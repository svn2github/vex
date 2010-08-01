
/*--------------------------------------------------------------------*/
/*--- begin                                       guest_arm_toIR.c ---*/
/*--------------------------------------------------------------------*/

/*
   This file is part of Valgrind, a dynamic binary instrumentation
   framework.

   Copyright (C) 2004-2010 OpenWorks LLP
      info@open-works.net

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
   02110-1301, USA.

   The GNU General Public License is contained in the file COPYING.
*/

/* XXXX thumb to check:
   that all cases where putIRegT writes r15, we generate a jump.

   All uses of newTemp assign to an IRTemp and not a UInt


   XXXX thumb to do: improve the ITSTATE-zeroing optimisation by
   taking into account the number of insns guarded by an IT.

   remove the nasty hack, in the spechelper, of looking for Or32(...,
   0xE0) in as the first arg to armg_calculate_condition, and instead
   use Slice44 as specified in comments in the spechelper.

   add specialisations for armg_calculate_flag_c and _v, as they
   are moderately often needed in Thumb code.
*/

/* Limitations, etc

   - pretty dodgy exception semantics for {LD,ST}Mxx, no doubt

   - SWP: the restart jump back is Ijk_Boring; it should be
     Ijk_NoRedir but that's expensive.  See comments on casLE() in
     guest_x86_toIR.c.

*/

/* "Special" instructions.

   This instruction decoder can decode four special instructions
   which mean nothing natively (are no-ops as far as regs/mem are
   concerned) but have meaning for supporting Valgrind.  A special
   instruction is flagged by a 16-byte preamble:

      E1A0C1EC E1A0C6EC E1A0CEEC E1A0C9EC
      (mov r12, r12, ROR #3;   mov r12, r12, ROR #13;
       mov r12, r12, ROR #29;  mov r12, r12, ROR #19)

   Following that, one of the following 3 are allowed
   (standard interpretation in parentheses):

      E18AA00A (orr r10,r10,r10)   R3 = client_request ( R4 )
      E18BB00B (orr r11,r11,r11)   R3 = guest_NRADDR
      E18CC00C (orr r12,r12,r12)   branch-and-link-to-noredir R4

   Any other bytes following the 16-byte preamble are illegal and
   constitute a failure in instruction decoding.  This all assumes
   that the preamble will never occur except in specific code
   fragments designed for Valgrind to catch.
*/

/* Translates ARM(v5) code to IR. */

#include "libvex_basictypes.h"
#include "libvex_ir.h"
#include "libvex.h"
#include "libvex_guest_arm.h"

#include "main_util.h"
#include "main_globals.h"
#include "guest_generic_bb_to_IR.h"
#include "guest_arm_defs.h"


/*------------------------------------------------------------*/
/*--- Globals                                              ---*/
/*------------------------------------------------------------*/

/* These are set at the start of the translation of a instruction, so
   that we don't have to pass them around endlessly.  CONST means does
   not change during translation of the instruction.
*/

/* CONST: is the host bigendian?  This has to do with float vs double
   register accesses on VFP, but it's complex and not properly thought
   out. */
static Bool host_is_bigendian;

/* CONST: The guest address for the instruction currently being
   translated.  This is the real, "decoded" address (not subject
   to the CPSR.T kludge). */
static Addr32 guest_R15_curr_instr_notENC;

/* MOD: The IRSB* into which we're generating code. */
static IRSB* irsb;

/* These are to do with handling writes to r15.  They are initially
   set at the start of disInstr_ARM_WRK to indicate no update,
   possibly updated during the routine, and examined again at the end.
   If they have been set to indicate a r15 update then a jump is
   generated.  Note, "explicit" jumps (b, bx, etc) are generated
   directly, not using this mechanism -- this is intended to handle
   the implicit-style jumps resulting from (eg) assigning to r15 as
   the result of insns we wouldn't normally consider branchy. */

/* MOD.  Initially False; set to True iff abovementioned handling is
   required. */
static Bool r15written;

/* MOD.  Initially IRTemp_INVALID.  If the r15 branch to be generated
   is conditional, this holds the gating IRTemp :: Ity_I32.  If the
   branch to be generated is unconditional, this remains
   IRTemp_INVALID. */
static IRTemp r15guard; /* :: Ity_I32, 0 or 1 */

/* MOD.  Initially Ijk_Boring.  If an r15 branch is to be generated,
   this holds the jump kind. */
static IRTemp r15kind;


/*------------------------------------------------------------*/
/*--- Debugging output                                     ---*/
/*------------------------------------------------------------*/

#define DIP(format, args...)           \
   if (vex_traceflags & VEX_TRACE_FE)  \
      vex_printf(format, ## args)

#define DIS(buf, format, args...)      \
   if (vex_traceflags & VEX_TRACE_FE)  \
      vex_sprintf(buf, format, ## args)


/*------------------------------------------------------------*/
/*--- Helper bits and pieces for deconstructing the        ---*/
/*--- arm insn stream.                                     ---*/
/*------------------------------------------------------------*/

/* Do a little-endian load of a 32-bit word, regardless of the
   endianness of the underlying host. */
static inline UInt getUIntLittleEndianly ( UChar* p )
{
   UInt w = 0;
   w = (w << 8) | p[3];
   w = (w << 8) | p[2];
   w = (w << 8) | p[1];
   w = (w << 8) | p[0];
   return w;
}

/* Do a little-endian load of a 16-bit word, regardless of the
   endianness of the underlying host. */
static inline UShort getUShortLittleEndianly ( UChar* p )
{
   UShort w = 0;
   w = (w << 8) | p[1];
   w = (w << 8) | p[0];
   return w;
}

static UInt ROR32 ( UInt x, UInt sh ) {
   vassert(sh >= 0 && sh < 32);
   if (sh == 0)
      return x;
   else
      return (x << (32-sh)) | (x >> sh);
}

static Int popcount32 ( UInt x )
{
   Int res = 0, i;
   for (i = 0; i < 32; i++) {
      res += (x & 1);
      x >>= 1;
   }
   return res;
}

static UInt setbit32 ( UInt x, Int ix, UInt b )
{
   UInt mask = 1 << ix;
   x &= ~mask;
   x |= ((b << ix) & mask);
   return x;
}

#define BITS2(_b1,_b0) \
   (((_b1) << 1) | (_b0))

#define BITS3(_b2,_b1,_b0)                      \
  (((_b2) << 2) | ((_b1) << 1) | (_b0))

#define BITS4(_b3,_b2,_b1,_b0) \
   (((_b3) << 3) | ((_b2) << 2) | ((_b1) << 1) | (_b0))

#define BITS8(_b7,_b6,_b5,_b4,_b3,_b2,_b1,_b0)  \
   ((BITS4((_b7),(_b6),(_b5),(_b4)) << 4) \
    | BITS4((_b3),(_b2),(_b1),(_b0)))

#define BITS5(_b4,_b3,_b2,_b1,_b0)  \
   (BITS8(0,0,0,(_b4),(_b3),(_b2),(_b1),(_b0)))
#define BITS6(_b5,_b4,_b3,_b2,_b1,_b0)  \
   (BITS8(0,0,(_b5),(_b4),(_b3),(_b2),(_b1),(_b0)))
#define BITS7(_b6,_b5,_b4,_b3,_b2,_b1,_b0)  \
   (BITS8(0,(_b6),(_b5),(_b4),(_b3),(_b2),(_b1),(_b0)))

#define BITS9(_b8,_b7,_b6,_b5,_b4,_b3,_b2,_b1,_b0)      \
   (((_b8) << 8) \
    | BITS8((_b7),(_b6),(_b5),(_b4),(_b3),(_b2),(_b1),(_b0)))

/* produces _uint[_bMax:_bMin] */
#define SLICE_UInt(_uint,_bMax,_bMin) \
   (( ((UInt)(_uint)) >> (_bMin)) \
      & ((1 << ((_bMax) - (_bMin) + 1)) - 1))


/*------------------------------------------------------------*/
/*--- Helper bits and pieces for creating IR fragments.    ---*/
/*------------------------------------------------------------*/

static IRExpr* mkU32 ( UInt i )
{
   return IRExpr_Const(IRConst_U32(i));
}

static IRExpr* mkU8 ( UInt i )
{
   vassert(i < 256);
   return IRExpr_Const(IRConst_U8( (UChar)i ));
}

static IRExpr* mkexpr ( IRTemp tmp )
{
   return IRExpr_RdTmp(tmp);
}

static IRExpr* unop ( IROp op, IRExpr* a )
{
   return IRExpr_Unop(op, a);
}

static IRExpr* binop ( IROp op, IRExpr* a1, IRExpr* a2 )
{
   return IRExpr_Binop(op, a1, a2);
}

static IRExpr* triop ( IROp op, IRExpr* a1, IRExpr* a2, IRExpr* a3 )
{
   return IRExpr_Triop(op, a1, a2, a3);
}

static IRExpr* loadLE ( IRType ty, IRExpr* addr )
{
   return IRExpr_Load(Iend_LE, ty, addr);
}

/* Add a statement to the list held by "irbb". */
static void stmt ( IRStmt* st )
{
   addStmtToIRSB( irsb, st );
}

static void assign ( IRTemp dst, IRExpr* e )
{
   stmt( IRStmt_WrTmp(dst, e) );
}

static void storeLE ( IRExpr* addr, IRExpr* data )
{
   stmt( IRStmt_Store(Iend_LE, addr, data) );
}

/* Generate a new temporary of the given type. */
static IRTemp newTemp ( IRType ty )
{
   vassert(isPlausibleIRType(ty));
   return newIRTemp( irsb->tyenv, ty );
}

/* Produces a value in 0 .. 3, which is encoded as per the type
   IRRoundingMode. */
static IRExpr* /* :: Ity_I32 */ get_FAKE_roundingmode ( void )
{
   return mkU32(Irrm_NEAREST);
}

/* Generate an expression for SRC rotated right by ROT. */
static IRExpr* genROR32( IRTemp src, Int rot )
{
   vassert(rot >= 0 && rot < 32);
   if (rot == 0)
      return mkexpr(src);
   return
      binop(Iop_Or32,
            binop(Iop_Shl32, mkexpr(src), mkU8(32 - rot)),
            binop(Iop_Shr32, mkexpr(src), mkU8(rot)));
}


/*------------------------------------------------------------*/
/*--- Helpers for accessing guest registers.               ---*/
/*------------------------------------------------------------*/

#define OFFB_R0       offsetof(VexGuestARMState,guest_R0)
#define OFFB_R1       offsetof(VexGuestARMState,guest_R1)
#define OFFB_R2       offsetof(VexGuestARMState,guest_R2)
#define OFFB_R3       offsetof(VexGuestARMState,guest_R3)
#define OFFB_R4       offsetof(VexGuestARMState,guest_R4)
#define OFFB_R5       offsetof(VexGuestARMState,guest_R5)
#define OFFB_R6       offsetof(VexGuestARMState,guest_R6)
#define OFFB_R7       offsetof(VexGuestARMState,guest_R7)
#define OFFB_R8       offsetof(VexGuestARMState,guest_R8)
#define OFFB_R9       offsetof(VexGuestARMState,guest_R9)
#define OFFB_R10      offsetof(VexGuestARMState,guest_R10)
#define OFFB_R11      offsetof(VexGuestARMState,guest_R11)
#define OFFB_R12      offsetof(VexGuestARMState,guest_R12)
#define OFFB_R13      offsetof(VexGuestARMState,guest_R13)
#define OFFB_R14      offsetof(VexGuestARMState,guest_R14)
#define OFFB_R15T     offsetof(VexGuestARMState,guest_R15T)

#define OFFB_CC_OP    offsetof(VexGuestARMState,guest_CC_OP)
#define OFFB_CC_DEP1  offsetof(VexGuestARMState,guest_CC_DEP1)
#define OFFB_CC_DEP2  offsetof(VexGuestARMState,guest_CC_DEP2)
#define OFFB_CC_NDEP  offsetof(VexGuestARMState,guest_CC_NDEP)
#define OFFB_NRADDR   offsetof(VexGuestARMState,guest_NRADDR)

#define OFFB_D0       offsetof(VexGuestARMState,guest_D0)
#define OFFB_D1       offsetof(VexGuestARMState,guest_D1)
#define OFFB_D2       offsetof(VexGuestARMState,guest_D2)
#define OFFB_D3       offsetof(VexGuestARMState,guest_D3)
#define OFFB_D4       offsetof(VexGuestARMState,guest_D4)
#define OFFB_D5       offsetof(VexGuestARMState,guest_D5)
#define OFFB_D6       offsetof(VexGuestARMState,guest_D6)
#define OFFB_D7       offsetof(VexGuestARMState,guest_D7)
#define OFFB_D8       offsetof(VexGuestARMState,guest_D8)
#define OFFB_D9       offsetof(VexGuestARMState,guest_D9)
#define OFFB_D10      offsetof(VexGuestARMState,guest_D10)
#define OFFB_D11      offsetof(VexGuestARMState,guest_D11)
#define OFFB_D12      offsetof(VexGuestARMState,guest_D12)
#define OFFB_D13      offsetof(VexGuestARMState,guest_D13)
#define OFFB_D14      offsetof(VexGuestARMState,guest_D14)
#define OFFB_D15      offsetof(VexGuestARMState,guest_D15)

#define OFFB_FPSCR    offsetof(VexGuestARMState,guest_FPSCR)
#define OFFB_TPIDRURO offsetof(VexGuestARMState,guest_TPIDRURO)
#define OFFB_ITSTATE  offsetof(VexGuestARMState,guest_ITSTATE)


/* ---------------- Integer registers ---------------- */

static Int integerGuestRegOffset ( UInt iregNo )
{
   /* Do we care about endianness here?  We do if sub-parts of integer
      registers are accessed, but I don't think that ever happens on
      ARM. */
   switch (iregNo) {
      case 0:  return OFFB_R0;
      case 1:  return OFFB_R1;
      case 2:  return OFFB_R2;
      case 3:  return OFFB_R3;
      case 4:  return OFFB_R4;
      case 5:  return OFFB_R5;
      case 6:  return OFFB_R6;
      case 7:  return OFFB_R7;
      case 8:  return OFFB_R8;
      case 9:  return OFFB_R9;
      case 10: return OFFB_R10;
      case 11: return OFFB_R11;
      case 12: return OFFB_R12;
      case 13: return OFFB_R13;
      case 14: return OFFB_R14;
      case 15: return OFFB_R15T;
      default: vassert(0);
   }
}

/* Plain ("low level") read from a reg; no +8 offset magic for r15. */
static IRExpr* llGetIReg ( UInt iregNo )
{
   vassert(iregNo < 16);
   return IRExpr_Get( integerGuestRegOffset(iregNo), Ity_I32 );
}

/* Architected read from a reg in ARM mode.  This automagically adds 8
   to all reads of r15. */
static IRExpr* getIRegA ( UInt iregNo )
{
   IRExpr* e;
   vassert(iregNo < 16);
   if (iregNo == 15) {
      /* If asked for r15, don't read the guest state value, as that
         may not be up to date in the case where loop unrolling has
         happened, because the first insn's write to the block is
         omitted; hence in the 2nd and subsequent unrollings we don't
         have a correct value in guest r15.  Instead produce the
         constant that we know would be produced at this point. */
      vassert(0 == (guest_R15_curr_instr_notENC & 3));
      e = mkU32(guest_R15_curr_instr_notENC + 8);
   } else {
      e = IRExpr_Get( integerGuestRegOffset(iregNo), Ity_I32 );
   }
   return e;
}

/* Architected read from a reg in Thumb mode.  This automagically adds
   4 to all reads of r15. */
static IRExpr* getIRegT ( UInt iregNo )
{
   IRExpr* e;
   vassert(iregNo < 16);
   if (iregNo == 15) {
      /* Ditto comment in getIReg. */
      vassert(0 == (guest_R15_curr_instr_notENC & 1));
      e = mkU32(guest_R15_curr_instr_notENC + 4);
   } else {
      e = IRExpr_Get( integerGuestRegOffset(iregNo), Ity_I32 );
   }
   return e;
}

/* Plain ("low level") write to a reg; no jump or alignment magic for
   r15. */
static void llPutIReg ( UInt iregNo, IRExpr* e )
{
   vassert(iregNo < 16);
   vassert(typeOfIRExpr(irsb->tyenv, e) == Ity_I32);
   stmt( IRStmt_Put(integerGuestRegOffset(iregNo), e) );
}

/* Architected write to an integer register in ARM mode.  If it is to
   r15, record info so at the end of this insn's translation, a branch
   to it can be made.  Also handles conditional writes to the
   register: if guardT == IRTemp_INVALID then the write is
   unconditional.  If writing r15, also 4-align it. */
static void putIRegA ( UInt       iregNo,
                       IRExpr*    e,
                       IRTemp     guardT /* :: Ity_I32, 0 or 1 */,
                       IRJumpKind jk /* if a jump is generated */ )
{
   /* if writing r15, force e to be 4-aligned. */
   // INTERWORKING FIXME.  this needs to be relaxed so that
   // puts caused by LDMxx which load r15 interwork right.
   // but is no aligned too relaxed?
   //if (iregNo == 15)
   //   e = binop(Iop_And32, e, mkU32(~3));
   /* So, generate either an unconditional or a conditional write to
      the reg. */
   if (guardT == IRTemp_INVALID) {
      /* unconditional write */
      llPutIReg( iregNo, e );
   } else {
      llPutIReg( iregNo,
                 IRExpr_Mux0X( unop(Iop_32to8, mkexpr(guardT)),
                               llGetIReg(iregNo),
                               e ));
   }
   if (iregNo == 15) {
      // assert against competing r15 updates.  Shouldn't
      // happen; should be ruled out by the instr matching
      // logic.
      vassert(r15written == False);
      vassert(r15guard   == IRTemp_INVALID);
      vassert(r15kind    == Ijk_Boring);
      r15written = True;
      r15guard   = guardT;
      r15kind    = jk;
   }
}


/* Architected write to an integer register in Thumb mode.  Writes to
   r15 are not allowed.  Handles conditional writes to the register:
   if guardT == IRTemp_INVALID then the write is unconditional. */
static void putIRegT ( UInt       iregNo,
                       IRExpr*    e,
                       IRTemp     guardT /* :: Ity_I32, 0 or 1 */ )
{
   /* So, generate either an unconditional or a conditional write to
      the reg. */
   vassert(iregNo >= 0 && iregNo <= 14);
   if (guardT == IRTemp_INVALID) {
      /* unconditional write */
      llPutIReg( iregNo, e );
   } else {
      llPutIReg( iregNo,
                 IRExpr_Mux0X( unop(Iop_32to8, mkexpr(guardT)),
                               llGetIReg(iregNo),
                               e ));
   }
}


/* Thumb16 and Thumb32 only.
   Returns true if reg is 13 or 15.  Implements the BadReg
   predicate in the ARM ARM. */
static Bool isBadRegT ( UInt r )
{
   vassert(r <= 15);
   return r == 13 || r == 15;
}


/* ---------------- Double registers ---------------- */

static Int doubleGuestRegOffset ( UInt dregNo )
{
   /* Do we care about endianness here?  Probably do if we ever get
      into the situation of dealing with the single-precision VFP
      registers. */
   switch (dregNo) {
      case 0:  return OFFB_D0;
      case 1:  return OFFB_D1;
      case 2:  return OFFB_D2;
      case 3:  return OFFB_D3;
      case 4:  return OFFB_D4;
      case 5:  return OFFB_D5;
      case 6:  return OFFB_D6;
      case 7:  return OFFB_D7;
      case 8:  return OFFB_D8;
      case 9:  return OFFB_D9;
      case 10: return OFFB_D10;
      case 11: return OFFB_D11;
      case 12: return OFFB_D12;
      case 13: return OFFB_D13;
      case 14: return OFFB_D14;
      case 15: return OFFB_D15;
      default: vassert(0);
   }
}

/* Plain ("low level") read from a VFP Dreg. */
static IRExpr* llGetDReg ( UInt dregNo )
{
   vassert(dregNo < 16);
   return IRExpr_Get( doubleGuestRegOffset(dregNo), Ity_F64 );
}

/* Architected read from a VFP Dreg. */
static IRExpr* getDReg ( UInt dregNo ) {
   return llGetDReg( dregNo );
}

/* Plain ("low level") write to a VFP Dreg. */
static void llPutDReg ( UInt dregNo, IRExpr* e )
{
   vassert(dregNo < 16);
   vassert(typeOfIRExpr(irsb->tyenv, e) == Ity_F64);
   stmt( IRStmt_Put(doubleGuestRegOffset(dregNo), e) );
}

/* Architected write to a VFP Dreg.  Handles conditional writes to the
   register: if guardT == IRTemp_INVALID then the write is
   unconditional. */
static void putDReg ( UInt    dregNo,
                      IRExpr* e,
                      IRTemp  guardT /* :: Ity_I32, 0 or 1 */)
{
   /* So, generate either an unconditional or a conditional write to
      the reg. */
   if (guardT == IRTemp_INVALID) {
      /* unconditional write */
      llPutDReg( dregNo, e );
   } else {
      llPutDReg( dregNo,
                 IRExpr_Mux0X( unop(Iop_32to8, mkexpr(guardT)),
                               llGetDReg(dregNo),
                               e ));
   }
}


/* ---------------- Float registers ---------------- */

static Int floatGuestRegOffset ( UInt fregNo )
{
   /* Start with the offset of the containing double, and the correct
      for endianness.  Actually this is completely bogus and needs
      careful thought. */
   Int off;
   vassert(fregNo < 32);
   off = doubleGuestRegOffset(fregNo >> 1);
   if (host_is_bigendian) {
      vassert(0);
   } else {
      if (fregNo & 1)
         off += 4;
   }
   return off;
}

/* Plain ("low level") read from a VFP Freg. */
static IRExpr* llGetFReg ( UInt fregNo )
{
   vassert(fregNo < 32);
   return IRExpr_Get( floatGuestRegOffset(fregNo), Ity_F32 );
}

/* Architected read from a VFP Freg. */
static IRExpr* getFReg ( UInt fregNo ) {
   return llGetFReg( fregNo );
}

/* Plain ("low level") write to a VFP Freg. */
static void llPutFReg ( UInt fregNo, IRExpr* e )
{
   vassert(fregNo < 32);
   vassert(typeOfIRExpr(irsb->tyenv, e) == Ity_F32);
   stmt( IRStmt_Put(floatGuestRegOffset(fregNo), e) );
}

/* Architected write to a VFP Freg.  Handles conditional writes to the
   register: if guardT == IRTemp_INVALID then the write is
   unconditional. */
static void putFReg ( UInt    fregNo,
                      IRExpr* e,
                      IRTemp  guardT /* :: Ity_I32, 0 or 1 */)
{
   /* So, generate either an unconditional or a conditional write to
      the reg. */
   if (guardT == IRTemp_INVALID) {
      /* unconditional write */
      llPutFReg( fregNo, e );
   } else {
      llPutFReg( fregNo,
                 IRExpr_Mux0X( unop(Iop_32to8, mkexpr(guardT)),
                               llGetFReg(fregNo),
                               e ));
   }
}


/* ---------------- Misc registers ---------------- */

static void putMiscReg32 ( UInt    gsoffset, 
                           IRExpr* e, /* :: Ity_I32 */
                           IRTemp  guardT /* :: Ity_I32, 0 or 1 */)
{
   switch (gsoffset) {
      case OFFB_FPSCR: break;
      default: vassert(0); /* awaiting more cases */
   }
   vassert(typeOfIRExpr(irsb->tyenv, e) == Ity_I32);

   if (guardT == IRTemp_INVALID) {
      /* unconditional write */
      stmt(IRStmt_Put(gsoffset, e));
   } else {
      vassert(0); //ATC
      stmt(IRStmt_Put( gsoffset,
                       IRExpr_Mux0X( unop(Iop_32to8, mkexpr(guardT)),
                                     IRExpr_Get(gsoffset, Ity_I32),
                                     e) ));

   }
}

static IRTemp get_ITSTATE ( void )
{
   IRTemp t = newTemp(Ity_I32);
   assign(t, IRExpr_Get( OFFB_ITSTATE, Ity_I32));
   return t;
}

static void put_ITSTATE ( IRTemp t )
{
   stmt( IRStmt_Put( OFFB_ITSTATE, mkexpr(t)) );
}


/* ---------------- FPSCR stuff ---------------- */

/* Generate IR to get hold of the rounding mode bits in FPSCR, and
   convert them to IR format.  Bind the final result to the
   returned temp. */
static IRTemp /* :: Ity_I32 */ mk_get_IR_rounding_mode ( void )
{
   /* The ARMvfp encoding for rounding mode bits is:
         00  to nearest
         01  to +infinity
         10  to -infinity
         11  to zero
      We need to convert that to the IR encoding:
         00  to nearest (the default)
         10  to +infinity
         01  to -infinity
         11  to zero
      Which can be done by swapping bits 0 and 1.
      The rmode bits are at 23:22 in FPSCR.
   */
   IRTemp armEncd = newTemp(Ity_I32);
   IRTemp swapped = newTemp(Ity_I32);
   /* Fish FPSCR[23:22] out, and slide to bottom.  Doesn't matter that
      we don't zero out bits 24 and above, since the assignment to
      'swapped' will mask them out anyway. */
   assign(armEncd,
          binop(Iop_Shr32, IRExpr_Get(OFFB_FPSCR, Ity_I32), mkU8(22)));
   /* Now swap them. */
   assign(swapped,
          binop(Iop_Or32,
                binop(Iop_And32,
                      binop(Iop_Shl32, mkexpr(armEncd), mkU8(1)),
                      mkU32(2)),
                binop(Iop_And32,
                      binop(Iop_Shr32, mkexpr(armEncd), mkU8(1)),
                      mkU32(1))
         ));
   return swapped;
}


/*------------------------------------------------------------*/
/*--- Helpers for flag handling and conditional insns      ---*/
/*------------------------------------------------------------*/

static HChar* name_ARMCondcode ( ARMCondcode cond )
{
   switch (cond) {
      case ARMCondEQ:  return "{eq}";
      case ARMCondNE:  return "{ne}";
      case ARMCondHS:  return "{hs}";  // or 'cs'
      case ARMCondLO:  return "{lo}";  // or 'cc'
      case ARMCondMI:  return "{mi}";
      case ARMCondPL:  return "{pl}";
      case ARMCondVS:  return "{vs}";
      case ARMCondVC:  return "{vc}";
      case ARMCondHI:  return "{hi}";
      case ARMCondLS:  return "{ls}";
      case ARMCondGE:  return "{ge}";
      case ARMCondLT:  return "{lt}";
      case ARMCondGT:  return "{gt}";
      case ARMCondLE:  return "{le}";
      case ARMCondAL:  return ""; // {al}: is the default
      case ARMCondNV:  return "{nv}";
      default: vpanic("name_ARMCondcode");
   }
}
/* and a handy shorthand for it */
static HChar* nCC ( ARMCondcode cond ) {
   return name_ARMCondcode(cond);
}


/* Build IR to calculate some particular condition from stored
   CC_OP/CC_DEP1/CC_DEP2/CC_NDEP.  Returns an expression of type
   Ity_I32, suitable for narrowing.  Although the return type is
   Ity_I32, the returned value is either 0 or 1.  'cond' must be
   :: Ity_I32 and must denote the condition to compute in 
   bits 7:4, and be zero everywhere else.
*/
static IRExpr* mk_armg_calculate_condition_dyn ( IRExpr* cond )
{
   vassert(typeOfIRExpr(irsb->tyenv, cond) == Ity_I32);
   /* And 'cond' had better produce a value in which only bits 7:4
      bits are nonzero.  However, obviously we can't assert for
      that. */

   /* So what we're constructing for the first argument is 
      "(cond << 4) | stored-operation-operation".  However,
      as per comments above, must be supplied pre-shifted to this
      function.

      This pairing scheme requires that the ARM_CC_OP_ values all fit
      in 4 bits.  Hence we are passing a (COND, OP) pair in the lowest
      8 bits of the first argument. */
   IRExpr** args
      = mkIRExprVec_4(
           binop(Iop_Or32, IRExpr_Get(OFFB_CC_OP, Ity_I32), cond),
           IRExpr_Get(OFFB_CC_DEP1, Ity_I32),
           IRExpr_Get(OFFB_CC_DEP2, Ity_I32),
           IRExpr_Get(OFFB_CC_NDEP, Ity_I32)
        );
   IRExpr* call
      = mkIRExprCCall(
           Ity_I32,
           0/*regparm*/, 
           "armg_calculate_condition", &armg_calculate_condition,
           args
        );

   /* Exclude the requested condition, OP and NDEP from definedness
      checking.  We're only interested in DEP1 and DEP2. */
   call->Iex.CCall.cee->mcx_mask = (1<<0) | (1<<3);
   return call;
}


/* Build IR to calculate some particular condition from stored
   CC_OP/CC_DEP1/CC_DEP2/CC_NDEP.  Returns an expression of type
   Ity_I32, suitable for narrowing.  Although the return type is
   Ity_I32, the returned value is either 0 or 1.
*/
static IRExpr* mk_armg_calculate_condition ( ARMCondcode cond )
{
  /* First arg is "(cond << 4) | condition".  This requires that the
     ARM_CC_OP_ values all fit in 4 bits.  Hence we are passing a
     (COND, OP) pair in the lowest 8 bits of the first argument. */
   vassert(cond >= 0 && cond <= 15);
   return mk_armg_calculate_condition_dyn( mkU32(cond << 4) );
}


/* Build IR to calculate just the carry flag from stored
   CC_OP/CC_DEP1/CC_DEP2/CC_NDEP.  Returns an expression ::
   Ity_I32. */
static IRExpr* mk_armg_calculate_flag_c ( void )
{
   IRExpr** args
      = mkIRExprVec_4( IRExpr_Get(OFFB_CC_OP,   Ity_I32),
                       IRExpr_Get(OFFB_CC_DEP1, Ity_I32),
                       IRExpr_Get(OFFB_CC_DEP2, Ity_I32),
                       IRExpr_Get(OFFB_CC_NDEP, Ity_I32) );
   IRExpr* call
      = mkIRExprCCall(
           Ity_I32,
           0/*regparm*/, 
           "armg_calculate_flag_c", &armg_calculate_flag_c,
           args
        );
   /* Exclude OP and NDEP from definedness checking.  We're only
      interested in DEP1 and DEP2. */
   call->Iex.CCall.cee->mcx_mask = (1<<0) | (1<<3);
   return call;
}


/* Build IR to calculate just the overflow flag from stored
   CC_OP/CC_DEP1/CC_DEP2/CC_NDEP.  Returns an expression ::
   Ity_I32. */
static IRExpr* mk_armg_calculate_flag_v ( void )
{
   IRExpr** args
      = mkIRExprVec_4( IRExpr_Get(OFFB_CC_OP,   Ity_I32),
                       IRExpr_Get(OFFB_CC_DEP1, Ity_I32),
                       IRExpr_Get(OFFB_CC_DEP2, Ity_I32),
                       IRExpr_Get(OFFB_CC_NDEP, Ity_I32) );
   IRExpr* call
      = mkIRExprCCall(
           Ity_I32,
           0/*regparm*/, 
           "armg_calculate_flag_v", &armg_calculate_flag_v,
           args
        );
   /* Exclude OP and NDEP from definedness checking.  We're only
      interested in DEP1 and DEP2. */
   call->Iex.CCall.cee->mcx_mask = (1<<0) | (1<<3);
   return call;
}


/* Build IR to calculate N Z C V in bits 31:28 of the
   returned word. */
static IRExpr* mk_armg_calculate_flags_nzcv ( void )
{
   IRExpr** args
      = mkIRExprVec_4( IRExpr_Get(OFFB_CC_OP,   Ity_I32),
                       IRExpr_Get(OFFB_CC_DEP1, Ity_I32),
                       IRExpr_Get(OFFB_CC_DEP2, Ity_I32),
                       IRExpr_Get(OFFB_CC_NDEP, Ity_I32) );
   IRExpr* call
      = mkIRExprCCall(
           Ity_I32,
           0/*regparm*/, 
           "armg_calculate_flags_nzcv", &armg_calculate_flags_nzcv,
           args
        );
   /* Exclude OP and NDEP from definedness checking.  We're only
      interested in DEP1 and DEP2. */
   call->Iex.CCall.cee->mcx_mask = (1<<0) | (1<<3);
   return call;
}


/* Build IR to conditionally set the flags thunk.  As with putIReg, if
   guard is IRTemp_INVALID then it's unconditional, else it holds a
   condition :: Ity_I32. */
static
void setFlags_D1_D2_ND ( UInt cc_op, IRTemp t_dep1,
                         IRTemp t_dep2, IRTemp t_ndep,
                         IRTemp guardT /* :: Ity_I32, 0 or 1 */ )
{
   IRTemp c8;
   vassert(typeOfIRTemp(irsb->tyenv, t_dep1 == Ity_I32));
   vassert(typeOfIRTemp(irsb->tyenv, t_dep2 == Ity_I32));
   vassert(typeOfIRTemp(irsb->tyenv, t_ndep == Ity_I32));
   vassert(cc_op >= ARMG_CC_OP_COPY && cc_op < ARMG_CC_OP_NUMBER);
   if (guardT == IRTemp_INVALID) {
      /* unconditional */
      stmt( IRStmt_Put( OFFB_CC_OP,   mkU32(cc_op) ));
      stmt( IRStmt_Put( OFFB_CC_DEP1, mkexpr(t_dep1) ));
      stmt( IRStmt_Put( OFFB_CC_DEP2, mkexpr(t_dep2) ));
      stmt( IRStmt_Put( OFFB_CC_NDEP, mkexpr(t_ndep) ));
   } else {
      /* conditional */
      c8 = newTemp(Ity_I8);
      assign( c8, unop(Iop_32to8, mkexpr(guardT)) );
      stmt( IRStmt_Put(
               OFFB_CC_OP,
               IRExpr_Mux0X( mkexpr(c8),
                             IRExpr_Get(OFFB_CC_OP, Ity_I32),
                             mkU32(cc_op) )));
      stmt( IRStmt_Put(
               OFFB_CC_DEP1,
               IRExpr_Mux0X( mkexpr(c8),
                             IRExpr_Get(OFFB_CC_DEP1, Ity_I32),
                             mkexpr(t_dep1) )));
      stmt( IRStmt_Put(
               OFFB_CC_DEP2,
               IRExpr_Mux0X( mkexpr(c8),
                             IRExpr_Get(OFFB_CC_DEP2, Ity_I32),
                             mkexpr(t_dep2) )));
      stmt( IRStmt_Put(
               OFFB_CC_NDEP,
               IRExpr_Mux0X( mkexpr(c8),
                             IRExpr_Get(OFFB_CC_NDEP, Ity_I32),
                             mkexpr(t_ndep) )));
   }
}


/* Minor variant of the above that sets NDEP to zero (if it
   sets it at all) */
static void setFlags_D1_D2 ( UInt cc_op, IRTemp t_dep1,
                             IRTemp t_dep2,
                             IRTemp guardT /* :: Ity_I32, 0 or 1 */ )
{
   IRTemp z32 = newTemp(Ity_I32);
   assign( z32, mkU32(0) );
   setFlags_D1_D2_ND( cc_op, t_dep1, t_dep2, z32, guardT );
}


/* Minor variant of the above that sets DEP2 to zero (if it
   sets it at all) */
static void setFlags_D1_ND ( UInt cc_op, IRTemp t_dep1,
                             IRTemp t_ndep,
                             IRTemp guardT /* :: Ity_I32, 0 or 1 */ )
{
   IRTemp z32 = newTemp(Ity_I32);
   assign( z32, mkU32(0) );
   setFlags_D1_D2_ND( cc_op, t_dep1, z32, t_ndep, guardT );
}


/* Minor variant of the above that sets DEP2 and NDEP to zero (if it
   sets them at all) */
static void setFlags_D1 ( UInt cc_op, IRTemp t_dep1,
                          IRTemp guardT /* :: Ity_I32, 0 or 1 */ )
{
   IRTemp z32 = newTemp(Ity_I32);
   assign( z32, mkU32(0) );
   setFlags_D1_D2_ND( cc_op, t_dep1, z32, z32, guardT );
}


/* ARM only */
/* Generate a side-exit to the next instruction, if the given guard
   expression :: Ity_I32 is 0 (note!  the side exit is taken if the
   condition is false!)  This is used to skip over conditional
   instructions which we can't generate straight-line code for, either
   because they are too complex or (more likely) they potentially
   generate exceptions.
*/
static void mk_skip_over_A32_if_cond_is_false ( 
               IRTemp guardT /* :: Ity_I32, 0 or 1 */
            )
{
   vassert(guardT != IRTemp_INVALID);
   vassert(0 == (guest_R15_curr_instr_notENC & 3));
   stmt( IRStmt_Exit(
            unop(Iop_Not1, unop(Iop_32to1, mkexpr(guardT))),
            Ijk_Boring,
            IRConst_U32(toUInt(guest_R15_curr_instr_notENC + 4))
       ));
}

/* Thumb16 only */
/* ditto, but jump over a 16-bit thumb insn */
static void mk_skip_over_T16_if_cond_is_false ( 
               IRTemp guardT /* :: Ity_I32, 0 or 1 */
            )
{
   vassert(guardT != IRTemp_INVALID);
   vassert(0 == (guest_R15_curr_instr_notENC & 1));
   stmt( IRStmt_Exit(
            unop(Iop_Not1, unop(Iop_32to1, mkexpr(guardT))),
            Ijk_Boring,
            IRConst_U32(toUInt((guest_R15_curr_instr_notENC + 2) | 1))
       ));
}


/* Thumb32 only */
/* ditto, but jump over a 32-bit thumb insn */
static void mk_skip_over_T32_if_cond_is_false ( 
               IRTemp guardT /* :: Ity_I32, 0 or 1 */
            )
{
   vassert(guardT != IRTemp_INVALID);
   vassert(0 == (guest_R15_curr_instr_notENC & 1));
   stmt( IRStmt_Exit(
            unop(Iop_Not1, unop(Iop_32to1, mkexpr(guardT))),
            Ijk_Boring,
            IRConst_U32(toUInt((guest_R15_curr_instr_notENC + 4) | 1))
       ));
}


/* Thumb16 and Thumb32 only
   Generate a SIGILL followed by a restart of the current instruction
   if the given temp is nonzero. */
static void gen_SIGILL_T_if_nonzero ( IRTemp t /* :: Ity_I32 */ )
{
   vassert(t != IRTemp_INVALID);
   vassert(0 == (guest_R15_curr_instr_notENC & 1));
   stmt(
      IRStmt_Exit(
         binop(Iop_CmpNE32, mkexpr(t), mkU32(0)),
         Ijk_NoDecode,
         IRConst_U32(toUInt(guest_R15_curr_instr_notENC | 1))
      )
   );
}


/* Inspect the old_itstate, and generate a SIGILL if it indicates that
   we are currently in an IT block and are not the last in the block.
   This also rolls back guest_ITSTATE to its old value before the exit
   and restores it to its new value afterwards.  This is so that if
   the exit is taken, we have an up to date version of ITSTATE
   available.  Without doing that, we have no hope of making precise
   exceptions work. */
static void gen_SIGILL_T_if_in_but_NLI_ITBlock (
               IRTemp old_itstate /* :: Ity_I32 */,
               IRTemp new_itstate /* :: Ity_I32 */
            )
{
   put_ITSTATE(old_itstate); // backout
   IRTemp guards_for_next3 = newTemp(Ity_I32);
   assign(guards_for_next3,
          binop(Iop_Shr32, mkexpr(old_itstate), mkU8(8)));
   gen_SIGILL_T_if_nonzero(guards_for_next3);
   put_ITSTATE(new_itstate); //restore
}


/* Simpler version of the above, which generates a SIGILL if
   we're anywhere within an IT block. */
static void gen_SIGILL_T_if_in_ITBlock (
               IRTemp old_itstate /* :: Ity_I32 */,
               IRTemp new_itstate /* :: Ity_I32 */
            )
{
   put_ITSTATE(old_itstate); // backout
   gen_SIGILL_T_if_nonzero(old_itstate);
   put_ITSTATE(new_itstate); //restore
}



/*------------------------------------------------------------*/
/*--- Larger helpers                                       ---*/
/*------------------------------------------------------------*/

/* Compute both the result and new C flag value for a LSL by an imm5
   or by a register operand.  May generate reads of the old C value
   (hence only safe to use before any writes to guest state happen).
   Are factored out so can be used by both ARM and Thumb.

   Note that in compute_result_and_C_after_{LSL,LSR,ASR}_by{imm5,reg},
   "res" (the result)  is a.k.a. "shop", shifter operand
   "newC" (the new C)  is a.k.a. "shco", shifter carry out

   The calling convention for res and newC is a bit funny.  They could
   be passed by value, but instead are passed by ref.
*/

static void compute_result_and_C_after_LSL_by_imm5 (
               /*OUT*/HChar* buf,
               IRTemp* res,
               IRTemp* newC,
               IRTemp rMt, UInt shift_amt, /* operands */
               UInt rM      /* only for debug printing */
            )
{
   if (shift_amt == 0) {
      if (newC) {
         assign( *newC, mk_armg_calculate_flag_c() );
      }
      assign( *res, mkexpr(rMt) );
      DIS(buf, "r%u", rM);
   } else {
      vassert(shift_amt >= 1 && shift_amt <= 31);
      if (newC) {
         assign( *newC,
                 binop(Iop_And32,
                       binop(Iop_Shr32, mkexpr(rMt), 
                                        mkU8(32 - shift_amt)),
                       mkU32(1)));
      }
      assign( *res,
              binop(Iop_Shl32, mkexpr(rMt), mkU8(shift_amt)) );
      DIS(buf, "r%u, LSL #%u", rM, shift_amt);
   }
}


static void compute_result_and_C_after_LSL_by_reg (
               /*OUT*/HChar* buf,
               IRTemp* res,
               IRTemp* newC,
               IRTemp rMt, IRTemp rSt,  /* operands */
               UInt rM,    UInt rS      /* only for debug printing */
            )
{
   // shift left in range 0 .. 255
   // amt  = rS & 255
   // res  = amt < 32 ?  Rm << amt  : 0
   // newC = amt == 0     ? oldC  :
   //        amt in 1..32 ?  Rm[32-amt]  : 0
   IRTemp amtT = newTemp(Ity_I32);
   assign( amtT, binop(Iop_And32, mkexpr(rSt), mkU32(255)) );
   if (newC) {
      /* mux0X(amt == 0,
               mux0X(amt < 32, 
                     0,
                     Rm[(32-amt) & 31])
               oldC)
      */
      /* About the best you can do is pray that iropt is able
         to nuke most or all of the following junk. */
      IRTemp oldC = newTemp(Ity_I32);
      assign(oldC, mk_armg_calculate_flag_c() );
      assign(
         *newC,
         IRExpr_Mux0X(
            unop(Iop_1Uto8,
                 binop(Iop_CmpEQ32, mkexpr(amtT), mkU32(0))),
            IRExpr_Mux0X(
               unop(Iop_1Uto8,
                    binop(Iop_CmpLE32U, mkexpr(amtT), mkU32(32))),
               mkU32(0),
               binop(Iop_Shr32,
                     mkexpr(rMt),
                     unop(Iop_32to8,
                          binop(Iop_And32,
                                binop(Iop_Sub32,
                                      mkU32(32),
                                      mkexpr(amtT)),
                                mkU32(31)
                          )
                     )
               )
            ),
            mkexpr(oldC)
         )
      );
   }
   // (Rm << (Rs & 31))  &  (((Rs & 255) - 32) >>s 31)
   // Lhs of the & limits the shift to 31 bits, so as to
   // give known IR semantics.  Rhs of the & is all 1s for
   // Rs <= 31 and all 0s for Rs >= 32.
   assign(
      *res,
      binop(
         Iop_And32,
         binop(Iop_Shl32,
               mkexpr(rMt),
               unop(Iop_32to8,
                    binop(Iop_And32, mkexpr(rSt), mkU32(31)))),
         binop(Iop_Sar32,
               binop(Iop_Sub32,
                     mkexpr(amtT),
                     mkU32(32)),
               mkU8(31))));
    DIS(buf, "r%u, LSL r%u", rM, rS);
}


static void compute_result_and_C_after_LSR_by_imm5 (
               /*OUT*/HChar* buf,
               IRTemp* res,
               IRTemp* newC,
               IRTemp rMt, UInt shift_amt, /* operands */
               UInt rM      /* only for debug printing */
            )
{
   if (shift_amt == 0) {
      // conceptually a 32-bit shift, however:
      // res  = 0
      // newC = Rm[31]
      if (newC) {
         assign( *newC,
                 binop(Iop_And32,
                       binop(Iop_Shr32, mkexpr(rMt), mkU8(31)), 
                       mkU32(1)));
      }
      assign( *res, mkU32(0) );
      DIS(buf, "r%u, LSR #0(a.k.a. 32)", rM);
   } else {
      // shift in range 1..31
      // res  = Rm >>u shift_amt
      // newC = Rm[shift_amt - 1]
      vassert(shift_amt >= 1 && shift_amt <= 31);
      if (newC) {
         assign( *newC,
                 binop(Iop_And32,
                       binop(Iop_Shr32, mkexpr(rMt), 
                                        mkU8(shift_amt - 1)),
                       mkU32(1)));
      }
      assign( *res,
              binop(Iop_Shr32, mkexpr(rMt), mkU8(shift_amt)) );
      DIS(buf, "r%u, LSR #%u", rM, shift_amt);
   }
}


static void compute_result_and_C_after_LSR_by_reg (
               /*OUT*/HChar* buf,
               IRTemp* res,
               IRTemp* newC,
               IRTemp rMt, IRTemp rSt,  /* operands */
               UInt rM,    UInt rS      /* only for debug printing */
            )
{
   // shift right in range 0 .. 255
   // amt = rS & 255
   // res  = amt < 32 ?  Rm >>u amt  : 0
   // newC = amt == 0     ? oldC  :
   //        amt in 1..32 ?  Rm[amt-1]  : 0
   IRTemp amtT = newTemp(Ity_I32);
   assign( amtT, binop(Iop_And32, mkexpr(rSt), mkU32(255)) );
   if (newC) {
      /* mux0X(amt == 0,
               mux0X(amt < 32, 
                     0,
                     Rm[(amt-1) & 31])
               oldC)
      */
      IRTemp oldC = newTemp(Ity_I32);
      assign(oldC, mk_armg_calculate_flag_c() );
      assign(
         *newC,
         IRExpr_Mux0X(
            unop(Iop_1Uto8,
                 binop(Iop_CmpEQ32, mkexpr(amtT), mkU32(0))),
            IRExpr_Mux0X(
               unop(Iop_1Uto8,
                    binop(Iop_CmpLE32U, mkexpr(amtT), mkU32(32))),
               mkU32(0),
               binop(Iop_Shr32,
                     mkexpr(rMt),
                     unop(Iop_32to8,
                          binop(Iop_And32,
                                binop(Iop_Sub32,
                                      mkexpr(amtT),
                                      mkU32(1)),
                                mkU32(31)
                          )
                     )
               )
            ),
            mkexpr(oldC)
         )
      );
   }
   // (Rm >>u (Rs & 31))  &  (((Rs & 255) - 32) >>s 31)
   // Lhs of the & limits the shift to 31 bits, so as to
   // give known IR semantics.  Rhs of the & is all 1s for
   // Rs <= 31 and all 0s for Rs >= 32.
   assign(
      *res,
      binop(
         Iop_And32,
         binop(Iop_Shr32,
               mkexpr(rMt),
               unop(Iop_32to8,
                    binop(Iop_And32, mkexpr(rSt), mkU32(31)))),
         binop(Iop_Sar32,
               binop(Iop_Sub32,
                     mkexpr(amtT),
                     mkU32(32)),
               mkU8(31))));
    DIS(buf, "r%u, LSR r%u", rM, rS);
}


static void compute_result_and_C_after_ASR_by_imm5 (
               /*OUT*/HChar* buf,
               IRTemp* res,
               IRTemp* newC,
               IRTemp rMt, UInt shift_amt, /* operands */
               UInt rM      /* only for debug printing */
            )
{
   if (shift_amt == 0) {
      // conceptually a 32-bit shift, however:
      // res  = Rm >>s 31
      // newC = Rm[31]
      if (newC) {
         assign( *newC,
                 binop(Iop_And32,
                       binop(Iop_Shr32, mkexpr(rMt), mkU8(31)), 
                       mkU32(1)));
      }
      assign( *res, binop(Iop_Sar32, mkexpr(rMt), mkU8(31)) );
      DIS(buf, "r%u, ASR #0(a.k.a. 32)", rM);
   } else {
      // shift in range 1..31
      // res = Rm >>s shift_amt
      // newC = Rm[shift_amt - 1]
      vassert(shift_amt >= 1 && shift_amt <= 31);
      if (newC) {
         assign( *newC,
                 binop(Iop_And32,
                       binop(Iop_Shr32, mkexpr(rMt), 
                                        mkU8(shift_amt - 1)),
                       mkU32(1)));
      }
      assign( *res,
              binop(Iop_Sar32, mkexpr(rMt), mkU8(shift_amt)) );
      DIS(buf, "r%u, ASR #%u", rM, shift_amt);
   }
}


static void compute_result_and_C_after_ASR_by_reg (
               /*OUT*/HChar* buf,
               IRTemp* res,
               IRTemp* newC,
               IRTemp rMt, IRTemp rSt,  /* operands */
               UInt rM,    UInt rS      /* only for debug printing */
            )
{
   // arithmetic shift right in range 0 .. 255
   // amt = rS & 255
   // res  = amt < 32 ?  Rm >>s amt  : Rm >>s 31
   // newC = amt == 0     ? oldC  :
   //        amt in 1..32 ?  Rm[amt-1]  : Rm[31]
   IRTemp amtT = newTemp(Ity_I32);
   assign( amtT, binop(Iop_And32, mkexpr(rSt), mkU32(255)) );
   if (newC) {
      /* mux0X(amt == 0,
               mux0X(amt < 32, 
                     Rm[31],
                     Rm[(amt-1) & 31])
               oldC)
      */
      IRTemp oldC = newTemp(Ity_I32);
      assign(oldC, mk_armg_calculate_flag_c() );
      assign(
         *newC,
         IRExpr_Mux0X(
            unop(Iop_1Uto8,
                 binop(Iop_CmpEQ32, mkexpr(amtT), mkU32(0))),
            IRExpr_Mux0X(
               unop(Iop_1Uto8,
                    binop(Iop_CmpLE32U, mkexpr(amtT), mkU32(32))),
               binop(Iop_Shr32,
                     mkexpr(rMt),
                     mkU8(31)
               ),
               binop(Iop_Shr32,
                     mkexpr(rMt),
                     unop(Iop_32to8,
                          binop(Iop_And32,
                                binop(Iop_Sub32,
                                      mkexpr(amtT),
                                      mkU32(1)),
                                mkU32(31)
                          )
                     )
               )
            ),
            mkexpr(oldC)
         )
      );
   }
   // (Rm >>s (amt <u 32 ? amt : 31))
   assign(
      *res,
      binop(
         Iop_Sar32,
         mkexpr(rMt),
         unop(
            Iop_32to8,
            IRExpr_Mux0X(
               unop(
                 Iop_1Uto8,
                 binop(Iop_CmpLT32U, mkexpr(amtT), mkU32(32))),
               mkU32(31),
               mkexpr(amtT)))));
    DIS(buf, "r%u, ASR r%u", rM, rS);
}


static void compute_result_and_C_after_ROR_by_reg (
               /*OUT*/HChar* buf,
               IRTemp* res,
               IRTemp* newC,
               IRTemp rMt, IRTemp rSt,  /* operands */
               UInt rM,    UInt rS      /* only for debug printing */
            )
{
   // rotate right in range 0 .. 255
   // amt = rS & 255
   // shop =  Rm `ror` (amt & 31)
   // shco =  amt == 0 ? oldC : Rm[(amt-1) & 31]
   IRTemp amtT = newTemp(Ity_I32);
   assign( amtT, binop(Iop_And32, mkexpr(rSt), mkU32(255)) );
   IRTemp amt5T = newTemp(Ity_I32);
   assign( amt5T, binop(Iop_And32, mkexpr(rSt), mkU32(31)) );
   IRTemp oldC = newTemp(Ity_I32);
   assign(oldC, mk_armg_calculate_flag_c() );
   if (newC) {
      assign(
         *newC,
         IRExpr_Mux0X(
            unop(Iop_32to8, mkexpr(amtT)),
            mkexpr(oldC),
            binop(Iop_And32,
                  binop(Iop_Shr32,
                        mkexpr(rMt), 
                        unop(Iop_32to8,
                             binop(Iop_And32,
                                   binop(Iop_Sub32,
                                         mkexpr(amtT), 
                                         mkU32(1)
                                   ),
                                   mkU32(31)
                             )
                        )
                  ),
                  mkU32(1)
            )
         )
      );
   }
   assign(
      *res,
      IRExpr_Mux0X(
         unop(Iop_32to8, mkexpr(amt5T)), mkexpr(rMt),
         binop(Iop_Or32,
               binop(Iop_Shr32,
                     mkexpr(rMt), 
                     unop(Iop_32to8, mkexpr(amt5T))
               ),
               binop(Iop_Shl32,
                     mkexpr(rMt),
                     unop(Iop_32to8,
                          binop(Iop_Sub32, mkU32(32), mkexpr(amt5T))
                     )
               )
         )
      )
   );
   DIS(buf, "r%u, ROR r#%u", rM, rS);
}


/* Generate an expression corresponding to the immediate-shift case of
   a shifter operand.  This is used both for ARM and Thumb2.

   Bind it to a temporary, and return that via *res.  If newC is
   non-NULL, also compute a value for the shifter's carry out (in the
   LSB of a word), bind it to a temporary, and return that via *shco.

   Generates GETs from the guest state and is therefore not safe to
   use once we start doing PUTs to it, for any given instruction.

   'how' is encoded thusly:
      00b LSL,  01b LSR,  10b ASR,  11b ROR
   Most but not all ARM and Thumb integer insns use this encoding.
   Be careful to ensure the right value is passed here.
*/
static void compute_result_and_C_after_shift_by_imm5 (
               /*OUT*/HChar* buf,
               /*OUT*/IRTemp* res,
               /*OUT*/IRTemp* newC,
               IRTemp  rMt,       /* reg to shift */
               UInt    how,       /* what kind of shift */
               UInt    shift_amt, /* shift amount (0..31) */
               UInt    rM         /* only for debug printing */
            )
{
   vassert(shift_amt < 32);
   vassert(how < 4);

   switch (how) {

      case 0:
         compute_result_and_C_after_LSL_by_imm5(
            buf, res, newC, rMt, shift_amt, rM
         );
         break;

      case 1:
         compute_result_and_C_after_LSR_by_imm5(
            buf, res, newC, rMt, shift_amt, rM
         );
         break;

      case 2:
         compute_result_and_C_after_ASR_by_imm5(
            buf, res, newC, rMt, shift_amt, rM
         );
         break;

      case 3:
         if (shift_amt == 0) {
            IRTemp oldcT = newTemp(Ity_I32);
            // rotate right 1 bit through carry (?)
            // RRX -- described at ARM ARM A5-17
            // res  = (oldC << 31) | (Rm >>u 1)
            // newC = Rm[0]
            if (newC) {
               assign( *newC,
                       binop(Iop_And32, mkexpr(rMt), mkU32(1)));
            }
            assign( oldcT, mk_armg_calculate_flag_c() );
            assign( *res, 
                    binop(Iop_Or32,
                          binop(Iop_Shl32, mkexpr(oldcT), mkU8(31)),
                          binop(Iop_Shr32, mkexpr(rMt), mkU8(1))) );
            DIS(buf, "r%u, RRX", rM);
         } else {
            // rotate right in range 1..31
            // res  = Rm `ror` shift_amt
            // newC = Rm[shift_amt - 1]
            vassert(shift_amt >= 1 && shift_amt <= 31);
            if (newC) {
               assign( *newC,
                       binop(Iop_And32,
                             binop(Iop_Shr32, mkexpr(rMt), 
                                              mkU8(shift_amt - 1)),
                             mkU32(1)));
            }
            assign( *res,
                    binop(Iop_Or32,
                          binop(Iop_Shr32, mkexpr(rMt), mkU8(shift_amt)),
                          binop(Iop_Shl32, mkexpr(rMt),
                                           mkU8(32-shift_amt))));
            DIS(buf, "r%u, ROR #%u", rM, shift_amt);
         }
         break;

      default:
         /*NOTREACHED*/
         vassert(0);
   }
}


/* Generate an expression corresponding to the register-shift case of
   a shifter operand.  This is used both for ARM and Thumb2.

   Bind it to a temporary, and return that via *res.  If newC is
   non-NULL, also compute a value for the shifter's carry out (in the
   LSB of a word), bind it to a temporary, and return that via *shco.

   Generates GETs from the guest state and is therefore not safe to
   use once we start doing PUTs to it, for any given instruction.

   'how' is encoded thusly:
      00b LSL,  01b LSR,  10b ASR,  11b ROR
   Most but not all ARM and Thumb integer insns use this encoding.
   Be careful to ensure the right value is passed here.
*/
static void compute_result_and_C_after_shift_by_reg (
               /*OUT*/HChar*  buf,
               /*OUT*/IRTemp* res,
               /*OUT*/IRTemp* newC,
               IRTemp  rMt,       /* reg to shift */
               UInt    how,       /* what kind of shift */
               IRTemp  rSt,       /* shift amount */
               UInt    rM,        /* only for debug printing */
               UInt    rS         /* only for debug printing */
            )
{
   vassert(how < 4);
   switch (how) {
      case 0: { /* LSL */
         compute_result_and_C_after_LSL_by_reg(
            buf, res, newC, rMt, rSt, rM, rS
         );
         break;
      }
      case 1: { /* LSR */
         compute_result_and_C_after_LSR_by_reg(
            buf, res, newC, rMt, rSt, rM, rS
         );
         break;
      }
      case 2: { /* ASR */
         compute_result_and_C_after_ASR_by_reg(
            buf, res, newC, rMt, rSt, rM, rS
         );
         break;
      }
      case 3: { /* ROR */
         compute_result_and_C_after_ROR_by_reg(
             buf, res, newC, rMt, rSt, rM, rS
         );
         break;
      }
      default:
         /*NOTREACHED*/
         vassert(0);
   }
}


/* Generate an expression corresponding to a shifter_operand, bind it
   to a temporary, and return that via *shop.  If shco is non-NULL,
   also compute a value for the shifter's carry out (in the LSB of a
   word), bind it to a temporary, and return that via *shco.

   If for some reason we can't come up with a shifter operand (missing
   case?  not really a shifter operand?) return False.

   Generates GETs from the guest state and is therefore not safe to
   use once we start doing PUTs to it, for any given instruction.

   For ARM insns only; not for Thumb.
*/
static Bool mk_shifter_operand ( UInt insn_25, UInt insn_11_0,
                                 /*OUT*/IRTemp* shop,
                                 /*OUT*/IRTemp* shco,
                                 /*OUT*/HChar* buf )
{
   UInt insn_4 = (insn_11_0 >> 4) & 1;
   UInt insn_7 = (insn_11_0 >> 7) & 1;
   vassert(insn_25 <= 0x1);
   vassert(insn_11_0 <= 0xFFF);

   vassert(shop && *shop == IRTemp_INVALID);
   *shop = newTemp(Ity_I32);

   if (shco) {
      vassert(*shco == IRTemp_INVALID);
      *shco = newTemp(Ity_I32);
   }

   /* 32-bit immediate */

   if (insn_25 == 1) {
      /* immediate: (7:0) rotated right by 2 * (11:8) */
      UInt imm = (insn_11_0 >> 0) & 0xFF;
      UInt rot = 2 * ((insn_11_0 >> 8) & 0xF);
      vassert(rot <= 30);
      imm = ROR32(imm, rot);
      if (shco) {
         if (rot == 0) {
            assign( *shco, mk_armg_calculate_flag_c() );
         } else {
            assign( *shco, mkU32( (imm >> 31) & 1 ) );
         }
      }
      DIS(buf, "#0x%x", imm);
      assign( *shop, mkU32(imm) );
      return True;
   }

   /* Shift/rotate by immediate */

   if (insn_25 == 0 && insn_4 == 0) {
      /* Rm (3:0) shifted (6:5) by immediate (11:7) */
      UInt shift_amt = (insn_11_0 >> 7) & 0x1F;
      UInt rM        = (insn_11_0 >> 0) & 0xF;
      UInt how       = (insn_11_0 >> 5) & 3;
      /* how: 00 = Shl, 01 = Shr, 10 = Sar, 11 = Ror */
      IRTemp rMt = newTemp(Ity_I32);
      assign(rMt, getIRegA(rM));

      vassert(shift_amt <= 31);

      compute_result_and_C_after_shift_by_imm5(
         buf, shop, shco, rMt, how, shift_amt, rM
      );
      return True;
   }

   /* Shift/rotate by register */
   if (insn_25 == 0 && insn_4 == 1) {
      /* Rm (3:0) shifted (6:5) by Rs (11:8) */
      UInt rM  = (insn_11_0 >> 0) & 0xF;
      UInt rS  = (insn_11_0 >> 8) & 0xF;
      UInt how = (insn_11_0 >> 5) & 3;
      /* how: 00 = Shl, 01 = Shr, 10 = Sar, 11 = Ror */
      IRTemp rMt = newTemp(Ity_I32);
      IRTemp rSt = newTemp(Ity_I32);

      if (insn_7 == 1)
         return False; /* not really a shifter operand */

      assign(rMt, getIRegA(rM));
      assign(rSt, getIRegA(rS));

      compute_result_and_C_after_shift_by_reg(
         buf, shop, shco, rMt, how, rSt, rM, rS
      );
      return True;
   }

   vex_printf("mk_shifter_operand(0x%x,0x%x)\n", insn_25, insn_11_0 );
   return False;
}


/* ARM only */
static 
IRExpr* mk_EA_reg_plusminus_imm12 ( UInt rN, UInt bU, UInt imm12,
                                    /*OUT*/HChar* buf )
{
   vassert(rN < 16);
   vassert(bU < 2);
   vassert(imm12 < 0x1000);
   UChar opChar = bU == 1 ? '+' : '-';
   DIS(buf, "[r%u, #%c%u]", rN, opChar, imm12);
   return
      binop( (bU == 1 ? Iop_Add32 : Iop_Sub32),
             getIRegA(rN),
             mkU32(imm12) );
}


/* ARM only.
   NB: This is "DecodeImmShift" in newer versions of the the ARM ARM.
*/
static
IRExpr* mk_EA_reg_plusminus_shifted_reg ( UInt rN, UInt bU, UInt rM,
                                          UInt sh2, UInt imm5,
                                          /*OUT*/HChar* buf )
{
   vassert(rN < 16);
   vassert(bU < 2);
   vassert(rM < 16);
   vassert(sh2 < 4);
   vassert(imm5 < 32);
   UChar   opChar = bU == 1 ? '+' : '-';
   IRExpr* index  = NULL;
   switch (sh2) {
      case 0: /* LSL */
         /* imm5 can be in the range 0 .. 31 inclusive. */
         index = binop(Iop_Shl32, getIRegA(rM), mkU8(imm5));
         DIS(buf, "[r%u, %c r%u LSL #%u]", rN, opChar, rM, imm5); 
         break;
      case 1: /* LSR */
         if (imm5 == 0) {
            index = mkU32(0);
            vassert(0); // ATC
         } else {
            index = binop(Iop_Shr32, getIRegA(rM), mkU8(imm5));
         }
         DIS(buf, "[r%u, %cr%u, LSR #%u]",
                  rN, opChar, rM, imm5 == 0 ? 32 : imm5); 
         break;
      case 2: /* ASR */
         /* Doesn't this just mean that the behaviour with imm5 == 0
            is the same as if it had been 31 ? */
         if (imm5 == 0) {
            index = binop(Iop_Sar32, getIRegA(rM), mkU8(31));
            vassert(0); // ATC
         } else {
            index = binop(Iop_Sar32, getIRegA(rM), mkU8(imm5));
         }
         DIS(buf, "[r%u, %cr%u, ASR #%u]",
                  rN, opChar, rM, imm5 == 0 ? 32 : imm5); 
         break;
      case 3: /* ROR or RRX */
         if (imm5 == 0) {
            IRTemp rmT    = newTemp(Ity_I32);
            IRTemp cflagT = newTemp(Ity_I32);
            assign(rmT, getIRegA(rM));
            assign(cflagT, mk_armg_calculate_flag_c());
            index = binop(Iop_Or32, 
                          binop(Iop_Shl32, mkexpr(cflagT), mkU8(31)),
                          binop(Iop_Shr32, mkexpr(rmT), mkU8(1)));
            DIS(buf, "[r%u, %cr%u, RRX]", rN, opChar, rM);
         } else {
            IRTemp rmT = newTemp(Ity_I32);
            assign(rmT, getIRegA(rM));
            vassert(imm5 >= 1 && imm5 <= 31);
            index = binop(Iop_Or32, 
                          binop(Iop_Shl32, mkexpr(rmT), mkU8(32-imm5)),
                          binop(Iop_Shr32, mkexpr(rmT), mkU8(imm5)));
            DIS(buf, "[r%u, %cr%u, ROR #%u]", rN, opChar, rM, imm5); 
         }
         break;
      default:
         vassert(0);
   }
   vassert(index);
   return binop(bU == 1 ? Iop_Add32 : Iop_Sub32,
                getIRegA(rN), index);
}


/* ARM only */
static 
IRExpr* mk_EA_reg_plusminus_imm8 ( UInt rN, UInt bU, UInt imm8,
                                   /*OUT*/HChar* buf )
{
   vassert(rN < 16);
   vassert(bU < 2);
   vassert(imm8 < 0x100);
   UChar opChar = bU == 1 ? '+' : '-';
   DIS(buf, "[r%u, #%c%u]", rN, opChar, imm8);
   return
      binop( (bU == 1 ? Iop_Add32 : Iop_Sub32),
             getIRegA(rN),
             mkU32(imm8) );
}


/* ARM only */
static
IRExpr* mk_EA_reg_plusminus_reg ( UInt rN, UInt bU, UInt rM,
                                  /*OUT*/HChar* buf )
{
   vassert(rN < 16);
   vassert(bU < 2);
   vassert(rM < 16);
   UChar   opChar = bU == 1 ? '+' : '-';
   IRExpr* index  = getIRegA(rM);
   DIS(buf, "[r%u, %c r%u]", rN, opChar, rM); 
   return binop(bU == 1 ? Iop_Add32 : Iop_Sub32,
                getIRegA(rN), index);
}


/* irRes :: Ity_I32 holds a floating point comparison result encoded
   as an IRCmpF64Result.  Generate code to convert it to an
   ARM-encoded (N,Z,C,V) group in the lowest 4 bits of an I32 value.
   Assign a new temp to hold that value, and return the temp. */
static
IRTemp mk_convert_IRCmpF64Result_to_NZCV ( IRTemp irRes )
{
   IRTemp ix       = newTemp(Ity_I32);
   IRTemp termL    = newTemp(Ity_I32);
   IRTemp termR    = newTemp(Ity_I32);
   IRTemp nzcv     = newTemp(Ity_I32);

   /* This is where the fun starts.  We have to convert 'irRes' from
      an IR-convention return result (IRCmpF64Result) to an
      ARM-encoded (N,Z,C,V) group.  The final result is in the bottom
      4 bits of 'nzcv'. */
   /* Map compare result from IR to ARM(nzcv) */
   /*
      FP cmp result | IR   | ARM(nzcv)
      --------------------------------
      UN              0x45   0011
      LT              0x01   1000
      GT              0x00   0010
      EQ              0x40   0110
   */
   /* Now since you're probably wondering WTF ..

      ix fishes the useful bits out of the IR value, bits 6 and 0, and
      places them side by side, giving a number which is 0, 1, 2 or 3.

      termL is a sequence cooked up by GNU superopt.  It converts ix
         into an almost correct value NZCV value (incredibly), except
         for the case of UN, where it produces 0100 instead of the
         required 0011.

      termR is therefore a correction term, also computed from ix.  It
         is 1 in the UN case and 0 for LT, GT and UN.  Hence, to get
         the final correct value, we subtract termR from termL.

      Don't take my word for it.  There's a test program at the bottom
      of this file, to try this out with.
   */
   assign(
      ix,
      binop(Iop_Or32,
            binop(Iop_And32,
                  binop(Iop_Shr32, mkexpr(irRes), mkU8(5)),
                  mkU32(3)),
            binop(Iop_And32, mkexpr(irRes), mkU32(1))));

   assign(
      termL,
      binop(Iop_Add32,
            binop(Iop_Shr32,
                  binop(Iop_Sub32,
                        binop(Iop_Shl32,
                              binop(Iop_Xor32, mkexpr(ix), mkU32(1)),
                              mkU8(30)),
                        mkU32(1)),
                  mkU8(29)),
            mkU32(1)));

   assign(
      termR,
      binop(Iop_And32,
            binop(Iop_And32,
                  mkexpr(ix),
                  binop(Iop_Shr32, mkexpr(ix), mkU8(1))),
            mkU32(1)));

   assign(nzcv, binop(Iop_Sub32, mkexpr(termL), mkexpr(termR)));
   return nzcv;
}


/* Thumb32 only.  This is "ThumbExpandImm" in the ARM ARM.  If
   updatesC is non-NULL, a boolean is written to it indicating whether
   or not the C flag is updated, as per ARM ARM "ThumbExpandImm_C".
*/
static UInt thumbExpandImm ( Bool* updatesC,
                             UInt imm1, UInt imm3, UInt imm8 )
{
   vassert(imm1 < (1<<1));
   vassert(imm3 < (1<<3));
   vassert(imm8 < (1<<8));
   UInt i_imm3_a = (imm1 << 4) | (imm3 << 1) | ((imm8 >> 7) & 1);
   UInt abcdefgh = imm8;
   UInt lbcdefgh = imm8 | 0x80;
   if (updatesC) {
      *updatesC = i_imm3_a >= 8;
   }
   switch (i_imm3_a) {
      case 0: case 1:
         return abcdefgh;
      case 2: case 3:
         return (abcdefgh << 16) | abcdefgh;
      case 4: case 5:
         return (abcdefgh << 24) | (abcdefgh << 8);
      case 6: case 7:
         return (abcdefgh << 24) | (abcdefgh << 16)
                | (abcdefgh << 8) | abcdefgh;
      case 8 ... 31:
         return lbcdefgh << (32 - i_imm3_a);
      default:
         break;
   }
   /*NOTREACHED*/vassert(0);
}


/* Version of thumbExpandImm where we simply feed it the
   instruction halfwords (the lowest addressed one is I0). */
static UInt thumbExpandImm_from_I0_I1 ( Bool* updatesC,
                                        UShort i0s, UShort i1s )
{
   UInt i0    = (UInt)i0s;
   UInt i1    = (UInt)i1s;
   UInt imm1  = SLICE_UInt(i0,10,10);
   UInt imm3  = SLICE_UInt(i1,14,12);
   UInt imm8  = SLICE_UInt(i1,7,0);
   return thumbExpandImm(updatesC, imm1, imm3, imm8);
}


/* Thumb16 only.  Given the firstcond and mask fields from an IT
   instruction, compute the 32-bit ITSTATE value implied, as described
   in libvex_guest_arm.h.  This is not the ARM ARM representation.
   Also produce the t/e chars for the 2nd, 3rd, 4th insns, for
   disassembly printing.  Returns False if firstcond or mask
   denote something invalid.

   The number and conditions for the instructions to be
   conditionalised depend on firstcond and mask:

   mask      cond 1    cond 2      cond 3      cond 4

   1000      fc[3:0]
   x100      fc[3:0]   fc[3:1]:x
   xy10      fc[3:0]   fc[3:1]:x   fc[3:1]:y
   xyz1      fc[3:0]   fc[3:1]:x   fc[3:1]:y   fc[3:1]:z

   The condition fields are assembled in *itstate backwards (cond 4 at
   the top, cond 1 at the bottom).  Conditions are << 4'd and then
   ^0xE'd, and those fields that correspond to instructions in the IT
   block are tagged with a 1 bit.
*/
static Bool compute_ITSTATE ( /*OUT*/UInt*  itstate,
                              /*OUT*/UChar* ch1,
                              /*OUT*/UChar* ch2,
                              /*OUT*/UChar* ch3,
                              UInt firstcond, UInt mask )
{
   vassert(firstcond <= 0xF);
   vassert(mask <= 0xF);
   *itstate = 0;
   *ch1 = *ch2 = *ch3 = '.';
   if (firstcond == 0xF)
      return False; /* NV is not allowed */
   if (firstcond == 0xE && popcount32(mask) != 1) 
      return False; /* if firstcond is AL then all the rest must be too */

   UInt m3 = (mask >> 3) & 1;
   UInt m2 = (mask >> 2) & 1;
   UInt m1 = (mask >> 1) & 1;
   UInt m0 = (mask >> 0) & 1;

   UInt fc = (firstcond << 4) | 1/*in-IT-block*/;
   UInt ni = (0xE/*AL*/ << 4) | 0/*not-in-IT-block*/;

   if (m3 == 1 && (m2|m1|m0) == 0) {
      *itstate = (ni << 24) | (ni << 16) | (ni << 8) | fc;
      *itstate ^= 0xE0E0E0E0;
      return True;
   }

   if (m2 == 1 && (m1|m0) == 0) {
      *itstate = (ni << 24) | (ni << 16) | (setbit32(fc, 4, m3) << 8) | fc;
      *itstate ^= 0xE0E0E0E0;
      *ch1 = m3 == (firstcond & 1) ? 't' : 'e';
      return True;
   }

   if (m1 == 1 && m0 == 0) {
      *itstate = (ni << 24)
                 | (setbit32(fc, 4, m2) << 16)
                 | (setbit32(fc, 4, m3) << 8) | fc;
      *itstate ^= 0xE0E0E0E0;
      *ch1 = m3 == (firstcond & 1) ? 't' : 'e';
      *ch2 = m2 == (firstcond & 1) ? 't' : 'e';
      return True;
   }

   if (m0 == 1) {
      *itstate = (setbit32(fc, 4, m1) << 24)
                 | (setbit32(fc, 4, m2) << 16)
                 | (setbit32(fc, 4, m3) << 8) | fc;
      *itstate ^= 0xE0E0E0E0;
      *ch1 = m3 == (firstcond & 1) ? 't' : 'e';
      *ch2 = m2 == (firstcond & 1) ? 't' : 'e';
      *ch3 = m1 == (firstcond & 1) ? 't' : 'e';
      return True;
   }

   return False;
}


/*------------------------------------------------------------*/
/*--- LDMxx/STMxx helper (both ARM and Thumb32)            ---*/
/*------------------------------------------------------------*/

/* Generate IR for LDMxx and STMxx.  This is complex.  Assumes it's
   unconditional, so the caller must produce a jump-around before
   calling this, if the insn is to be conditional.  Caller is
   responsible for all validation of parameters.  For LDMxx, if PC is
   amongst the values loaded, caller is also responsible for
   generating the jump. */
static void mk_ldm_stm ( Bool arm,     /* True: ARM, False: Thumb */
                         UInt rN,      /* base reg */
                         UInt bINC,    /* 1: inc,  0: dec */
                         UInt bBEFORE, /* 1: inc/dec before, 0: after */
                         UInt bW,      /* 1: writeback to Rn */
                         UInt bL,      /* 1: load, 0: store */
                         UInt regList )
{
   Int i, r, m, nRegs;

   /* Get hold of the old Rn value.  We might need to write its value
      to memory during a store, and if it's also the writeback
      register then we need to get its value now.  We can't treat it
      exactly like the other registers we're going to transfer,
      because for xxMDA and xxMDB writeback forms, the generated IR
      updates Rn in the guest state before any transfers take place.
      We have to do this as per comments below, in order that if Rn is
      the stack pointer then it always has a value is below or equal
      to any of the transfer addresses.  Ick. */
   IRTemp oldRnT = newTemp(Ity_I32);
   assign(oldRnT, arm ? getIRegA(rN) : getIRegT(rN));

   IRTemp anchorT = newTemp(Ity_I32);
   /* The old (Addison-Wesley) ARM ARM seems to say that LDMxx/STMxx
      ignore the bottom two bits of the address.  However, Cortex-A8
      doesn't seem to care.  Hence: */
   /* No .. don't force alignment .. */
   /* assign(anchorT, binop(Iop_And32, mkexpr(oldRnT), mkU32(~3U))); */
   /* Instead, use the potentially misaligned address directly. */
   assign(anchorT, mkexpr(oldRnT));

   IROp opADDorSUB = bINC ? Iop_Add32 : Iop_Sub32;
   // bINC == 1:  xxMIA, xxMIB
   // bINC == 0:  xxMDA, xxMDB

   // For xxMDA and xxMDB, update Rn first if necessary.  We have
   // to do this first so that, for the common idiom of the transfers
   // faulting because we're pushing stuff onto a stack and the stack
   // is growing down onto allocate-on-fault pages (as Valgrind simulates),
   // we need to have the SP up-to-date "covering" (pointing below) the
   // transfer area.  For the same reason, if we are doing xxMIA or xxMIB,
   // do the transfer first, and then update rN afterwards.
   nRegs = 0;
   for (i = 0; i < 16; i++) {
     if ((regList & (1 << i)) != 0)
         nRegs++;
   }
   if (bW == 1 && !bINC) {
      IRExpr* e = binop(opADDorSUB, mkexpr(oldRnT), mkU32(4*nRegs));
      if (arm)
         putIRegA( rN, e, IRTemp_INVALID, Ijk_Boring );
      else
         putIRegT( rN, e, IRTemp_INVALID );
   }

   // Make up a list of the registers to transfer, and their offsets
   // in memory relative to the anchor.  If the base reg (Rn) is part
   // of the transfer, then do it last for a load and first for a store.
   UInt xReg[16], xOff[16];
   Int  nX = 0;
   m = 0;
   for (i = 0; i < 16; i++) {
      r = bINC ? i : (15-i);
      if (0 == (regList & (1<<r)))
         continue;
      if (bBEFORE)
         m++;
      /* paranoia: check we aren't transferring the writeback
         register during a load. Should be assured by decode-point
         check above. */
      if (bW == 1 && bL == 1)
         vassert(r != rN);

      xOff[nX] = 4 * m;
      xReg[nX] = r;
      nX++;

      if (!bBEFORE)
         m++;
   }
   vassert(m == nRegs);
   vassert(nX == nRegs);
   vassert(nX <= 16);

   if (bW == 0 && (regList & (1<<rN)) != 0) {
      /* Non-writeback, and basereg is to be transferred.  Do its
         transfer last for a load and first for a store.  Requires
         reordering xOff/xReg. */
      if (0) {
         vex_printf("\nREG_LIST_PRE: (rN=%d)\n", rN);
         for (i = 0; i < nX; i++)
            vex_printf("reg %d   off %d\n", xReg[i], xOff[i]);
         vex_printf("\n");
      }

      vassert(nX > 0);
      for (i = 0; i < nX; i++) {
         if (xReg[i] == rN)
             break;
      }
      vassert(i < nX); /* else we didn't find it! */
      UInt tReg = xReg[i];
      UInt tOff = xOff[i];
      if (bL == 1) {
         /* load; make this transfer happen last */
         if (i < nX-1) {
            for (m = i+1; m < nX; m++) {
               xReg[m-1] = xReg[m];
               xOff[m-1] = xOff[m];
            }
            vassert(m == nX);
            xReg[m-1] = tReg;
            xOff[m-1] = tOff;
         }
      } else {
         /* store; make this transfer happen first */
         if (i > 0) {
            for (m = i-1; m >= 0; m--) {
               xReg[m+1] = xReg[m];
               xOff[m+1] = xOff[m];
            }
            vassert(m == -1);
            xReg[0] = tReg;
            xOff[0] = tOff;
         }
      }

      if (0) {
         vex_printf("REG_LIST_POST:\n");
         for (i = 0; i < nX; i++)
            vex_printf("reg %d   off %d\n", xReg[i], xOff[i]);
         vex_printf("\n");
      }
   }

   /* Actually generate the transfers */
   for (i = 0; i < nX; i++) {
      r = xReg[i];
      if (bL == 1) {
         IRExpr* e = loadLE(Ity_I32,
                            binop(opADDorSUB, mkexpr(anchorT),
                                  mkU32(xOff[i])));
         if (arm) {
            putIRegA( r, e, IRTemp_INVALID, Ijk_Ret );
         } else {
            // no: putIRegT( r, e, IRTemp_INVALID );
            // putIRegT refuses to write to R15.  But that might happen.
            // Since this is uncond, and we need to be able to
            // write the PC, just use the low level put:
            llPutIReg( r, e );
         }
      } else {
         /* if we're storing Rn, make sure we use the correct
            value, as per extensive comments above */
         storeLE( binop(opADDorSUB, mkexpr(anchorT), mkU32(xOff[i])),
                  r == rN ? mkexpr(oldRnT) 
                          : (arm ? getIRegA(r) : getIRegT(r) ) );
      }
   }

   // If we are doing xxMIA or xxMIB,
   // do the transfer first, and then update rN afterwards.
   if (bW == 1 && bINC) {
      IRExpr* e = binop(opADDorSUB, mkexpr(oldRnT), mkU32(4*nRegs));
      if (arm)
         putIRegA( rN, e, IRTemp_INVALID, Ijk_Boring );
      else
         putIRegT( rN, e, IRTemp_INVALID );
   }
}


/*------------------------------------------------------------*/
/*--- Instructions in NV (never) space                     ---*/
/*------------------------------------------------------------*/

/* ARM only */
/* Translate a NV space instruction.  If successful, returns True and
   *dres may or may not be updated.  If failure, returns False and
   doesn't change *dres nor create any IR. */
static Bool decode_NV_instruction ( /*MOD*/DisResult* dres, UInt insn )
{
#  define INSN(_bMax,_bMin)  SLICE_UInt(insn, (_bMax), (_bMin))
#  define INSN_COND          SLICE_UInt(insn, 31, 28)

   HChar dis_buf[128];

   // Should only be called for NV instructions
   vassert(BITS4(1,1,1,1) == INSN_COND);

   /* ------------------------ pld ------------------------ */
   if (BITS8(0,1,0,1, 0, 1,0,1) == (INSN(27,20) & BITS8(1,1,1,1,0,1,1,1))
       && BITS4(1,1,1,1) == INSN(15,12)) {
      UInt rN    = INSN(19,16);
      UInt imm12 = INSN(11,0);
      UInt bU    = INSN(23,23);
      DIP("pld [r%u, #%c%u]\n", rN, bU ? '+' : '-', imm12);
      return True;
   }

   if (BITS8(0,1,1,1, 0, 1,0,1) == (INSN(27,20) & BITS8(1,1,1,1,0,1,1,1))
       && BITS4(1,1,1,1) == INSN(15,12)
       && 0 == INSN(4,4)) {
      UInt rN   = INSN(19,16);
      UInt rM   = INSN(3,0);
      UInt imm5 = INSN(11,7);
      UInt sh2  = INSN(6,5);
      UInt bU   = INSN(23,23);
      if (rM != 15) {
         IRExpr* eaE = mk_EA_reg_plusminus_shifted_reg(rN, bU, rM,
                                                       sh2, imm5, dis_buf);
         IRTemp eaT = newTemp(Ity_I32);
         /* Bind eaE to a temp merely for debugging-vex purposes, so we
            can check it's a plausible decoding.  It will get removed
            by iropt a little later on. */
         vassert(eaE);
         assign(eaT, eaE);
         DIP("pld %s\n", dis_buf);
         return True;
      }
      /* fall through */
   }

   /* --------------------- Interworking branches --------------------- */

   // BLX (1), viz, unconditional branch and link to R15+simm24
   // and set CPSR.T = 1, that is, switch to Thumb mode
   if (INSN(31,25) == BITS7(1,1,1,1,1,0,1)) {
      UInt bitH   = INSN(24,24);
      Int  uimm24 = INSN(23,0);
      Int  simm24 = (((uimm24 << 8) >> 8) << 2) + (bitH << 1);
      /* Now this is a bit tricky.  Since we're decoding an ARM insn,
         it is implies that CPSR.T == 0.  Hence the current insn's
         address is guaranteed to be of the form X--(30)--X00.  So, no
         need to mask any bits off it.  But need to set the lowest bit
         to 1 to denote we're in Thumb mode after this, since
         guest_R15T has CPSR.T as the lowest bit.  And we can't chase
         into the call, so end the block at this point. */
      UInt dst = guest_R15_curr_instr_notENC + 8 + (simm24 | 1);
      putIRegA( 14, mkU32(guest_R15_curr_instr_notENC + 4),
                    IRTemp_INVALID/*because AL*/, Ijk_Boring );
      irsb->next     = mkU32(dst);
      irsb->jumpkind = Ijk_Call;
      dres->whatNext = Dis_StopHere;
      DIP("blx 0x%x (and switch to Thumb mode)\n", dst - 1);
      return True;
   }

   /* ------------------- v7 barrier insns ------------------- */
   switch (insn) {
      case 0xF57FF06F: /* ISB */
         stmt( IRStmt_MBE(Imbe_Fence) );
         DIP("ISB\n");
         return True;
      case 0xF57FF04F: /* DSB */
         stmt( IRStmt_MBE(Imbe_Fence) );
         DIP("DSB\n");
         return True;
      case 0xF57FF05F: /* DMB */
         stmt( IRStmt_MBE(Imbe_Fence) );
         DIP("DMB\n");
         return True;
      default:
         break;
   }

   return False;

#  undef INSN_COND
#  undef INSN
}


/*------------------------------------------------------------*/
/*--- Disassemble a single ARM instruction                 ---*/
/*------------------------------------------------------------*/

/* Disassemble a single ARM instruction into IR.  The instruction is
   located in host memory at guest_instr, and has (decoded) guest IP
   of guest_R15_curr_instr_notENC, which will have been set before the
   call here. */

static   
DisResult disInstr_ARM_WRK (
             Bool         put_IP,
             Bool         (*resteerOkFn) ( /*opaque*/void*, Addr64 ),
             Bool         resteerCisOk,
             void*        callback_opaque,
             UChar*       guest_instr,
             VexArchInfo* archinfo,
             VexAbiInfo*  abiinfo
          )
{
   // A macro to fish bits out of 'insn'.
#  define INSN(_bMax,_bMin)  SLICE_UInt(insn, (_bMax), (_bMin))
#  define INSN_COND          SLICE_UInt(insn, 31, 28)

   DisResult dres;
   UInt      insn;
   //Bool      allow_VFP = False;
   //UInt      hwcaps = archinfo->hwcaps;
   IRTemp    condT; /* :: Ity_I32 */
   UInt      summary;
   HChar     dis_buf[128];  // big enough to hold LDMIA etc text

   /* What insn variants are we supporting today? */
   //allow_VFP  = (0 != (hwcaps & VEX_HWCAPS_ARM_VFP));
   // etc etc

   /* Set result defaults. */
   dres.whatNext   = Dis_Continue;
   dres.len        = 4;
   dres.continueAt = 0;

   /* Set default actions for post-insn handling of writes to r15, if
      required. */
   r15written = False;
   r15guard   = IRTemp_INVALID; /* unconditional */
   r15kind    = Ijk_Boring;

   /* At least this is simple on ARM: insns are all 4 bytes long, and
      4-aligned.  So just fish the whole thing out of memory right now
      and have done. */
   insn = getUIntLittleEndianly( guest_instr );

   if (0) vex_printf("insn: 0x%x\n", insn);

   DIP("\t(arm) 0x%x:  ", (UInt)guest_R15_curr_instr_notENC);

   /* We may be asked to update the guest R15 before going further. */
   vassert(0 == (guest_R15_curr_instr_notENC & 3));
   if (put_IP) {
      llPutIReg( 15, mkU32(guest_R15_curr_instr_notENC) );
   }

   /* ----------------------------------------------------------- */

   /* Spot "Special" instructions (see comment at top of file). */
   {
      UChar* code = (UChar*)guest_instr;
      /* Spot the 16-byte preamble: 

         e1a0c1ec  mov r12, r12, ROR #3
         e1a0c6ec  mov r12, r12, ROR #13
         e1a0ceec  mov r12, r12, ROR #29
         e1a0c9ec  mov r12, r12, ROR #19
      */
      UInt word1 = 0xE1A0C1EC;
      UInt word2 = 0xE1A0C6EC;
      UInt word3 = 0xE1A0CEEC;
      UInt word4 = 0xE1A0C9EC;
      if (getUIntLittleEndianly(code+ 0) == word1 &&
          getUIntLittleEndianly(code+ 4) == word2 &&
          getUIntLittleEndianly(code+ 8) == word3 &&
          getUIntLittleEndianly(code+12) == word4) {
         /* Got a "Special" instruction preamble.  Which one is it? */
         if (getUIntLittleEndianly(code+16) == 0xE18AA00A
                                               /* orr r10,r10,r10 */) {
            /* R3 = client_request ( R4 ) */
            DIP("r3 = client_request ( %%r4 )\n");
            irsb->next     = mkU32( guest_R15_curr_instr_notENC + 20 );
            irsb->jumpkind = Ijk_ClientReq;
            dres.whatNext  = Dis_StopHere;
            goto decode_success;
         }
         else
         if (getUIntLittleEndianly(code+16) == 0xE18BB00B
                                               /* orr r11,r11,r11 */) {
            /* R3 = guest_NRADDR */
            DIP("r3 = guest_NRADDR\n");
            dres.len = 20;
            llPutIReg(3, IRExpr_Get( OFFB_NRADDR, Ity_I32 ));
            goto decode_success;
         }
         else
         if (getUIntLittleEndianly(code+16) == 0xE18CC00C
                                               /* orr r12,r12,r12 */) {
            /*  branch-and-link-to-noredir R4 */
            DIP("branch-and-link-to-noredir r4\n");
            llPutIReg(14, mkU32( guest_R15_curr_instr_notENC + 20) );
            irsb->next     = llGetIReg(4);
            irsb->jumpkind = Ijk_NoRedir;
            dres.whatNext  = Dis_StopHere;
            goto decode_success;
         }
         /* We don't know what it is.  Set opc1/opc2 so decode_failure
            can print the insn following the Special-insn preamble. */
         insn = getUIntLittleEndianly(code+16);
         goto decode_failure;
         /*NOTREACHED*/
      }

   }

   /* ----------------------------------------------------------- */

   /* Main ARM instruction decoder starts here. */

   /* Deal with the condition.  Strategy is to merely generate a
      condition temporary at this point (or IRTemp_INVALID, meaning
      unconditional).  We leave it to lower-level instruction decoders
      to decide whether they can generate straight-line code, or
      whether they must generate a side exit before the instruction.
      condT :: Ity_I32 and is always either zero or one. */
   condT = IRTemp_INVALID;
   switch ( (ARMCondcode)INSN_COND ) {
      case ARMCondNV: {
         // Illegal instruction prior to v5 (see ARM ARM A3-5), but
         // some cases are acceptable
         Bool ok = decode_NV_instruction(&dres, insn);
         if (ok)
            goto decode_success;
         else
            goto decode_failure;
      }
      case ARMCondAL: // Always executed
         break;
      case ARMCondEQ: case ARMCondNE: case ARMCondHS: case ARMCondLO:
      case ARMCondMI: case ARMCondPL: case ARMCondVS: case ARMCondVC:
      case ARMCondHI: case ARMCondLS: case ARMCondGE: case ARMCondLT:
      case ARMCondGT: case ARMCondLE:
         condT = newTemp(Ity_I32);
         assign( condT, mk_armg_calculate_condition( INSN_COND ));
         break;
   }

   /* ----------------------------------------------------------- */
   /* -- ARMv5 integer instructions                            -- */
   /* ----------------------------------------------------------- */

   /* ---------------- Data processing ops ------------------- */

   if (0 == (INSN(27,20) & BITS8(1,1,0,0,0,0,0,0))
       && !(INSN(25,25) == 0 && INSN(7,7) == 1 && INSN(4,4) == 1)) {
      IRTemp  shop = IRTemp_INVALID; /* shifter operand */
      IRTemp  shco = IRTemp_INVALID; /* shifter carry out */
      UInt    rD   = (insn >> 12) & 0xF; /* 15:12 */
      UInt    rN   = (insn >> 16) & 0xF; /* 19:16 */
      UInt    bitS = (insn >> 20) & 1; /* 20:20 */
      IRTemp  rNt  = IRTemp_INVALID;
      IRTemp  res  = IRTemp_INVALID;
      IRTemp  oldV = IRTemp_INVALID;
      IRTemp  oldC = IRTemp_INVALID;
      HChar*  name = NULL;
      IROp    op   = Iop_INVALID;
      Bool    ok;

      switch (INSN(24,21)) {

         /* --------- ADD, SUB, AND, OR --------- */
         case BITS4(0,1,0,0): /* ADD:  Rd = Rn + shifter_operand */
            name = "add"; op = Iop_Add32; goto rd_eq_rn_op_SO;
         case BITS4(0,0,1,0): /* SUB:  Rd = Rn - shifter_operand */
            name = "sub"; op = Iop_Sub32; goto rd_eq_rn_op_SO;
         case BITS4(0,0,1,1): /* RSB:  Rd = shifter_operand - Rn */
            name = "rsb"; op = Iop_Sub32; goto rd_eq_rn_op_SO;
         case BITS4(0,0,0,0): /* AND:  Rd = Rn & shifter_operand */
            name = "and"; op = Iop_And32; goto rd_eq_rn_op_SO;
         case BITS4(1,1,0,0): /* OR:   Rd = Rn | shifter_operand */
            name = "orr"; op = Iop_Or32; goto rd_eq_rn_op_SO;
         case BITS4(0,0,0,1): /* EOR:  Rd = Rn ^ shifter_operand */
            name = "eor"; op = Iop_Xor32; goto rd_eq_rn_op_SO;
         case BITS4(1,1,1,0): /* BIC:  Rd = Rn & ~shifter_operand */
            name = "bic"; op = Iop_And32; goto rd_eq_rn_op_SO;
         rd_eq_rn_op_SO: {
            Bool isRSB = False;
            Bool isBIC = False;
            switch (INSN(24,21)) {
               case BITS4(0,0,1,1):
                  vassert(op == Iop_Sub32); isRSB = True; break;
               case BITS4(1,1,1,0):
                  vassert(op == Iop_And32); isBIC = True; break;
               default:
                  break;
            }
            rNt = newTemp(Ity_I32);
            assign(rNt, getIRegA(rN));
            ok = mk_shifter_operand(
                    INSN(25,25), INSN(11,0), 
                    &shop, bitS ? &shco : NULL, dis_buf
                 );
            if (!ok)
               break;
            res = newTemp(Ity_I32);
            // compute the main result
            if (isRSB) {
               // reverse-subtract: shifter_operand - Rn
               vassert(op == Iop_Sub32);
               assign(res, binop(op, mkexpr(shop), mkexpr(rNt)) );
            } else if (isBIC) {
               // andn: shifter_operand & ~Rn
               vassert(op == Iop_And32);
               assign(res, binop(op, mkexpr(rNt),
                                     unop(Iop_Not32, mkexpr(shop))) );
            } else {
               // normal: Rn op shifter_operand
               assign(res, binop(op, mkexpr(rNt), mkexpr(shop)) );
            }
            // but don't commit it until after we've finished
            // all necessary reads from the guest state
            if (bitS
                && (op == Iop_And32 || op == Iop_Or32 || op == Iop_Xor32)) {
               oldV = newTemp(Ity_I32);
               assign( oldV, mk_armg_calculate_flag_v() );
            }
            // can't safely read guest state after here
            // now safe to put the main result
            putIRegA( rD, mkexpr(res), condT, Ijk_Boring );
            // XXXX!! not safe to read any guest state after
            // this point (I think the code below doesn't do that).
            if (!bitS)
               vassert(shco == IRTemp_INVALID);
            /* Update the flags thunk if necessary */
            if (bitS) {
               vassert(shco != IRTemp_INVALID);
               switch (op) {
                  case Iop_Add32:
                     setFlags_D1_D2( ARMG_CC_OP_ADD, rNt, shop, condT );
                     break;
                  case Iop_Sub32:
                     if (isRSB) {
                        setFlags_D1_D2( ARMG_CC_OP_SUB, shop, rNt, condT );
                     } else {
                        setFlags_D1_D2( ARMG_CC_OP_SUB, rNt, shop, condT );
                     }
                     break;
                  case Iop_And32: /* BIC and AND set the flags the same */
                  case Iop_Or32:
                  case Iop_Xor32:
                     // oldV has been read just above
                     setFlags_D1_D2_ND( ARMG_CC_OP_LOGIC,
                                        res, shco, oldV, condT );
                     break;
                  default:
                     vassert(0);
               }
            }
            DIP("%s%s%s r%u, r%u, %s\n",
                name, nCC(INSN_COND), bitS ? "s" : "", rD, rN, dis_buf );
            goto decode_success;
         }

         /* --------- MOV, MVN --------- */
         case BITS4(1,1,0,1):   /* MOV: Rd = shifter_operand */
         case BITS4(1,1,1,1): { /* MVN: Rd = not(shifter_operand) */
            Bool isMVN = INSN(24,21) == BITS4(1,1,1,1);
            if (rN != 0)
               break; /* rN must be zero */
            ok = mk_shifter_operand(
                    INSN(25,25), INSN(11,0), 
                    &shop, bitS ? &shco : NULL, dis_buf
                 );
            if (!ok)
               break;
            res = newTemp(Ity_I32);
            assign( res, isMVN ? unop(Iop_Not32, mkexpr(shop))
                               : mkexpr(shop) );
            if (bitS) {
               vassert(shco != IRTemp_INVALID);
               oldV = newTemp(Ity_I32);
               assign( oldV, mk_armg_calculate_flag_v() );
            } else {
               vassert(shco == IRTemp_INVALID);
            }
            // can't safely read guest state after here
            putIRegA( rD, mkexpr(res), condT, Ijk_Boring );
            /* Update the flags thunk if necessary */
            if (bitS) {
               setFlags_D1_D2_ND( ARMG_CC_OP_LOGIC, 
                                  res, shco, oldV, condT );
            }
            DIP("%s%s%s r%u, %s\n",
                isMVN ? "mvn" : "mov",
                nCC(INSN_COND), bitS ? "s" : "", rD, dis_buf );
            goto decode_success;
         }

         /* --------- CMP --------- */
         case BITS4(1,0,1,0):   /* CMP:  (void) Rn - shifter_operand */
         case BITS4(1,0,1,1): { /* CMN:  (void) Rn + shifter_operand */
            Bool isCMN = INSN(24,21) == BITS4(1,0,1,1);
            if (rD != 0)
               break; /* rD must be zero */
            if (bitS == 0)
               break; /* if S (bit 20) is not set, it's not CMP/CMN */
            rNt = newTemp(Ity_I32);
            assign(rNt, getIRegA(rN));
            ok = mk_shifter_operand(
                    INSN(25,25), INSN(11,0), 
                    &shop, NULL, dis_buf
                 );
            if (!ok)
               break;
            // can't safely read guest state after here
            /* Update the flags thunk. */
            setFlags_D1_D2( isCMN ? ARMG_CC_OP_ADD : ARMG_CC_OP_SUB,
                            rNt, shop, condT );
            DIP("%s%s r%u, %s\n",
                isCMN ? "cmn" : "cmp",
                nCC(INSN_COND), rN, dis_buf );
            goto decode_success;
         }

         /* --------- TST --------- */
         case BITS4(1,0,0,0):   /* TST:  (void) Rn & shifter_operand */
         case BITS4(1,0,0,1): { /* TEQ:  (void) Rn ^ shifter_operand */
            Bool isTEQ = INSN(24,21) == BITS4(1,0,0,1);
            if (rD != 0)
               break; /* rD must be zero */
            if (bitS == 0)
               break; /* if S (bit 20) is not set, it's not TST/TEQ */
            rNt = newTemp(Ity_I32);
            assign(rNt, getIRegA(rN));
            ok = mk_shifter_operand(
                    INSN(25,25), INSN(11,0), 
                    &shop, &shco, dis_buf
                 );
            if (!ok)
               break;
            /* Update the flags thunk. */
            res = newTemp(Ity_I32);
            assign( res, binop(isTEQ ? Iop_Xor32 : Iop_And32, 
                               mkexpr(rNt), mkexpr(shop)) );
            oldV = newTemp(Ity_I32);
            assign( oldV, mk_armg_calculate_flag_v() );
            // can't safely read guest state after here
            setFlags_D1_D2_ND( ARMG_CC_OP_LOGIC,
                               res, shco, oldV, condT );
            DIP("%s%s r%u, %s\n",
                isTEQ ? "teq" : "tst",
                nCC(INSN_COND), rN, dis_buf );
            goto decode_success;
         }

         /* --------- ADC, SBC, RSC --------- */
         case BITS4(0,1,0,1): /* ADC:  Rd = Rn + shifter_operand + oldC */
            name = "adc"; goto rd_eq_rn_op_SO_op_oldC;
         case BITS4(0,1,1,0): /* SBC:  Rd = Rn - shifter_operand - (oldC ^ 1) */
            name = "sbc"; goto rd_eq_rn_op_SO_op_oldC;
         case BITS4(0,1,1,1): /* RSC:  Rd = shifter_operand - Rn - (oldC ^ 1) */
            name = "rsc"; goto rd_eq_rn_op_SO_op_oldC;
         rd_eq_rn_op_SO_op_oldC: {
            rNt = newTemp(Ity_I32);
            assign(rNt, getIRegA(rN));
            ok = mk_shifter_operand(
                    INSN(25,25), INSN(11,0), 
                    &shop, bitS ? &shco : NULL, dis_buf
                 );
            if (!ok)
               break;
            oldC = newTemp(Ity_I32);
            assign( oldC, mk_armg_calculate_flag_c() );
            res = newTemp(Ity_I32);
            // compute the main result
            switch (INSN(24,21)) {
               case BITS4(0,1,0,1): /* ADC */
                  assign(res,
                         binop(Iop_Add32,
                               binop(Iop_Add32, mkexpr(rNt), mkexpr(shop)),
                               mkexpr(oldC) ));
                  break;
               case BITS4(0,1,1,0): /* SBC */
                  assign(res,
                         binop(Iop_Sub32,
                               binop(Iop_Sub32, mkexpr(rNt), mkexpr(shop)),
                               binop(Iop_Xor32, mkexpr(oldC), mkU32(1)) ));
                  break;
               case BITS4(0,1,1,1): /* RSC */
                  assign(res,
                         binop(Iop_Sub32,
                               binop(Iop_Sub32, mkexpr(shop), mkexpr(rNt)),
                               binop(Iop_Xor32, mkexpr(oldC), mkU32(1)) ));
                  break;
               default:
                  vassert(0);
            }
            // but don't commit it until after we've finished
            // all necessary reads from the guest state
            // now safe to put the main result
            putIRegA( rD, mkexpr(res), condT, Ijk_Boring );
            // XXXX!! not safe to read any guest state after
            // this point (I think the code below doesn't do that).
            if (!bitS)
               vassert(shco == IRTemp_INVALID);
            /* Update the flags thunk if necessary */
            if (bitS) {
               vassert(shco != IRTemp_INVALID);
               switch (INSN(24,21)) {
                  case BITS4(0,1,0,1): /* ADC */
                     setFlags_D1_D2_ND( ARMG_CC_OP_ADC,
                                        rNt, shop, oldC, condT );
                     break;
                  case BITS4(0,1,1,0): /* SBC */
                     setFlags_D1_D2_ND( ARMG_CC_OP_SBB,
                                        rNt, shop, oldC, condT );
                     break;
                  case BITS4(0,1,1,1): /* RSC */
                     setFlags_D1_D2_ND( ARMG_CC_OP_SBB,
                                        shop, rNt, oldC, condT );
                     break;
                  default:
                     vassert(0);
               }
            }
            DIP("%s%s%s r%u, r%u, %s\n",
                name, nCC(INSN_COND), bitS ? "s" : "", rD, rN, dis_buf );
            goto decode_success;
         }

         /* --------- ??? --------- */
         default:
            break;
      }
   } /* if (0 == (INSN(27,20) & BITS8(1,1,0,0,0,0,0,0)) */

   /* --------------------- Load/store (ubyte & word) -------- */
   // LDR STR LDRB STRB
   /*                 31   27   23   19 15 11    6   4 3  # highest bit
                        28   24   20 16 12
      A5-20   1 | 16  cond 0101 UB0L Rn Rd imm12
      A5-22   1 | 32  cond 0111 UBOL Rn Rd imm5  sh2 0 Rm
      A5-24   2 | 16  cond 0101 UB1L Rn Rd imm12
      A5-26   2 | 32  cond 0111 UB1L Rn Rd imm5  sh2 0 Rm
      A5-28   3 | 16  cond 0100 UB0L Rn Rd imm12
      A5-32   3 | 32  cond 0110 UB0L Rn Rd imm5  sh2 0 Rm
   */
   /* case coding:
             1   at-ea               (access at ea)
             2   at-ea-then-upd      (access at ea, then Rn = ea)
             3   at-Rn-then-upd      (access at Rn, then Rn = ea)
      ea coding
             16  Rn +/- imm12
             32  Rn +/- Rm sh2 imm5
   */
   /* Quickly skip over all of this for hopefully most instructions */
   if ((INSN(27,24) & BITS4(1,1,0,0)) != BITS4(0,1,0,0))
      goto after_load_store_ubyte_or_word;

   summary = 0;
   
   /**/ if (INSN(27,24) == BITS4(0,1,0,1) && INSN(21,21) == 0) {
      summary = 1 | 16;
   }
   else if (INSN(27,24) == BITS4(0,1,1,1) && INSN(21,21) == 0
                                          && INSN(4,4) == 0) {
      summary = 1 | 32;
   }
   else if (INSN(27,24) == BITS4(0,1,0,1) && INSN(21,21) == 1) {
      summary = 2 | 16;
   }
   else if (INSN(27,24) == BITS4(0,1,1,1) && INSN(21,21) == 1
                                          && INSN(4,4) == 0) {
      summary = 2 | 32;
   }
   else if (INSN(27,24) == BITS4(0,1,0,0) && INSN(21,21) == 0) {
      summary = 3 | 16;
   }
   else if (INSN(27,24) == BITS4(0,1,1,0) && INSN(21,21) == 0
                                          && INSN(4,4) == 0) {
      summary = 3 | 32;
   }
   else goto after_load_store_ubyte_or_word;

   { UInt rN = (insn >> 16) & 0xF; /* 19:16 */
     UInt rD = (insn >> 12) & 0xF; /* 15:12 */
     UInt rM = (insn >> 0)  & 0xF; /*  3:0  */
     UInt bU = (insn >> 23) & 1;      /* 23 */
     UInt bB = (insn >> 22) & 1;      /* 22 */
     UInt bL = (insn >> 20) & 1;      /* 20 */
     UInt imm12 = (insn >> 0) & 0xFFF; /* 11:0 */
     UInt imm5  = (insn >> 7) & 0x1F;  /* 11:7 */
     UInt sh2   = (insn >> 5) & 3;     /* 6:5 */

     /* Skip some invalid cases, which would lead to two competing
        updates to the same register, or which are otherwise
        disallowed by the spec. */
     switch (summary) {
        case 1 | 16:
           break;
        case 1 | 32: 
           if (rM == 15) goto after_load_store_ubyte_or_word;
           break;
        case 2 | 16: case 3 | 16:
           if (rN == 15) goto after_load_store_ubyte_or_word;
           if (bL == 1 && rN == rD) goto after_load_store_ubyte_or_word;
           break;
        case 2 | 32: case 3 | 32:
           if (rM == 15) goto after_load_store_ubyte_or_word;
           if (rN == 15) goto after_load_store_ubyte_or_word;
           if (rN == rM) goto after_load_store_ubyte_or_word;
           if (bL == 1 && rN == rD) goto after_load_store_ubyte_or_word;
           break;
        default:
           vassert(0);
     }

     /* Now, we can't do a conditional load or store, since that very
        likely will generate an exception.  So we have to take a side
        exit at this point if the condition is false. */
     if (condT != IRTemp_INVALID) {
        mk_skip_over_A32_if_cond_is_false( condT );
        condT = IRTemp_INVALID;
     }
     /* Ok, now we're unconditional.  Do the load or store. */

     /* compute the effective address.  Bind it to a tmp since we
        may need to use it twice. */
     IRExpr* eaE = NULL;
     switch (summary & 0xF0) {
        case 16:
           eaE = mk_EA_reg_plusminus_imm12( rN, bU, imm12, dis_buf );
           break;
        case 32:
           eaE = mk_EA_reg_plusminus_shifted_reg( rN, bU, rM, sh2, imm5,
                                                  dis_buf );
           break;
     }
     vassert(eaE);
     IRTemp eaT = newTemp(Ity_I32);
     assign(eaT, eaE);

     /* get the old Rn value */
     IRTemp rnT = newTemp(Ity_I32);
     assign(rnT, getIRegA(rN));

     /* decide on the transfer address */
     IRTemp taT = IRTemp_INVALID;
     switch (summary & 0x0F) {
        case 1: case 2: taT = eaT; break;
        case 3:         taT = rnT; break;
     }
     vassert(taT != IRTemp_INVALID);

     if (bL == 0) {
       /* Store.  If necessary, update the base register before the
          store itself, so that the common idiom of "str rX, [sp,
          #-4]!" (store rX at sp-4, then do new sp = sp-4, a.k.a "push
          rX") doesn't cause Memcheck to complain that the access is
          below the stack pointer.  Also, not updating sp before the
          store confuses Valgrind's dynamic stack-extending logic.  So
          do it before the store.  Hence we need to snarf the store
          data before doing the basereg update. */

        /* get hold of the data to be stored */
        IRTemp rDt = newTemp(Ity_I32);
        assign(rDt, getIRegA(rD));

        /* Update Rn if necessary. */
        switch (summary & 0x0F) {
           case 2: case 3:
              putIRegA( rN, mkexpr(eaT), IRTemp_INVALID, Ijk_Boring );
              break;
        }

        /* generate the transfer */
        if (bB == 0) { // word store
           storeLE( mkexpr(taT), mkexpr(rDt) );
        } else { // byte store
           vassert(bB == 1);
           storeLE( mkexpr(taT), unop(Iop_32to8, mkexpr(rDt)) );
        }

     } else {
        /* Load */
        vassert(bL == 1);

        /* generate the transfer */
        if (bB == 0) { // word load
           putIRegA( rD, loadLE(Ity_I32, mkexpr(taT)),
                     IRTemp_INVALID, Ijk_Boring );
        } else { // byte load
           vassert(bB == 1);
           putIRegA( rD, unop(Iop_8Uto32, loadLE(Ity_I8, mkexpr(taT))),
                     IRTemp_INVALID, Ijk_Boring );
        }

        /* Update Rn if necessary. */
        switch (summary & 0x0F) {
           case 2: case 3:
              // should be assured by logic above:
              if (bL == 1)
                 vassert(rD != rN); /* since we just wrote rD */
              putIRegA( rN, mkexpr(eaT), IRTemp_INVALID, Ijk_Boring );
              break;
        }
     }
 
     switch (summary & 0x0F) {
        case 1:  DIP("%sr%s%s r%u, %s\n",
                     bL == 0 ? "st" : "ld",
                     bB == 0 ? "" : "b", nCC(INSN_COND), rD, dis_buf);
                 break;
        case 2:  DIP("%sr%s%s r%u, %s! (at-EA-then-Rn=EA)\n",
                     bL == 0 ? "st" : "ld",
                     bB == 0 ? "" : "b", nCC(INSN_COND), rD, dis_buf);
                 break;
        case 3:  DIP("%sr%s%s r%u, %s! (at-Rn-then-Rn=EA)\n",
                     bL == 0 ? "st" : "ld",
                     bB == 0 ? "" : "b", nCC(INSN_COND), rD, dis_buf);
                 break;
        default: vassert(0);
     }

     /* XXX deal with alignment constraints */

     goto decode_success;

     /* Complications:

        For all loads: if the Amode specifies base register
        writeback, and the same register is specified for Rd and Rn,
        the results are UNPREDICTABLE.

        For all loads and stores: if R15 is written, branch to
        that address afterwards.

        STRB: straightforward
        LDRB: loaded data is zero extended
        STR:  lowest 2 bits of address are ignored
        LDR:  if the lowest 2 bits of the address are nonzero
              then the loaded value is rotated right by 8 * the lowest 2 bits
     */
   }

  after_load_store_ubyte_or_word:

   /* --------------------- Load/store (sbyte & hword) -------- */
   // LDRH LDRSH STRH LDRSB
   /*                 31   27   23   19 15 11   7    3     # highest bit
                        28   24   20 16 12    8    4    0
      A5-36   1 | 16  cond 0001 U10L Rn Rd im4h 1SH1 im4l
      A5-38   1 | 32  cond 0001 U00L Rn Rd 0000 1SH1 Rm
      A5-40   2 | 16  cond 0001 U11L Rn Rd im4h 1SH1 im4l
      A5-42   2 | 32  cond 0001 U01L Rn Rd 0000 1SH1 Rm
      A5-44   3 | 16  cond 0000 U10L Rn Rd im4h 1SH1 im4l
      A5-46   3 | 32  cond 0000 U00L Rn Rd 0000 1SH1 Rm
   */
   /* case coding:
             1   at-ea               (access at ea)
             2   at-ea-then-upd      (access at ea, then Rn = ea)
             3   at-Rn-then-upd      (access at Rn, then Rn = ea)
      ea coding
             16  Rn +/- imm8
             32  Rn +/- Rm
   */
   /* Quickly skip over all of this for hopefully most instructions */
   if ((INSN(27,24) & BITS4(1,1,1,0)) != BITS4(0,0,0,0))
      goto after_load_store_sbyte_or_hword;

   /* Check the "1SH1" thing. */
   if ((INSN(7,4) & BITS4(1,0,0,1)) != BITS4(1,0,0,1))
      goto after_load_store_sbyte_or_hword;

   summary = 0;

   /**/ if (INSN(27,24) == BITS4(0,0,0,1) && INSN(22,21) == BITS2(1,0)) {
      summary = 1 | 16;
   }
   else if (INSN(27,24) == BITS4(0,0,0,1) && INSN(22,21) == BITS2(0,0)) {
      summary = 1 | 32;
   }
   else if (INSN(27,24) == BITS4(0,0,0,1) && INSN(22,21) == BITS2(1,1)) {
      summary = 2 | 16;
   }
   else if (INSN(27,24) == BITS4(0,0,0,1) && INSN(22,21) == BITS2(0,1)) {
      summary = 2 | 32;
   }
   else if (INSN(27,24) == BITS4(0,0,0,0) && INSN(22,21) == BITS2(1,0)) {
      summary = 3 | 16;
   }
   else if (INSN(27,24) == BITS4(0,0,0,0) && INSN(22,21) == BITS2(0,0)) {
      summary = 3 | 32;
   }
   else goto after_load_store_sbyte_or_hword;

   { UInt rN   = (insn >> 16) & 0xF; /* 19:16 */
     UInt rD   = (insn >> 12) & 0xF; /* 15:12 */
     UInt rM   = (insn >> 0)  & 0xF; /*  3:0  */
     UInt bU   = (insn >> 23) & 1;   /* 23 U=1 offset+, U=0 offset- */
     UInt bL   = (insn >> 20) & 1;   /* 20 L=1 load, L=0 store */
     UInt bH   = (insn >> 5) & 1;    /* H=1 halfword, H=0 byte */
     UInt bS   = (insn >> 6) & 1;    /* S=1 signed, S=0 unsigned */
     UInt imm8 = ((insn >> 4) & 0xF0) | (insn & 0xF); /* 11:8, 3:0 */

     /* Skip combinations that are either meaningless or already
        handled by main word-or-unsigned-byte load-store
        instructions. */
     if (bS == 0 && bH == 0) /* "unsigned byte" */
        goto after_load_store_sbyte_or_hword;
     if (bS == 1 && bL == 0) /* "signed store" */
        goto after_load_store_sbyte_or_hword;

     /* Require 11:8 == 0 for Rn +/- Rm cases */
     if ((summary & 32) != 0 && (imm8 & 0xF0) != 0)
        goto after_load_store_sbyte_or_hword;

     /* Skip some invalid cases, which would lead to two competing
        updates to the same register, or which are otherwise
        disallowed by the spec. */
     switch (summary) {
        case 1 | 16:
           break;
        case 1 | 32: 
           if (rM == 15) goto after_load_store_sbyte_or_hword;
           break;
        case 2 | 16: case 3 | 16:
           if (rN == 15) goto after_load_store_sbyte_or_hword;
           if (bL == 1 && rN == rD) goto after_load_store_sbyte_or_hword;
           break;
        case 2 | 32: case 3 | 32:
           if (rM == 15) goto after_load_store_sbyte_or_hword;
           if (rN == 15) goto after_load_store_sbyte_or_hword;
           if (rN == rM) goto after_load_store_sbyte_or_hword;
           if (bL == 1 && rN == rD) goto after_load_store_sbyte_or_hword;
           break;
        default:
           vassert(0);
     }

     /* Now, we can't do a conditional load or store, since that very
        likely will generate an exception.  So we have to take a side
        exit at this point if the condition is false. */
     if (condT != IRTemp_INVALID) {
        mk_skip_over_A32_if_cond_is_false( condT );
        condT = IRTemp_INVALID;
     }
     /* Ok, now we're unconditional.  Do the load or store. */

     /* compute the effective address.  Bind it to a tmp since we
        may need to use it twice. */
     IRExpr* eaE = NULL;
     switch (summary & 0xF0) {
        case 16:
           eaE = mk_EA_reg_plusminus_imm8( rN, bU, imm8, dis_buf );
           break;
        case 32:
           eaE = mk_EA_reg_plusminus_reg( rN, bU, rM, dis_buf );
           break;
     }
     vassert(eaE);
     IRTemp eaT = newTemp(Ity_I32);
     assign(eaT, eaE);

     /* get the old Rn value */
     IRTemp rnT = newTemp(Ity_I32);
     assign(rnT, getIRegA(rN));

     /* decide on the transfer address */
     IRTemp taT = IRTemp_INVALID;
     switch (summary & 0x0F) {
        case 1: case 2: taT = eaT; break;
        case 3:         taT = rnT; break;
     }
     vassert(taT != IRTemp_INVALID);

     /* halfword store  H 1  L 0  S 0
        uhalf load      H 1  L 1  S 0
        shalf load      H 1  L 1  S 1
        sbyte load      H 0  L 1  S 1
     */
     HChar* name = NULL;
     /* generate the transfer */
     /**/ if (bH == 1 && bL == 0 && bS == 0) { // halfword store
        storeLE( mkexpr(taT), unop(Iop_32to16, getIRegA(rD)) );
        name = "strh";
     }
     else if (bH == 1 && bL == 1 && bS == 0) { // uhalf load
        putIRegA( rD, unop(Iop_16Uto32, loadLE(Ity_I16, mkexpr(taT))),
                  IRTemp_INVALID, Ijk_Boring );
        name = "ldrh";
     }
     else if (bH == 1 && bL == 1 && bS == 1) { // shalf load
        putIRegA( rD, unop(Iop_16Sto32, loadLE(Ity_I16, mkexpr(taT))),
                  IRTemp_INVALID, Ijk_Boring );
        name = "ldrsh";
     }
     else if (bH == 0 && bL == 1 && bS == 1) { // sbyte load
        putIRegA( rD, unop(Iop_8Sto32, loadLE(Ity_I8, mkexpr(taT))),
                  IRTemp_INVALID, Ijk_Boring );
        name = "ldrsb";
     }
     else
        vassert(0); // should be assured by logic above

     /* Update Rn if necessary. */
     switch (summary & 0x0F) {
        case 2: case 3:
           // should be assured by logic above:
           if (bL == 1)
              vassert(rD != rN); /* since we just wrote rD */
           putIRegA( rN, mkexpr(eaT), IRTemp_INVALID, Ijk_Boring );
           break;
     }

     switch (summary & 0x0F) {
        case 1:  DIP("%s%s r%u, %s\n", name, nCC(INSN_COND), rD, dis_buf);
                 break;
        case 2:  DIP("%s%s r%u, %s! (at-EA-then-Rn=EA)\n",
                     name, nCC(INSN_COND), rD, dis_buf);
                 break;
        case 3:  DIP("%s%s r%u, %s! (at-Rn-then-Rn=EA)\n",
                     name, nCC(INSN_COND), rD, dis_buf);
                 break;
        default: vassert(0);
     }

     /* XXX deal with alignment constraints */

     goto decode_success;

     /* Complications:

        For all loads: if the Amode specifies base register
        writeback, and the same register is specified for Rd and Rn,
        the results are UNPREDICTABLE.

        For all loads and stores: if R15 is written, branch to
        that address afterwards.

        Misaligned halfword stores => Unpredictable
        Misaligned halfword loads  => Unpredictable
     */
   }

  after_load_store_sbyte_or_hword:

   /* --------------------- Load/store multiple -------------- */
   // LD/STMIA LD/STMIB LD/STMDA LD/STMDB
   // Remarkably complex and difficult to get right
   // match 27:20 as 100XX0WL
   if (BITS8(1,0,0,0,0,0,0,0) == (INSN(27,20) & BITS8(1,1,1,0,0,1,0,0))) {
      // A5-50 LD/STMIA  cond 1000 10WL Rn RegList
      // A5-51 LD/STMIB  cond 1001 10WL Rn RegList
      // A5-53 LD/STMDA  cond 1000 00WL Rn RegList
      // A5-53 LD/STMDB  cond 1001 00WL Rn RegList
      //                   28   24   20 16       0

      UInt bINC    = (insn >> 23) & 1;
      UInt bBEFORE = (insn >> 24) & 1;

      UInt bL      = (insn >> 20) & 1;  /* load=1, store=0 */
      UInt bW      = (insn >> 21) & 1;  /* Rn wback=1, no wback=0 */
      UInt rN      = (insn >> 16) & 0xF;
      UInt regList = insn & 0xFFFF;
      /* Skip some invalid cases, which would lead to two competing
         updates to the same register, or which are otherwise
         disallowed by the spec.  Note the test above has required
         that S == 0, since that looks like a kernel-mode only thing.
         Done by forcing the real pattern, viz 100XXSWL to actually be
         100XX0WL. */
      if (rN == 15) goto after_load_store_multiple;
      // reglist can't be empty
      if (regList == 0) goto after_load_store_multiple;
      // if requested to writeback Rn, and this is a load instruction,
      // then Rn can't appear in RegList, since we'd have two competing
      // new values for Rn.  We do however accept this case for store
      // instructions.
      if (bW == 1 && bL == 1 && ((1 << rN) & regList) > 0)
         goto after_load_store_multiple;

      /* Now, we can't do a conditional load or store, since that very
         likely will generate an exception.  So we have to take a side
         exit at this point if the condition is false. */
      if (condT != IRTemp_INVALID) {
         mk_skip_over_A32_if_cond_is_false( condT );
         condT = IRTemp_INVALID;
      }

      /* Ok, now we're unconditional.  Generate the IR. */
      mk_ldm_stm( True/*arm*/, rN, bINC, bBEFORE, bW, bL, regList );

      DIP("%sm%c%c%s r%u%s, {0x%04x}\n",
          bL == 1 ? "ld" : "st", bINC ? 'i' : 'd', bBEFORE ? 'b' : 'a',
          nCC(INSN_COND),
          rN, bW ? "!" : "", regList);

      goto decode_success;
   }

  after_load_store_multiple:

   /* --------------------- Control flow --------------------- */
   // B, BL (Branch, or Branch-and-Link, to immediate offset)
   //
   if (BITS8(1,0,1,0,0,0,0,0) == (INSN(27,20) & BITS8(1,1,1,0,0,0,0,0))) {
      UInt link   = (insn >> 24) & 1;
      UInt uimm24 = insn & ((1<<24)-1);
      Int  simm24 = (Int)uimm24;
      UInt dst    = guest_R15_curr_instr_notENC + 8
                    + (((simm24 << 8) >> 8) << 2);
      IRJumpKind jk = link ? Ijk_Call : Ijk_Boring;
      if (link) {
         putIRegA(14, mkU32(guest_R15_curr_instr_notENC + 4),
                      condT, Ijk_Boring);
      }
      if (condT == IRTemp_INVALID) {
         /* unconditional transfer to 'dst'.  See if we can simply
            continue tracing at the destination. */
         if (resteerOkFn( callback_opaque, (Addr64)dst )) {
            /* yes */
            dres.whatNext   = Dis_ResteerU;
            dres.continueAt = (Addr64)dst;
         } else {
            /* no; terminate the SB at this point. */
            irsb->next     = mkU32(dst);
            irsb->jumpkind = jk;
            dres.whatNext  = Dis_StopHere;
         }
         DIP("b%s 0x%x\n", link ? "l" : "", dst);
      } else {
         /* conditional transfer to 'dst' */
         HChar* comment = "";

         /* First see if we can do some speculative chasing into one
            arm or the other.  Be conservative and only chase if
            !link, that is, this is a normal conditional branch to a
            known destination. */
         if (!link
             && resteerCisOk
             && vex_control.guest_chase_cond
             && dst < guest_R15_curr_instr_notENC
             && resteerOkFn( callback_opaque, (Addr64)(Addr32)dst) ) {
            /* Speculation: assume this backward branch is taken.  So
               we need to emit a side-exit to the insn following this
               one, on the negation of the condition, and continue at
               the branch target address (dst). */
            stmt( IRStmt_Exit( unop(Iop_Not1,
                                    unop(Iop_32to1, mkexpr(condT))),
                               Ijk_Boring,
                               IRConst_U32(guest_R15_curr_instr_notENC+4) ));
            dres.whatNext   = Dis_ResteerC;
            dres.continueAt = (Addr64)(Addr32)dst;
            comment = "(assumed taken)";
         }
         else
         if (!link
             && resteerCisOk
             && vex_control.guest_chase_cond
             && dst >= guest_R15_curr_instr_notENC
             && resteerOkFn( callback_opaque, 
                             (Addr64)(Addr32)
                                     (guest_R15_curr_instr_notENC+4)) ) {
            /* Speculation: assume this forward branch is not taken.
               So we need to emit a side-exit to dst (the dest) and
               continue disassembling at the insn immediately
               following this one. */
            stmt( IRStmt_Exit( unop(Iop_32to1, mkexpr(condT)),
                               Ijk_Boring,
                               IRConst_U32(dst) ));
            dres.whatNext   = Dis_ResteerC;
            dres.continueAt = (Addr64)(Addr32)
                                      (guest_R15_curr_instr_notENC+4);
            comment = "(assumed not taken)";
         }
         else {
            /* Conservative default translation - end the block at
               this point. */
            stmt( IRStmt_Exit( unop(Iop_32to1, mkexpr(condT)),
                               jk, IRConst_U32(dst) ));
            irsb->next     = mkU32(guest_R15_curr_instr_notENC + 4);
            irsb->jumpkind = jk;
            dres.whatNext  = Dis_StopHere;
         }
         DIP("b%s%s 0x%x %s\n", link ? "l" : "", nCC(INSN_COND),
             dst, comment);
      }
      goto decode_success;
   }

   // B, BL (Branch, or Branch-and-Link, to a register)
   // NB: interworking branch
   if (INSN(27,20) == BITS8(0,0,0,1,0,0,1,0)
       && INSN(19,12) == BITS8(1,1,1,1,1,1,1,1)
       && (INSN(11,4) == BITS8(1,1,1,1,0,0,1,1)
           || INSN(11,4) == BITS8(1,1,1,1,0,0,0,1))) {
      IRExpr* dst;
      UInt    link = (INSN(11,4) >> 1) & 1;
      UInt    rM   = INSN(3,0);
      // we don't decode the case (link && rM == 15), as that's
      // Unpredictable.
      if (!(link && rM == 15)) {
         if (condT != IRTemp_INVALID) {
            mk_skip_over_A32_if_cond_is_false( condT );
         }
         // rM contains an interworking address exactly as we require
         // (with continuation CPSR.T in bit 0), so we can use it
         // as-is, with no masking.
         dst = getIRegA(rM);
         if (link) {
            putIRegA( 14, mkU32(guest_R15_curr_instr_notENC + 4),
                      IRTemp_INVALID/*because AL*/, Ijk_Boring );
         }
         irsb->next     = dst;
         irsb->jumpkind = link ? Ijk_Call
                               : (rM == 14 ? Ijk_Ret : Ijk_Boring);
         dres.whatNext  = Dis_StopHere;
         if (condT == IRTemp_INVALID) {
            DIP("b%sx r%u\n", link ? "l" : "", rM);
         } else {
            DIP("b%sx%s r%u\n", link ? "l" : "", nCC(INSN_COND), rM);
         }
         goto decode_success;
      }
      /* else: (link && rM == 15): just fall through */
   }

   /* --- NB: ARM interworking branches are in NV space, hence
      are handled elsewhere by decode_NV_instruction.
      ---
   */

   /* --------------------- Clz --------------------- */
   // CLZ
   if (INSN(27,20) == BITS8(0,0,0,1,0,1,1,0)
       && INSN(19,16) == BITS4(1,1,1,1)
       && INSN(11,4) == BITS8(1,1,1,1,0,0,0,1)) {
      UInt rD = INSN(15,12);
      UInt rM = INSN(3,0);
      IRTemp arg = newTemp(Ity_I32);
      IRTemp res = newTemp(Ity_I32);
      assign(arg, getIRegA(rM));
      assign(res, IRExpr_Mux0X(
                     unop(Iop_1Uto8,binop(Iop_CmpEQ32, mkexpr(arg),
                                                       mkU32(0))),
                     unop(Iop_Clz32, mkexpr(arg)),
                     mkU32(32)
            ));
      putIRegA(rD, mkexpr(res), condT, Ijk_Boring);
      DIP("clz%s r%u, r%u\n", nCC(INSN_COND), rD, rM);
      goto decode_success;
   }

   /* --------------------- Mul etc --------------------- */
   // MUL
   if (BITS8(0,0,0,0,0,0,0,0) == (INSN(27,20) & BITS8(1,1,1,1,1,1,1,0))
       && INSN(15,12) == BITS4(0,0,0,0)
       && INSN(7,4) == BITS4(1,0,0,1)) {
      UInt bitS = (insn >> 20) & 1; /* 20:20 */
      UInt rD = INSN(19,16);
      UInt rS = INSN(11,8);
      UInt rM = INSN(3,0);
      if (rD == 15 || rM == 15 || rS == 15) {
         /* Unpredictable; don't decode; fall through */
      } else {
         IRTemp argL = newTemp(Ity_I32);
         IRTemp argR = newTemp(Ity_I32);
         IRTemp res  = newTemp(Ity_I32);
         IRTemp oldC = IRTemp_INVALID;
         IRTemp oldV = IRTemp_INVALID;
         assign( argL, getIRegA(rM));
         assign( argR, getIRegA(rS));
         assign( res, binop(Iop_Mul32, mkexpr(argL), mkexpr(argR)) );
         if (bitS) {
            oldC = newTemp(Ity_I32);
            assign(oldC, mk_armg_calculate_flag_c());
            oldV = newTemp(Ity_I32);
            assign(oldV, mk_armg_calculate_flag_v());
         }
         // now update guest state
         putIRegA( rD, mkexpr(res), condT, Ijk_Boring );
         if (bitS) {
            IRTemp pair = newTemp(Ity_I32);
            assign( pair, binop(Iop_Or32,
                                binop(Iop_Shl32, mkexpr(oldC), mkU8(1)),
                                mkexpr(oldV)) );
            setFlags_D1_ND( ARMG_CC_OP_MUL, res, pair, condT );
         }
         DIP("mul%c%s r%u, r%u, r%u\n",
             bitS ? 's' : ' ', nCC(INSN_COND), rD, rM, rS);
         goto decode_success;
      }
      /* fall through */
   }

   // MLA, MLS
   if (BITS8(0,0,0,0,0,0,1,0) == (INSN(27,20) & BITS8(1,1,1,1,1,0,1,0))
       && INSN(7,4) == BITS4(1,0,0,1)) {
      UInt bitS  = (insn >> 20) & 1; /* 20:20 */
      UInt isMLS = (insn >> 22) & 1; /* 22:22 */
      UInt rD = INSN(19,16);
      UInt rN = INSN(15,12);
      UInt rS = INSN(11,8);
      UInt rM = INSN(3,0);
      if (bitS == 1 && isMLS == 1) {
         /* This isn't allowed (MLS that sets flags).  don't decode;
            fall through */
      }
      else
      if (rD == 15 || rM == 15 || rS == 15 || rN == 15) {
         /* Unpredictable; don't decode; fall through */
      } else {
         IRTemp argL = newTemp(Ity_I32);
         IRTemp argR = newTemp(Ity_I32);
         IRTemp argP = newTemp(Ity_I32);
         IRTemp res  = newTemp(Ity_I32);
         IRTemp oldC = IRTemp_INVALID;
         IRTemp oldV = IRTemp_INVALID;
         assign( argL, getIRegA(rM));
         assign( argR, getIRegA(rS));
         assign( argP, getIRegA(rN));
         assign( res, binop(isMLS ? Iop_Sub32 : Iop_Add32,
                            mkexpr(argP),
                            binop(Iop_Mul32, mkexpr(argL), mkexpr(argR)) ));
         if (bitS) {
            vassert(!isMLS); // guaranteed above
            oldC = newTemp(Ity_I32);
            assign(oldC, mk_armg_calculate_flag_c());
            oldV = newTemp(Ity_I32);
            assign(oldV, mk_armg_calculate_flag_v());
         }
         // now update guest state
         putIRegA( rD, mkexpr(res), condT, Ijk_Boring );
         if (bitS) {
            IRTemp pair = newTemp(Ity_I32);
            assign( pair, binop(Iop_Or32,
                                binop(Iop_Shl32, mkexpr(oldC), mkU8(1)),
                                mkexpr(oldV)) );
            setFlags_D1_ND( ARMG_CC_OP_MUL, res, pair, condT );
         }
         DIP("ml%c%c%s r%u, r%u, r%u, r%u\n",
             isMLS ? 's' : 'a', bitS ? 's' : ' ', nCC(INSN_COND), rD, rM, rS, rN);
         goto decode_success;
      }
      /* fall through */
   }

   // SMULL, UMULL
   if (BITS8(0,0,0,0,1,0,0,0) == (INSN(27,20) & BITS8(1,1,1,1,1,0,1,0))
       && INSN(7,4) == BITS4(1,0,0,1)) {
      UInt bitS = (insn >> 20) & 1; /* 20:20 */
      UInt rDhi = INSN(19,16);
      UInt rDlo = INSN(15,12);
      UInt rS   = INSN(11,8);
      UInt rM   = INSN(3,0);
      UInt isS  = (INSN(27,20) >> 2) & 1; /* 22:22 */
      if (rDhi == 15 || rDlo == 15 || rM == 15 || rS == 15 || rDhi == rDlo)  {
         /* Unpredictable; don't decode; fall through */
      } else {
         IRTemp argL  = newTemp(Ity_I32);
         IRTemp argR  = newTemp(Ity_I32);
         IRTemp res   = newTemp(Ity_I64);
         IRTemp resHi = newTemp(Ity_I32);
         IRTemp resLo = newTemp(Ity_I32);
         IRTemp oldC  = IRTemp_INVALID;
         IRTemp oldV  = IRTemp_INVALID;
         IROp   mulOp = isS ? Iop_MullS32 : Iop_MullU32;
         assign( argL, getIRegA(rM));
         assign( argR, getIRegA(rS));
         assign( res, binop(mulOp, mkexpr(argL), mkexpr(argR)) );
         assign( resHi, unop(Iop_64HIto32, mkexpr(res)) );
         assign( resLo, unop(Iop_64to32, mkexpr(res)) );
         if (bitS) {
            oldC = newTemp(Ity_I32);
            assign(oldC, mk_armg_calculate_flag_c());
            oldV = newTemp(Ity_I32);
            assign(oldV, mk_armg_calculate_flag_v());
         }
         // now update guest state
         putIRegA( rDhi, mkexpr(resHi), condT, Ijk_Boring );
         putIRegA( rDlo, mkexpr(resLo), condT, Ijk_Boring );
         if (bitS) {
            IRTemp pair = newTemp(Ity_I32);
            assign( pair, binop(Iop_Or32,
                                binop(Iop_Shl32, mkexpr(oldC), mkU8(1)),
                                mkexpr(oldV)) );
            setFlags_D1_D2_ND( ARMG_CC_OP_MULL, resLo, resHi, pair, condT );
         }
         DIP("%cmull%c%s r%u, r%u, r%u, r%u\n",
             isS ? 's' : 'u', bitS ? 's' : ' ',
             nCC(INSN_COND), rDlo, rDhi, rM, rS);
         goto decode_success;
      }
      /* fall through */
   }

   // SMLAL, UMLAL
   if (BITS8(0,0,0,0,1,0,1,0) == (INSN(27,20) & BITS8(1,1,1,1,1,0,1,0))
       && INSN(7,4) == BITS4(1,0,0,1)) {
      UInt bitS = (insn >> 20) & 1; /* 20:20 */
      UInt rDhi = INSN(19,16);
      UInt rDlo = INSN(15,12);
      UInt rS   = INSN(11,8);
      UInt rM   = INSN(3,0);
      UInt isS  = (INSN(27,20) >> 2) & 1; /* 22:22 */
      if (rDhi == 15 || rDlo == 15 || rM == 15 || rS == 15 || rDhi == rDlo)  {
         /* Unpredictable; don't decode; fall through */
      } else {
         IRTemp argL  = newTemp(Ity_I32);
         IRTemp argR  = newTemp(Ity_I32);
         IRTemp old   = newTemp(Ity_I64);
         IRTemp res   = newTemp(Ity_I64);
         IRTemp resHi = newTemp(Ity_I32);
         IRTemp resLo = newTemp(Ity_I32);
         IRTemp oldC  = IRTemp_INVALID;
         IRTemp oldV  = IRTemp_INVALID;
         IROp   mulOp = isS ? Iop_MullS32 : Iop_MullU32;
         assign( argL, getIRegA(rM));
         assign( argR, getIRegA(rS));
         assign( old, binop(Iop_32HLto64, getIRegA(rDhi), getIRegA(rDlo)) );
         assign( res, binop(Iop_Add64,
                            mkexpr(old),
                            binop(mulOp, mkexpr(argL), mkexpr(argR))) );
         assign( resHi, unop(Iop_64HIto32, mkexpr(res)) );
         assign( resLo, unop(Iop_64to32, mkexpr(res)) );
         if (bitS) {
            oldC = newTemp(Ity_I32);
            assign(oldC, mk_armg_calculate_flag_c());
            oldV = newTemp(Ity_I32);
            assign(oldV, mk_armg_calculate_flag_v());
         }
         // now update guest state
         putIRegA( rDhi, mkexpr(resHi), condT, Ijk_Boring );
         putIRegA( rDlo, mkexpr(resLo), condT, Ijk_Boring );
         if (bitS) {
            IRTemp pair = newTemp(Ity_I32);
            assign( pair, binop(Iop_Or32,
                                binop(Iop_Shl32, mkexpr(oldC), mkU8(1)),
                                mkexpr(oldV)) );
            setFlags_D1_D2_ND( ARMG_CC_OP_MULL, resLo, resHi, pair, condT );
         }
         DIP("%cmlal%c%s r%u, r%u, r%u, r%u\n",
             isS ? 's' : 'u', bitS ? 's' : ' ', nCC(INSN_COND),
             rDlo, rDhi, rM, rS);
         goto decode_success;
      }
      /* fall through */
   }

   /* --------------------- Msr etc --------------------- */

   // MSR cpsr_f, #imm8  (immediate form, flags only)
   if (BITS8(0,0,1,1,0,0,1,0) == (INSN(27,20) & BITS8(1,1,1,1,1,0,1,1))
       && INSN(15,12) == BITS4(1,1,1,1)) {
      UInt bitR = (insn >> 22) & 1;
      if (bitR == 0 && INSN(19,16) == BITS4(1,0,0,0)) {
         UInt   imm = (INSN(11,0) >> 0) & 0xFF;
         UInt   rot = 2 * ((INSN(11,0) >> 8) & 0xF);
         IRTemp immT = newTemp(Ity_I32);
         vassert(rot <= 30);
         imm = ROR32(imm, rot);
         imm &= 0xFF000000;
         imm &= (ARMG_CC_MASK_N | ARMG_CC_MASK_Z 
                 | ARMG_CC_MASK_V | ARMG_CC_MASK_C);
         assign( immT, mkU32(imm & 0xF0000000) );
         setFlags_D1(ARMG_CC_OP_COPY, immT, condT);
         DIP("msr%s cpsr_f, #0x%08x\n", nCC(INSN_COND), imm);
         goto decode_success;
      }
      /* fall through */
   }

   // MSR cpsr_f, rM  (flags only)
   if (BITS8(0,0,0,1,0,0,1,0) == (INSN(27,20) & BITS8(1,1,1,1,1,0,1,1))
       && INSN(15,12) == BITS4(1,1,1,1)) {
      UInt bitR = (insn >> 22) & 1;
      if (bitR == 0 && INSN(19,16) == BITS4(1,0,0,0)
          && INSN(11,4) == BITS8(0,0,0,0,0,0,0,0)
          && INSN(3,0) != 15) {
         UInt rM = INSN(3,0);
         IRTemp immT = newTemp(Ity_I32);
         assign(immT, binop(Iop_And32, getIRegA(rM), mkU32(0xF0000000)) );
         setFlags_D1(ARMG_CC_OP_COPY, immT, condT);
         DIP("msr%s cpsr_f, r%u\n", nCC(INSN_COND), rM);
         goto decode_success;
      }
      /* fall through */
   }

   // MRS rD, cpsr
   if (BITS8(0,0,0,1,0,0,0,0) == (INSN(27,20) & BITS8(1,1,1,1,1,0,1,1))
       && INSN(19,16) == BITS4(1,1,1,1)
       && INSN(11,0) == 0) {
      UInt bitR = (insn >> 22) & 1;
      UInt rD   = INSN(15,12);
      if (bitR == 0 && rD != 15) {
         IRTemp res = newTemp(Ity_I32);
         assign( res, mk_armg_calculate_flags_nzcv() );
         putIRegA( rD, mkexpr(res), condT, Ijk_Boring );
         DIP("mrs%s r%u, cpsr\n", nCC(INSN_COND), rD);
         goto decode_success;
      }
      /* fall through */
   }

   /* --------------------- Svc --------------------- */
   if (BITS8(1,1,1,1,0,0,0,0) == (INSN(27,20) & BITS8(1,1,1,1,0,0,0,0))) {
      UInt imm24 = (insn >> 0) & 0xFFFFFF;
      if (imm24 == 0) {
         /* A syscall.  We can't do this conditionally, hence: */
         if (condT != IRTemp_INVALID) {
            mk_skip_over_A32_if_cond_is_false( condT );
         }
         // AL after here
         irsb->next     = mkU32( guest_R15_curr_instr_notENC + 4 );
         irsb->jumpkind = Ijk_Sys_syscall;
         dres.whatNext  = Dis_StopHere;
         DIP("svc%s #0x%08x\n", nCC(INSN_COND), imm24);
         goto decode_success;
      }
      /* fall through */
   }

   /* ------------------------ swp ------------------------ */

   // SWP, SWPB
   if (BITS8(0,0,0,1,0,0,0,0) == (INSN(27,20) & BITS8(1,1,1,1,1,0,1,1))
       && BITS4(0,0,0,0) == INSN(11,8)
       && BITS4(1,0,0,1) == INSN(7,4)) {
      UInt   rN   = INSN(19,16);
      UInt   rD   = INSN(15,12);
      UInt   rM   = INSN(3,0);
      IRTemp tRn  = newTemp(Ity_I32);
      IRTemp tNew = newTemp(Ity_I32);
      IRTemp tOld = IRTemp_INVALID;
      IRTemp tSC1 = newTemp(Ity_I1);
      UInt   isB  = (insn >> 22) & 1;

      if (rD == 15 || rN == 15 || rM == 15 || rN == rM || rN == rD) {
         /* undecodable; fall through */
      } else {
         /* make unconditional */
         if (condT != IRTemp_INVALID) {
            mk_skip_over_A32_if_cond_is_false( condT );
            condT = IRTemp_INVALID;
         }
         /* Ok, now we're unconditional.  Generate a LL-SC loop. */
         assign(tRn, getIRegA(rN));
         assign(tNew, getIRegA(rM));
         if (isB) {
            /* swpb */
            tOld = newTemp(Ity_I8);
            stmt( IRStmt_LLSC(Iend_LE, tOld, mkexpr(tRn),
                              NULL/*=>isLL*/) );
            stmt( IRStmt_LLSC(Iend_LE, tSC1, mkexpr(tRn),
                              unop(Iop_32to8, mkexpr(tNew))) );
         } else {
            /* swp */
            tOld = newTemp(Ity_I32);
            stmt( IRStmt_LLSC(Iend_LE, tOld, mkexpr(tRn),
                              NULL/*=>isLL*/) );
            stmt( IRStmt_LLSC(Iend_LE, tSC1, mkexpr(tRn),
                              mkexpr(tNew)) );
         }
         stmt( IRStmt_Exit(unop(Iop_Not1, mkexpr(tSC1)),
                           /*Ijk_NoRedir*/Ijk_Boring,
                           IRConst_U32(guest_R15_curr_instr_notENC)) );
         putIRegA(rD, isB ? unop(Iop_8Uto32, mkexpr(tOld)) : mkexpr(tOld),
                      IRTemp_INVALID, Ijk_Boring);
         DIP("swp%s%s r%u, r%u, [r%u]\n",
             isB ? "b" : "", nCC(INSN_COND), rD, rM, rN);
         goto decode_success;
      }
      /* fall through */
   }

   /* ----------------------------------------------------------- */
   /* -- VFP instructions -- double precision (mostly)         -- */
   /* ----------------------------------------------------------- */

   /* --------------------- fldmx, fstmx --------------------- */
   /*
                                 31   27   23   19 15 11   7   0
                                         P U WL
      C4-100, C5-26  1  FSTMX    cond 1100 1000 Rn Dd 1011 offset
      C4-100, C5-28  2  FSTMIAX  cond 1100 1010 Rn Dd 1011 offset
      C4-100, C5-30  3  FSTMDBX  cond 1101 0010 Rn Dd 1011 offset

      C4-42, C5-26   1  FLDMX    cond 1100 1001 Rn Dd 1011 offset
      C4-42, C5-28   2  FLDMIAX  cond 1100 1011 Rn Dd 1011 offset
      C4-42, C5-30   3  FLDMDBX  cond 1101 0011 Rn Dd 1011 offset

      Regs transferred: Dd .. D(d + (offset-3)/2)
      offset must be odd, must not imply a reg > 15
      IA/DB: Rn is changed by (4 + 8 x # regs transferred)

      case coding:
         1  at-Rn   (access at Rn)
         2  ia-Rn   (access at Rn, then Rn += 4+8n)
         3  db-Rn   (Rn -= 4+8n,   then access at Rn)
   */
   if (BITS8(1,1,0,0,0,0,0,0) == (INSN(27,20) & BITS8(1,1,1,0,0,1,0,0))
       && INSN(11,8) == BITS4(1,0,1,1)) {
      UInt bP     = (insn >> 24) & 1;
      UInt bU     = (insn >> 23) & 1;
      UInt bW     = (insn >> 21) & 1;
      UInt bL     = (insn >> 20) & 1;
      UInt offset = (insn >> 0) & 0xFF;
      UInt rN     = INSN(19,16);
      UInt dD     = INSN(15,12);
      UInt nRegs  = (offset - 1) / 2;
      Int  i;

      /**/ if (bP == 0 && bU == 1 && bW == 0) {
         vassert(0); //ATC
         summary = 1;
      }
      else if (bP == 0 && bU == 1 && bW == 1) {
         summary = 2;
      }
      else if (bP == 1 && bU == 0 && bW == 1) {
         summary = 3;
      }
      else goto after_vfp_fldmx_fstmx;

      /* no writebacks to r15 allowed */
      if (rN == 15 && (summary == 2 || summary == 3))
         goto after_vfp_fldmx_fstmx;

      /* offset must be odd, and specify at least one register */
      if (0 == (offset & 1) || offset < 3)
         goto after_vfp_fldmx_fstmx;

      /* can't transfer regs after D15 */
      if (dD + nRegs - 1 >= 16)
         goto after_vfp_fldmx_fstmx;

      /* Now, we can't do a conditional load or store, since that very
         likely will generate an exception.  So we have to take a side
         exit at this point if the condition is false. */
      if (condT != IRTemp_INVALID) {
         mk_skip_over_A32_if_cond_is_false( condT );
         condT = IRTemp_INVALID;
      }
      /* Ok, now we're unconditional.  Do the load or store. */

      /* get the old Rn value */
      IRTemp rnT = newTemp(Ity_I32);
      assign(rnT, getIRegA(rN));

      /* make a new value for Rn, post-insn */
      IRTemp rnTnew = IRTemp_INVALID;
      if (summary == 2 || summary == 3) {
         rnTnew = newTemp(Ity_I32);
         assign(rnTnew, binop(summary == 2 ? Iop_Add32 : Iop_Sub32,
                              mkexpr(rnT),
                              mkU32(4 + 8 * nRegs)));
      }

      /* decide on the base transfer address */
      IRTemp taT = newTemp(Ity_I32);
      assign(taT,  summary == 3 ? mkexpr(rnTnew) : mkexpr(rnT));

      /* update Rn if necessary -- in case 3, we're moving it down, so
         update before any memory reference, in order to keep Memcheck
         and V's stack-extending logic (on linux) happy */
      if (summary == 3)
         putIRegA(rN, mkexpr(rnTnew), IRTemp_INVALID, Ijk_Boring);

      /* generate the transfers */
      for (i = 0; i < nRegs; i++) {
         IRExpr* addr = binop(Iop_Add32, mkexpr(taT), mkU32(8*i));
         if (bL) {
            putDReg(dD + i, loadLE(Ity_F64, addr), IRTemp_INVALID);
         } else {
            storeLE(addr, getDReg(dD + i));
         }
      }

      /* update Rn if necessary -- in case 2, we're moving it up, so
         update after any memory reference, in order to keep Memcheck
         and V's stack-extending logic (on linux) happy */
      if (summary == 2)
         putIRegA(rN, mkexpr(rnTnew), IRTemp_INVALID, Ijk_Boring);

      HChar* nm = bL==1 ? "ld" : "st";
      switch (summary) {
         case 1:  DIP("f%smx%s r%u, {d%u-d%u}\n", 
                      nm, nCC(INSN_COND), rN, dD, dD + nRegs - 1);
                  break;
         case 2:  DIP("f%smiax%s r%u!, {d%u-d%u}\n", 
                      nm, nCC(INSN_COND), rN, dD, dD + nRegs - 1);
                  break;
         case 3:  DIP("f%smdbx%s r%u!, {d%u-d%u}\n", 
                      nm, nCC(INSN_COND), rN, dD, dD + nRegs - 1);
                  break;
         default: vassert(0);
      }


      goto decode_success;
      /* FIXME alignment constraints? */
   }

  after_vfp_fldmx_fstmx:

   /* --------------------- fldmd, fstmd --------------------- */
   /*
                                 31   27   23   19 15 11   7   0
                                         P U WL
      C4-96, C5-26   1  FSTMD    cond 1100 1000 Rn Dd 1011 offset
      C4-96, C5-28   2  FSTMDIA  cond 1100 1010 Rn Dd 1011 offset
      C4-96, C5-30   3  FSTMDDB  cond 1101 0010 Rn Dd 1011 offset

      C4-38, C5-26   1  FLDMD    cond 1100 1001 Rn Dd 1011 offset
      C4-38, C5-28   2  FLDMIAD  cond 1100 1011 Rn Dd 1011 offset
      C4-38, C5-30   3  FLDMDBD  cond 1101 0011 Rn Dd 1011 offset

      Regs transferred: Dd .. D(d + (offset-2)/2)
      offset must be even, must not imply a reg > 15
      IA/DB: Rn is changed by (8 x # regs transferred)

      case coding:
         1  at-Rn   (access at Rn)
         2  ia-Rn   (access at Rn, then Rn += 8n)
         3  db-Rn   (Rn -= 8n,     then access at Rn)
   */
   if (BITS8(1,1,0,0,0,0,0,0) == (INSN(27,20) & BITS8(1,1,1,0,0,1,0,0))
       && INSN(11,8) == BITS4(1,0,1,1)) {
      UInt bP     = (insn >> 24) & 1;
      UInt bU     = (insn >> 23) & 1;
      UInt bW     = (insn >> 21) & 1;
      UInt bL     = (insn >> 20) & 1;
      UInt offset = (insn >> 0) & 0xFF;
      UInt rN     = INSN(19,16);
      UInt dD     = INSN(15,12);
      UInt nRegs  = offset / 2;
      Int  i;

      /**/ if (bP == 0 && bU == 1 && bW == 0) {
         vassert(0); //ATC
         summary = 1;
      }
      else if (bP == 0 && bU == 1 && bW == 1) {
         summary = 2;
      }
      else if (bP == 1 && bU == 0 && bW == 1) {
         summary = 3;
      }
      else goto after_vfp_fldmd_fstmd;

      /* no writebacks to r15 allowed */
      if (rN == 15 && (summary == 2 || summary == 3))
         goto after_vfp_fldmd_fstmd;

      /* offset must be even, and specify at least one register */
      if (1 == (offset & 1) || offset < 2)
         goto after_vfp_fldmd_fstmd;

      /* can't transfer regs after D15 */
      if (dD + nRegs - 1 >= 16)
         goto after_vfp_fldmd_fstmd;

      /* Now, we can't do a conditional load or store, since that very
         likely will generate an exception.  So we have to take a side
         exit at this point if the condition is false. */
      if (condT != IRTemp_INVALID) {
         mk_skip_over_A32_if_cond_is_false( condT );
         condT = IRTemp_INVALID;
      }
      /* Ok, now we're unconditional.  Do the load or store. */

      /* get the old Rn value */
      IRTemp rnT = newTemp(Ity_I32);
      assign(rnT, getIRegA(rN));

      /* make a new value for Rn, post-insn */
      IRTemp rnTnew = IRTemp_INVALID;
      if (summary == 2 || summary == 3) {
         rnTnew = newTemp(Ity_I32);
         assign(rnTnew, binop(summary == 2 ? Iop_Add32 : Iop_Sub32,
                              mkexpr(rnT),
                              mkU32(8 * nRegs)));
      }

      /* decide on the base transfer address */
      IRTemp taT = newTemp(Ity_I32);
      assign(taT, summary == 3 ? mkexpr(rnTnew) : mkexpr(rnT));

      /* update Rn if necessary -- in case 3, we're moving it down, so
         update before any memory reference, in order to keep Memcheck
         and V's stack-extending logic (on linux) happy */
      if (summary == 3)
         putIRegA(rN, mkexpr(rnTnew), IRTemp_INVALID, Ijk_Boring);

      /* generate the transfers */
      for (i = 0; i < nRegs; i++) {
         IRExpr* addr = binop(Iop_Add32, mkexpr(taT), mkU32(8*i));
         if (bL) {
            putDReg(dD + i, loadLE(Ity_F64, addr), IRTemp_INVALID);
         } else {
            storeLE(addr, getDReg(dD + i));
         }
      }

      /* update Rn if necessary -- in case 2, we're moving it up, so
         update after any memory reference, in order to keep Memcheck
         and V's stack-extending logic (on linux) happy */
      if (summary == 2)
         putIRegA(rN, mkexpr(rnTnew), IRTemp_INVALID, Ijk_Boring);

      HChar* nm = bL==1 ? "ld" : "st";
      switch (summary) {
         case 1:  DIP("f%smd%s r%u, {d%u-d%u}\n", 
                      nm, nCC(INSN_COND), rN, dD, dD + nRegs - 1);
                  break;
         case 2:  DIP("f%smiad%s r%u!, {d%u-d%u}\n", 
                      nm, nCC(INSN_COND), rN, dD, dD + nRegs - 1);
                  break;
         case 3:  DIP("f%smdbd%s r%u!, {d%u-d%u}\n", 
                      nm, nCC(INSN_COND), rN, dD, dD + nRegs - 1);
                  break;
         default: vassert(0);
      }

      goto decode_success;
      /* FIXME alignment constraints? */
   }

  after_vfp_fldmd_fstmd:

   /* ------------------- fmrx, fmxr ------------------- */
   if (BITS8(1,1,1,0,1,1,1,1) == INSN(27,20)
       && BITS4(1,0,1,0) == INSN(11,8)
       && BITS8(0,0,0,1,0,0,0,0) == (insn & 0xFF)) {
      UInt rD  = INSN(15,12);
      UInt reg = INSN(19,16);
      if (reg == BITS4(0,0,0,1)) {
         if (rD == 15) {
            IRTemp nzcvT = newTemp(Ity_I32);
            /* When rD is 15, we are copying the top 4 bits of FPSCR
               into CPSR.  That is, set the flags thunk to COPY and
               install FPSCR[31:28] as the value to copy. */
            assign(nzcvT, binop(Iop_And32,
                                IRExpr_Get(OFFB_FPSCR, Ity_I32),
                                mkU32(0xF0000000)));
            setFlags_D1(ARMG_CC_OP_COPY, nzcvT, condT);
            DIP("fmstat%s\n", nCC(INSN_COND));
         } else {
            /* Otherwise, merely transfer FPSCR to r0 .. r14. */
            putIRegA(rD, IRExpr_Get(OFFB_FPSCR, Ity_I32), 
                         condT, Ijk_Boring);
            DIP("fmrx%s r%u, fpscr\n", nCC(INSN_COND), rD);
         }
         goto decode_success;
      }
      /* fall through */
   }

   if (BITS8(1,1,1,0,1,1,1,0) == INSN(27,20)
       && BITS4(1,0,1,0) == INSN(11,8)
       && BITS8(0,0,0,1,0,0,0,0) == (insn & 0xFF)) {
      UInt rD  = INSN(15,12);
      UInt reg = INSN(19,16);
      if (reg == BITS4(0,0,0,1)) {
         putMiscReg32(OFFB_FPSCR, getIRegA(rD), condT);
         DIP("fmxr%s fpscr, r%u\n", nCC(INSN_COND), rD);
         goto decode_success;
      }
      /* fall through */
   }

   /* --------------------- vmov --------------------- */
   // VMOV dM, rD, rN
   if (0x0C400B10 == (insn & 0x0FF00FF0)) {
      UInt dM = INSN(3,0);
      UInt rD = INSN(15,12); /* lo32 */
      UInt rN = INSN(19,16); /* hi32 */
      if (rD == 15 || rN == 15) {
         /* fall through */
      } else {
         putDReg(dM,
                 unop(Iop_ReinterpI64asF64,
                      binop(Iop_32HLto64, getIRegA(rN), getIRegA(rD))),
                 condT);
         DIP("vmov%s d%u, r%u, r%u\n", nCC(INSN_COND), dM, rD, rN);
         goto decode_success;
      }
      /* fall through */
   }

   // VMOV rD, rN, dM
   if (0x0C500B10 == (insn & 0x0FF00FF0)) {
      UInt dM = INSN(3,0);
      UInt rD = INSN(15,12); /* lo32 */
      UInt rN = INSN(19,16); /* hi32 */
      if (rD == 15 || rN == 15 || rD == rN) {
         /* fall through */
      } else {
         IRTemp i64 = newTemp(Ity_I64);
         assign(i64, unop(Iop_ReinterpF64asI64, getDReg(dM)));
         putIRegA(rN, unop(Iop_64HIto32, mkexpr(i64)), condT, Ijk_Boring);
         putIRegA(rD, unop(Iop_64to32,   mkexpr(i64)), condT, Ijk_Boring);
         DIP("vmov%s r%u, r%u, d%u\n", nCC(INSN_COND), rD, rN, dM);
         goto decode_success;
      }
      /* fall through */
   }

   /* --------------------- f{ld,st}d --------------------- */
   // FLDD, FSTD
   if (BITS8(1,1,0,1,0,0,0,0) == (INSN(27,20) & BITS8(1,1,1,1,0,1,1,0))
       && BITS4(1,0,1,1) == INSN(11,8)) {
      UInt dD     = INSN(15,12);
      UInt rN     = INSN(19,16);
      UInt offset = (insn & 0xFF) << 2;
      UInt bU     = (insn >> 23) & 1; /* 1: +offset  0: -offset */
      UInt bL     = (insn >> 20) & 1; /* 1: load  0: store */
      /* make unconditional */
      if (condT != IRTemp_INVALID) {
         mk_skip_over_A32_if_cond_is_false( condT );
         condT = IRTemp_INVALID;
      }
      IRTemp ea = newTemp(Ity_I32);
      assign(ea, binop(bU ? Iop_Add32 : Iop_Sub32,
                       getIRegA(rN), mkU32(offset)));
      if (bL) {
         putDReg(dD, loadLE(Ity_F64,mkexpr(ea)), IRTemp_INVALID);
      } else {
         storeLE(mkexpr(ea), getDReg(dD));
      }
      DIP("f%sd%s d%u, [r%u, %c#%u]\n",
          bL ? "ld" : "st", nCC(INSN_COND), dD, rN,
          bU ? '+' : '-', offset);
      goto decode_success;
   }

   /* --------------------- dp insns (D) --------------------- */
   if (BITS8(1,1,1,0,0,0,0,0) == (INSN(27,20) & BITS8(1,1,1,1,0,1,0,0))
       && BITS4(1,0,1,1) == INSN(11,8)
       && BITS4(0,0,0,0) == (INSN(7,4) & BITS4(1,0,1,1))) {
      UInt    dM  = INSN(3,0);   /* argR */
      UInt    dD  = INSN(15,12); /* dst/acc */
      UInt    dN  = INSN(19,16); /* argL */
      UInt    bP  = (insn >> 23) & 1;
      UInt    bQ  = (insn >> 21) & 1;
      UInt    bR  = (insn >> 20) & 1;
      UInt    bS  = (insn >> 6) & 1;
      UInt    opc = (bP << 3) | (bQ << 2) | (bR << 1) | bS;
      IRExpr* rm  = get_FAKE_roundingmode(); /* XXXROUNDINGFIXME */
      switch (opc) {
         case BITS4(0,0,0,0): /* MAC: d + n * m */
            putDReg(dD, triop(Iop_AddF64, rm,
                              getDReg(dD),
                              triop(Iop_MulF64, rm, getDReg(dN),
                                                    getDReg(dM))),
                        condT);
            DIP("fmacd%s d%u, d%u, d%u\n", nCC(INSN_COND), dD, dN, dM);
            goto decode_success;
         case BITS4(0,0,0,1): /* NMAC: d - n * m */
            putDReg(dD, triop(Iop_SubF64, rm,
                              getDReg(dD),
                              triop(Iop_MulF64, rm, getDReg(dN),
                                                    getDReg(dM))),
                        condT);
            DIP("fnmacd%s d%u, d%u, d%u\n", nCC(INSN_COND), dD, dN, dM);
            goto decode_success;
         case BITS4(0,0,1,0): /* MSC: - d + n * m */
            putDReg(dD, triop(Iop_AddF64, rm,
                              unop(Iop_NegF64, getDReg(dD)),
                              triop(Iop_MulF64, rm, getDReg(dN),
                                                    getDReg(dM))),
                        condT);
            DIP("fmscd%s d%u, d%u, d%u\n", nCC(INSN_COND), dD, dN, dM);
            goto decode_success;
         case BITS4(0,0,1,1): /* NMSC: - d - n * m */
            putDReg(dD, triop(Iop_SubF64, rm,
                              unop(Iop_NegF64, getDReg(dD)),
                              triop(Iop_MulF64, rm, getDReg(dN),
                                                    getDReg(dM))),
                        condT);
            DIP("fnmscd%s d%u, d%u, d%u\n", nCC(INSN_COND), dD, dN, dM);
            goto decode_success;
         case BITS4(0,1,0,0): /* MUL: n * m */
            putDReg(dD, triop(Iop_MulF64, rm, getDReg(dN), getDReg(dM)),
                        condT);
            DIP("fmuld%s d%u, d%u, d%u\n", nCC(INSN_COND), dD, dN, dM);
            goto decode_success;
         case BITS4(0,1,0,1): /* NMUL: - n * m */
            putDReg(dD, unop(Iop_NegF64,
                             triop(Iop_MulF64, rm, getDReg(dN),
                                                   getDReg(dM))),
                    condT);
            DIP("fnmuld%s d%u, d%u, d%u\n", nCC(INSN_COND), dD, dN, dM);
            goto decode_success;
         case BITS4(0,1,1,0): /* ADD: n + m */
            putDReg(dD, triop(Iop_AddF64, rm, getDReg(dN), getDReg(dM)),
                        condT);
            DIP("faddd%s d%u, d%u, d%u\n", nCC(INSN_COND), dD, dN, dM);
            goto decode_success;
         case BITS4(0,1,1,1): /* SUB: n - m */
            putDReg(dD, triop(Iop_SubF64, rm, getDReg(dN), getDReg(dM)),
                        condT);
            DIP("fsubd%s d%u, d%u, d%u\n", nCC(INSN_COND), dD, dN, dM);
            goto decode_success;
         case BITS4(1,0,0,0): /* DIV: n / m */
            putDReg(dD, triop(Iop_DivF64, rm, getDReg(dN), getDReg(dM)),
                        condT);
            DIP("fdivd%s d%u, d%u, d%u\n", nCC(INSN_COND), dD, dN, dM);
            goto decode_success;
         default:
            break;
      }
   }

   /* --------------------- compares (D) --------------------- */
   /*          31   27   23   19   15 11   7    3
                 28   24   20   16 12    8    4    0 
      FCMPD    cond 1110 1011 0100 Dd 1011 0100 Dm
      FCMPED   cond 1110 1011 0100 Dd 1011 1100 Dm
      FCMPZD   cond 1110 1011 0101 Dd 1011 0100 0000
      FCMPZED  cond 1110 1011 0101 Dd 1011 1100 0000
                                 Z         N

      Z=0 Compare Dd vs Dm     and set FPSCR 31:28 accordingly
      Z=1 Compare Dd vs zero

      N=1 generates Invalid Operation exn if either arg is any kind of NaN
      N=0 generates Invalid Operation exn if either arg is a signalling NaN
      (Not that we pay any attention to N here)
   */
   if (BITS8(1,1,1,0,1,0,1,1) == INSN(27,20)
       && BITS4(0,1,0,0) == (INSN(19,16) & BITS4(1,1,1,0))
       && BITS4(1,0,1,1) == INSN(11,8)
       && BITS4(0,1,0,0) == (INSN(7,4) & BITS4(0,1,1,1))) {
      UInt bZ = (insn >> 16) & 1;
      UInt bN = (insn >> 7) & 1;
      UInt dD = INSN(15,12);
      UInt dM = INSN(3,0);
      if (bZ && INSN(3,0) != 0) {
         /* does not decode; fall through */
      } else {
         IRTemp argL = newTemp(Ity_F64);
         IRTemp argR = newTemp(Ity_F64);
         IRTemp irRes = newTemp(Ity_I32);
         assign(argL, getDReg(dD));
         assign(argR, bZ ? IRExpr_Const(IRConst_F64i(0)) : getDReg(dM));
         assign(irRes, binop(Iop_CmpF64, mkexpr(argL), mkexpr(argR)));

         IRTemp nzcv     = IRTemp_INVALID;
         IRTemp oldFPSCR = newTemp(Ity_I32);
         IRTemp newFPSCR = newTemp(Ity_I32);

         /* This is where the fun starts.  We have to convert 'irRes'
            from an IR-convention return result (IRCmpF64Result) to an
            ARM-encoded (N,Z,C,V) group.  The final result is in the
            bottom 4 bits of 'nzcv'. */
         /* Map compare result from IR to ARM(nzcv) */
         /*
            FP cmp result | IR   | ARM(nzcv)
            --------------------------------
            UN              0x45   0011
            LT              0x01   1000
            GT              0x00   0010
            EQ              0x40   0110
         */
         nzcv = mk_convert_IRCmpF64Result_to_NZCV(irRes);

         /* And update FPSCR accordingly */
         assign(oldFPSCR, IRExpr_Get(OFFB_FPSCR, Ity_I32));
         assign(newFPSCR, 
                binop(Iop_Or32, 
                      binop(Iop_And32, mkexpr(oldFPSCR), mkU32(0x0FFFFFFF)),
                      binop(Iop_Shl32, mkexpr(nzcv), mkU8(28))));

         putMiscReg32(OFFB_FPSCR, mkexpr(newFPSCR), condT);

         if (bZ) {
            DIP("fcmpz%sd%s d%u\n", bN ? "e" : "", nCC(INSN_COND), dD);
         } else {
            DIP("fcmp%sd%s d%u, d%u\n", bN ? "e" : "", nCC(INSN_COND), dD, dM);
         }
         goto decode_success;
      }
      /* fall through */
   }  

   /* --------------------- unary (D) --------------------- */
   if (BITS8(1,1,1,0,1,0,1,1) == INSN(27,20)
       && BITS4(0,0,0,0) == (INSN(19,16) & BITS4(1,1,1,0))
       && BITS4(1,0,1,1) == INSN(11,8)
       && BITS4(0,1,0,0) == (INSN(7,4) & BITS4(0,1,1,1))) {
      UInt dD  = INSN(15,12);
      UInt dM  = INSN(3,0);
      UInt b16 = (insn >> 16) & 1;
      UInt b7  = (insn >> 7) & 1;
      /**/ if (b16 == 0 && b7 == 0) {
         // FCPYD
         putDReg(dD, getDReg(dM), condT);
         DIP("fcpyd%s d%u, d%u\n", nCC(INSN_COND), dD, dM);
         goto decode_success;
      }
      else if (b16 == 0 && b7 == 1) {
         // FABSD
         putDReg(dD, unop(Iop_AbsF64, getDReg(dM)), condT);
         DIP("fabsd%s d%u, d%u\n", nCC(INSN_COND), dD, dM);
         goto decode_success;
      }
      else if (b16 == 1 && b7 == 0) {
         // FNEGD
         putDReg(dD, unop(Iop_NegF64, getDReg(dM)), condT);
         DIP("fnegd%s d%u, d%u\n", nCC(INSN_COND), dD, dM);
         goto decode_success;
      }
      else if (b16 == 1 && b7 == 1) {
         // FSQRTD
         IRExpr* rm = get_FAKE_roundingmode(); /* XXXROUNDINGFIXME */
         putDReg(dD, binop(Iop_SqrtF64, rm, getDReg(dM)), condT);
         DIP("fsqrtd%s d%u, d%u\n", nCC(INSN_COND), dD, dM);
         goto decode_success;
      }
      else
         vassert(0);

      /* fall through */
   }

   /* ----------------- I <-> D conversions ----------------- */

   // F{S,U}ITOD dD, fM
   if (BITS8(1,1,1,0,1,0,1,1) == (INSN(27,20) & BITS8(1,1,1,1,1,1,1,1))
       && BITS4(1,0,0,0) == (INSN(19,16) & BITS4(1,1,1,1))
       && BITS4(1,0,1,1) == INSN(11,8)
       && BITS4(0,1,0,0) == (INSN(7,4) & BITS4(0,1,0,1))) {
      UInt bM    = (insn >> 5) & 1;
      UInt fM    = (INSN(3,0) << 1) | bM;
      UInt dD    = INSN(15,12);
      UInt syned = (insn >> 7) & 1;
      if (syned) {
         // FSITOD
         putDReg(dD, unop(Iop_I32StoF64,
                          unop(Iop_ReinterpF32asI32, getFReg(fM))),
                 condT);
         DIP("fsitod%s d%u, s%u\n", nCC(INSN_COND), dD, fM);
      } else {
         // FUITOD
         putDReg(dD, unop(Iop_I32UtoF64,
                          unop(Iop_ReinterpF32asI32, getFReg(fM))),
                 condT);
         DIP("fuitod%s d%u, s%u\n", nCC(INSN_COND), dD, fM);
      }
      goto decode_success;
   }

   // FTO{S,U}ID fD, dM
   if (BITS8(1,1,1,0,1,0,1,1) == (INSN(27,20) & BITS8(1,1,1,1,1,0,1,1))
       && BITS4(1,1,0,0) == (INSN(19,16) & BITS4(1,1,1,0))
       && BITS4(1,0,1,1) == INSN(11,8)
       && BITS4(0,1,0,0) == (INSN(7,4) & BITS4(0,1,1,1))) {
      UInt   bD    = (insn >> 22) & 1;
      UInt   fD    = (INSN(15,12) << 1) | bD;
      UInt   dM    = INSN(3,0);
      UInt   bZ    = (insn >> 7) & 1;
      UInt   syned = (insn >> 16) & 1;
      IRTemp rmode = newTemp(Ity_I32);
      assign(rmode, bZ ? mkU32(Irrm_ZERO)
                       : mkexpr(mk_get_IR_rounding_mode()));
      if (syned) {
         // FTOSID
         putFReg(fD, unop(Iop_ReinterpI32asF32,
                          binop(Iop_F64toI32S, mkexpr(rmode),
                                getDReg(dM))),
                 condT);
         DIP("ftosi%sd%s s%u, d%u\n", bZ ? "z" : "",
             nCC(INSN_COND), fD, dM);
      } else {
         // FTOUID
         putFReg(fD, unop(Iop_ReinterpI32asF32,
                          binop(Iop_F64toI32U, mkexpr(rmode),
                                getDReg(dM))),
                 condT);
         DIP("ftoui%sd%s s%u, d%u\n", bZ ? "z" : "",
             nCC(INSN_COND), fD, dM);
      }
      goto decode_success;
   }

   /* ----------------------------------------------------------- */
   /* -- VFP instructions -- single precision                  -- */
   /* ----------------------------------------------------------- */

   /* --------------------- fldms, fstms --------------------- */
   /*
                                 31   27   23   19 15 11   7   0
                                         P UDWL
      C4-98, C5-26   1  FSTMD    cond 1100 1x00 Rn Fd 1010 offset
      C4-98, C5-28   2  FSTMDIA  cond 1100 1x10 Rn Fd 1010 offset
      C4-98, C5-30   3  FSTMDDB  cond 1101 0x10 Rn Fd 1010 offset

      C4-40, C5-26   1  FLDMD    cond 1100 1x01 Rn Fd 1010 offset
      C4-40, C5-26   2  FLDMIAD  cond 1100 1x11 Rn Fd 1010 offset
      C4-40, C5-26   3  FLDMDBD  cond 1101 0x11 Rn Fd 1010 offset

      Regs transferred: F(Fd:D) .. F(Fd:d + offset)
      offset must not imply a reg > 15
      IA/DB: Rn is changed by (4 x # regs transferred)

      case coding:
         1  at-Rn   (access at Rn)
         2  ia-Rn   (access at Rn, then Rn += 4n)
         3  db-Rn   (Rn -= 4n,     then access at Rn)
   */
   if (BITS8(1,1,0,0,0,0,0,0) == (INSN(27,20) & BITS8(1,1,1,0,0,0,0,0))
       && INSN(11,8) == BITS4(1,0,1,0)) {
      UInt bP     = (insn >> 24) & 1;
      UInt bU     = (insn >> 23) & 1;
      UInt bW     = (insn >> 21) & 1;
      UInt bL     = (insn >> 20) & 1;
      UInt bD     = (insn >> 22) & 1;
      UInt offset = (insn >> 0) & 0xFF;
      UInt rN     = INSN(19,16);
      UInt fD     = (INSN(15,12) << 1) | bD;
      UInt nRegs  = offset;
      Int  i;

      /**/ if (bP == 0 && bU == 1 && bW == 0) {
         vassert(0); //ATC
         summary = 1;
      }
      else if (bP == 0 && bU == 1 && bW == 1) {
         summary = 2;
      }
      else if (bP == 1 && bU == 0 && bW == 1) {
         summary = 3;
      }
      else goto after_vfp_fldms_fstms;

      /* no writebacks to r15 allowed */
      if (rN == 15 && (summary == 2 || summary == 3))
         goto after_vfp_fldms_fstms;

      /* offset must specify at least one register */
      if (offset < 1)
         goto after_vfp_fldms_fstms;

      /* can't transfer regs after S31 */
      if (fD + nRegs - 1 >= 32)
         goto after_vfp_fldms_fstms;

      /* Now, we can't do a conditional load or store, since that very
         likely will generate an exception.  So we have to take a side
         exit at this point if the condition is false. */
      if (condT != IRTemp_INVALID) {
         mk_skip_over_A32_if_cond_is_false( condT );
         condT = IRTemp_INVALID;
      }
      /* Ok, now we're unconditional.  Do the load or store. */

      /* get the old Rn value */
      IRTemp rnT = newTemp(Ity_I32);
      assign(rnT, getIRegA(rN));

      /* make a new value for Rn, post-insn */
      IRTemp rnTnew = IRTemp_INVALID;
      if (summary == 2 || summary == 3) {
         rnTnew = newTemp(Ity_I32);
         assign(rnTnew, binop(summary == 2 ? Iop_Add32 : Iop_Sub32,
                              mkexpr(rnT),
                              mkU32(4 * nRegs)));
      }

      /* decide on the base transfer address */
      IRTemp taT = newTemp(Ity_I32);
      assign(taT, summary == 3 ? mkexpr(rnTnew) : mkexpr(rnT));

      /* update Rn if necessary -- in case 3, we're moving it down, so
         update before any memory reference, in order to keep Memcheck
         and V's stack-extending logic (on linux) happy */
      if (summary == 3)
         putIRegA(rN, mkexpr(rnTnew), IRTemp_INVALID, Ijk_Boring);

      /* generate the transfers */
      for (i = 0; i < nRegs; i++) {
         IRExpr* addr = binop(Iop_Add32, mkexpr(taT), mkU32(4*i));
         if (bL) {
            putFReg(fD + i, loadLE(Ity_F32, addr), IRTemp_INVALID);
         } else {
            storeLE(addr, getFReg(fD + i));
         }
      }

      /* update Rn if necessary -- in case 2, we're moving it up, so
         update after any memory reference, in order to keep Memcheck
         and V's stack-extending logic (on linux) happy */
      if (summary == 2)
         putIRegA(rN, mkexpr(rnTnew), IRTemp_INVALID, Ijk_Boring);

      HChar* nm = bL==1 ? "ld" : "st";
      switch (summary) {
         case 1:  DIP("f%sms%s r%u, {s%u-s%u}\n", 
                      nm, nCC(INSN_COND), rN, fD, fD + nRegs - 1);
                  break;
         case 2:  DIP("f%smias%s r%u!, {s%u-s%u}\n", 
                      nm, nCC(INSN_COND), rN, fD, fD + nRegs - 1);
                  break;
         case 3:  DIP("f%smdbs%s r%u!, {s%u-s%u}\n", 
                      nm, nCC(INSN_COND), rN, fD, fD + nRegs - 1);
                  break;
         default: vassert(0);
      }

      goto decode_success;
      /* FIXME alignment constraints? */
   }

  after_vfp_fldms_fstms:

   /* --------------------- fmsr, fmrs --------------------- */
   if (BITS8(1,1,1,0,0,0,0,0) == (INSN(27,20) & BITS8(1,1,1,1,1,1,1,0))
       && BITS4(1,0,1,0) == INSN(11,8)
       && BITS4(0,0,0,0) == INSN(3,0)
       && BITS4(0,0,0,1) == (INSN(7,4) & BITS4(0,1,1,1))) {
      UInt rD  = INSN(15,12);
      UInt b7  = (insn >> 7) & 1;
      UInt fN  = (INSN(19,16) << 1) | b7;
      UInt b20 = (insn >> 20) & 1;
      if (rD == 15) {
         /* fall through */
         /* Let's assume that no sane person would want to do
            floating-point transfers to or from the program counter,
            and simply decline to decode the instruction.  The ARM ARM
            doesn't seem to explicitly disallow this case, though. */
      } else {
         if (b20) {
            putIRegA(rD, unop(Iop_ReinterpF32asI32, getFReg(fN)),
                         condT, Ijk_Boring);
            DIP("fmrs%s r%u, s%u\n", nCC(INSN_COND), rD, fN);
         } else {
            putFReg(fN, unop(Iop_ReinterpI32asF32, getIRegA(rD)), condT);
            DIP("fmsr%s s%u, r%u\n", nCC(INSN_COND), fN, rD);
         }
         goto decode_success;
      }
      /* fall through */
   }

   /* --------------------- f{ld,st}s --------------------- */
   // FLDS, FSTS
   if (BITS8(1,1,0,1,0,0,0,0) == (INSN(27,20) & BITS8(1,1,1,1,0,0,1,0))
       && BITS4(1,0,1,0) == INSN(11,8)) {
      UInt bD     = (insn >> 22) & 1;
      UInt fD     = (INSN(15,12) << 1) | bD;
      UInt rN     = INSN(19,16);
      UInt offset = (insn & 0xFF) << 2;
      UInt bU     = (insn >> 23) & 1; /* 1: +offset  0: -offset */
      UInt bL     = (insn >> 20) & 1; /* 1: load  0: store */
      /* make unconditional */
      if (condT != IRTemp_INVALID) {
         mk_skip_over_A32_if_cond_is_false( condT );
         condT = IRTemp_INVALID;
      }
      IRTemp ea = newTemp(Ity_I32);
      assign(ea, binop(bU ? Iop_Add32 : Iop_Sub32,
                       getIRegA(rN), mkU32(offset)));
      if (bL) {
         putFReg(fD, loadLE(Ity_F32,mkexpr(ea)), IRTemp_INVALID);
      } else {
         storeLE(mkexpr(ea), getFReg(fD));
      }
      DIP("f%ss%s s%u, [r%u, %c#%u]\n",
          bL ? "ld" : "st", nCC(INSN_COND), fD, rN,
          bU ? '+' : '-', offset);
      goto decode_success;
   }

   /* --------------------- dp insns (F) --------------------- */
   if (BITS8(1,1,1,0,0,0,0,0) == (INSN(27,20) & BITS8(1,1,1,1,0,0,0,0))
       && BITS4(1,0,1,0) == INSN(11,8)
       && BITS4(0,0,0,0) == (INSN(7,4) & BITS4(0,0,0,1))) {
      UInt    bM  = (insn >> 5) & 1;
      UInt    bD  = (insn >> 22) & 1;
      UInt    bN  = (insn >> 7) & 1;
      UInt    fM  = (INSN(3,0) << 1) | bM;   /* argR */
      UInt    fD  = (INSN(15,12) << 1) | bD; /* dst/acc */
      UInt    fN  = (INSN(19,16) << 1) | bN; /* argL */
      UInt    bP  = (insn >> 23) & 1;
      UInt    bQ  = (insn >> 21) & 1;
      UInt    bR  = (insn >> 20) & 1;
      UInt    bS  = (insn >> 6) & 1;
      UInt    opc = (bP << 3) | (bQ << 2) | (bR << 1) | bS;
      IRExpr* rm  = get_FAKE_roundingmode(); /* XXXROUNDINGFIXME */
      switch (opc) {
         case BITS4(0,0,0,0): /* MAC: d + n * m */
            putFReg(fD, triop(Iop_AddF32, rm,
                              getFReg(fD),
                              triop(Iop_MulF32, rm, getFReg(fN), getFReg(fM))),
                        condT);
            DIP("fmacs%s s%u, s%u, s%u\n", nCC(INSN_COND), fD, fN, fM);
            goto decode_success;
         case BITS4(0,0,0,1): /* NMAC: d - n * m */
            putFReg(fD, triop(Iop_SubF32, rm,
                              getFReg(fD),
                              triop(Iop_MulF32, rm, getFReg(fN), getFReg(fM))),
                        condT);
            DIP("fnmacs%s s%u, s%u, s%u\n", nCC(INSN_COND), fD, fN, fM);
            goto decode_success;
         case BITS4(0,0,1,0): /* MSC: - d + n * m */
            putFReg(fD, triop(Iop_AddF32, rm,
                              unop(Iop_NegF32, getFReg(fD)),
                              triop(Iop_MulF32, rm, getFReg(fN), getFReg(fM))),
                        condT);
            DIP("fmscs%s s%u, s%u, s%u\n", nCC(INSN_COND), fD, fN, fM);
            goto decode_success;
         case BITS4(0,0,1,1): /* NMSC: - d - n * m */
            break; //ATC
         case BITS4(0,1,0,0): /* MUL: n * m */
            putFReg(fD, triop(Iop_MulF32, rm, getFReg(fN), getFReg(fM)),
                        condT);
            DIP("fmuls%s s%u, s%u, s%u\n", nCC(INSN_COND), fD, fN, fM);
            goto decode_success;
         case BITS4(0,1,0,1): /* NMUL: - n * m */
            putFReg(fD, unop(Iop_NegF32,
                             triop(Iop_MulF32, rm, getFReg(fN),
                                                   getFReg(fM))),
                    condT);
            DIP("fnmuls%s s%u, s%u, s%u\n", nCC(INSN_COND), fD, fN, fM);
            goto decode_success;
         case BITS4(0,1,1,0): /* ADD: n + m */
            putFReg(fD, triop(Iop_AddF32, rm, getFReg(fN), getFReg(fM)),
                        condT);
            DIP("fadds%s s%u, s%u, s%u\n", nCC(INSN_COND), fD, fN, fM);
            goto decode_success;
         case BITS4(0,1,1,1): /* SUB: n - m */
            putFReg(fD, triop(Iop_SubF32, rm, getFReg(fN), getFReg(fM)),
                        condT);
            DIP("fsubs%s s%u, s%u, s%u\n", nCC(INSN_COND), fD, fN, fM);
            goto decode_success;
         case BITS4(1,0,0,0): /* DIV: n / m */
            putFReg(fD, triop(Iop_DivF32, rm, getFReg(fN), getFReg(fM)),
                        condT);
            DIP("fdivs%s s%u, s%u, s%u\n", nCC(INSN_COND), fD, fN, fM);
            goto decode_success;
         default:
            break;
      }
   }

   /* --------------------- compares (S) --------------------- */
   /*          31   27   23   19   15 11   7    3
                 28   24   20   16 12    8    4    0 
      FCMPS    cond 1110 1D11 0100 Fd 1010 01M0 Fm
      FCMPES   cond 1110 1D11 0100 Fd 1010 11M0 Fm
      FCMPZS   cond 1110 1D11 0101 Fd 1010 0100 0000
      FCMPZED  cond 1110 1D11 0101 Fd 1010 1100 0000
                                 Z         N

      Z=0 Compare Fd:D vs Fm:M     and set FPSCR 31:28 accordingly
      Z=1 Compare Fd:D vs zero

      N=1 generates Invalid Operation exn if either arg is any kind of NaN
      N=0 generates Invalid Operation exn if either arg is a signalling NaN
      (Not that we pay any attention to N here)
   */
   if (BITS8(1,1,1,0,1,0,1,1) == (INSN(27,20) & BITS8(1,1,1,1,1,0,1,1))
       && BITS4(0,1,0,0) == (INSN(19,16) & BITS4(1,1,1,0))
       && BITS4(1,0,1,0) == INSN(11,8)
       && BITS4(0,1,0,0) == (INSN(7,4) & BITS4(0,1,0,1))) {
      UInt bZ = (insn >> 16) & 1;
      UInt bN = (insn >> 7) & 1;
      UInt bD = (insn >> 22) & 1;
      UInt bM = (insn >> 5) & 1;
      UInt fD = (INSN(15,12) << 1) | bD;
      UInt fM = (INSN(3,0) << 1) | bM;
      if (bZ && (INSN(3,0) != 0 || (INSN(7,4) & 3) != 0)) {
         /* does not decode; fall through */
      } else {
         IRTemp argL = newTemp(Ity_F64);
         IRTemp argR = newTemp(Ity_F64);
         IRTemp irRes = newTemp(Ity_I32);

         assign(argL, unop(Iop_F32toF64, getFReg(fD)));
         assign(argR, bZ ? IRExpr_Const(IRConst_F64i(0))
                         : unop(Iop_F32toF64, getFReg(fM)));
         assign(irRes, binop(Iop_CmpF64, mkexpr(argL), mkexpr(argR)));

         IRTemp nzcv     = IRTemp_INVALID;
         IRTemp oldFPSCR = newTemp(Ity_I32);
         IRTemp newFPSCR = newTemp(Ity_I32);

         /* This is where the fun starts.  We have to convert 'irRes'
            from an IR-convention return result (IRCmpF64Result) to an
            ARM-encoded (N,Z,C,V) group.  The final result is in the
            bottom 4 bits of 'nzcv'. */
         /* Map compare result from IR to ARM(nzcv) */
         /*
            FP cmp result | IR   | ARM(nzcv)
            --------------------------------
            UN              0x45   0011
            LT              0x01   1000
            GT              0x00   0010
            EQ              0x40   0110
         */
         nzcv = mk_convert_IRCmpF64Result_to_NZCV(irRes);

         /* And update FPSCR accordingly */
         assign(oldFPSCR, IRExpr_Get(OFFB_FPSCR, Ity_I32));
         assign(newFPSCR, 
                binop(Iop_Or32, 
                      binop(Iop_And32, mkexpr(oldFPSCR), mkU32(0x0FFFFFFF)),
                      binop(Iop_Shl32, mkexpr(nzcv), mkU8(28))));

         putMiscReg32(OFFB_FPSCR, mkexpr(newFPSCR), condT);

         if (bZ) {
            DIP("fcmpz%ss%s s%u\n", bN ? "e" : "", nCC(INSN_COND), fD);
         } else {
            DIP("fcmp%ss%s s%u, s%u\n", bN ? "e" : "",
                nCC(INSN_COND), fD, fM);
         }
         goto decode_success;
      }
      /* fall through */
   }  

   /* --------------------- unary (S) --------------------- */
   if (BITS8(1,1,1,0,1,0,1,1) == (INSN(27,20) & BITS8(1,1,1,1,1,0,1,1))
       && BITS4(0,0,0,0) == (INSN(19,16) & BITS4(1,1,1,0))
       && BITS4(1,0,1,0) == INSN(11,8)
       && BITS4(0,1,0,0) == (INSN(7,4) & BITS4(0,1,0,1))) {
      UInt bD = (insn >> 22) & 1;
      UInt bM = (insn >> 5) & 1;
      UInt fD  = (INSN(15,12) << 1) | bD;
      UInt fM  = (INSN(3,0) << 1) | bM;
      UInt b16 = (insn >> 16) & 1;
      UInt b7  = (insn >> 7) & 1;
      /**/ if (b16 == 0 && b7 == 0) {
         // FCPYS
         putFReg(fD, getFReg(fM), condT);
         DIP("fcpys%s s%u, s%u\n", nCC(INSN_COND), fD, fM);
         goto decode_success;
      }
      else if (b16 == 0 && b7 == 1) {
         // FABSS
         putFReg(fD, unop(Iop_AbsF32, getFReg(fM)), condT);
         DIP("fabss%s s%u, s%u\n", nCC(INSN_COND), fD, fM);
         goto decode_success;
      }
      else if (b16 == 1 && b7 == 0) {
         // FNEGS
         putFReg(fD, unop(Iop_NegF32, getFReg(fM)), condT);
         DIP("fnegs%s s%u, s%u\n", nCC(INSN_COND), fD, fM);
         goto decode_success;
      }
      else if (b16 == 1 && b7 == 1) {
         // FSQRTS
         IRExpr* rm = get_FAKE_roundingmode(); /* XXXROUNDINGFIXME */
         putFReg(fD, binop(Iop_SqrtF32, rm, getFReg(fM)), condT);
         DIP("fsqrts%s s%u, s%u\n", nCC(INSN_COND), fD, fM);
         goto decode_success;
      }
      else
         vassert(0);

      /* fall through */
   }

   /* ----------------- I <-> S conversions ----------------- */

   // F{S,U}ITOS fD, fM
   /* These are more complex than FSITOD/FUITOD.  In the D cases, a 32
      bit int will always fit within the 53 bit mantissa, so there's
      no possibility of a loss of precision, but that's obviously not
      the case here.  Hence this case possibly requires rounding, and
      so it drags in the current rounding mode. */
   if (BITS8(1,1,1,0,1,0,1,1) == (INSN(27,20) & BITS8(1,1,1,1,1,0,1,1))
       && BITS4(1,0,0,0) == (INSN(19,16) & BITS4(1,1,1,1))
       && BITS4(1,0,1,0) == INSN(11,8)
       && BITS4(0,1,0,0) == (INSN(7,4) & BITS4(0,1,0,1))) {
      UInt bM    = (insn >> 5) & 1;
      UInt bD    = (insn >> 22) & 1;
      UInt fM    = (INSN(3,0) << 1) | bM;
      UInt fD    = (INSN(15,12) << 1) | bD;
      UInt syned = (insn >> 7) & 1;
      IRTemp rmode = newTemp(Ity_I32);
      assign(rmode, mkexpr(mk_get_IR_rounding_mode()));
      if (syned) {
         // FSITOS
         putFReg(fD, binop(Iop_F64toF32,
                           mkexpr(rmode),
                           unop(Iop_I32StoF64,
                                unop(Iop_ReinterpF32asI32, getFReg(fM)))),
                 condT);
         DIP("fsitos%s s%u, s%u\n", nCC(INSN_COND), fD, fM);
      } else {
         // FUITOS
         putFReg(fD, binop(Iop_F64toF32,
                           mkexpr(rmode),
                           unop(Iop_I32UtoF64,
                                unop(Iop_ReinterpF32asI32, getFReg(fM)))),
                 condT);
         DIP("fuitos%s s%u, s%u\n", nCC(INSN_COND), fD, fM);
      }
      goto decode_success;
   }

   // FTO{S,U}IS fD, fM
   if (BITS8(1,1,1,0,1,0,1,1) == (INSN(27,20) & BITS8(1,1,1,1,1,0,1,1))
       && BITS4(1,1,0,0) == (INSN(19,16) & BITS4(1,1,1,0))
       && BITS4(1,0,1,0) == INSN(11,8)
       && BITS4(0,1,0,0) == (INSN(7,4) & BITS4(0,1,0,1))) {
      UInt   bM    = (insn >> 5) & 1;
      UInt   bD    = (insn >> 22) & 1;
      UInt   fD    = (INSN(15,12) << 1) | bD;
      UInt   fM    = (INSN(3,0) << 1) | bM;
      UInt   bZ    = (insn >> 7) & 1;
      UInt   syned = (insn >> 16) & 1;
      IRTemp rmode = newTemp(Ity_I32);
      assign(rmode, bZ ? mkU32(Irrm_ZERO)
                       : mkexpr(mk_get_IR_rounding_mode()));
      if (syned) {
         // FTOSIS
         putFReg(fD, unop(Iop_ReinterpI32asF32,
                          binop(Iop_F64toI32S, mkexpr(rmode),
                                unop(Iop_F32toF64, getFReg(fM)))),
                 condT);
         DIP("ftosi%ss%s s%u, d%u\n", bZ ? "z" : "",
             nCC(INSN_COND), fD, fM);
         goto decode_success;
      } else {
         // FTOUIS
         putFReg(fD, unop(Iop_ReinterpI32asF32,
                          binop(Iop_F64toI32U, mkexpr(rmode),
                                unop(Iop_F32toF64, getFReg(fM)))),
                 condT);
         DIP("ftoui%ss%s s%u, d%u\n", bZ ? "z" : "",
             nCC(INSN_COND), fD, fM);
         goto decode_success;
      }
   }

   /* ----------------- S <-> D conversions ----------------- */

   // FCVTDS
   if (BITS8(1,1,1,0,1,0,1,1) == INSN(27,20)
       && BITS4(0,1,1,1) == INSN(19,16)
       && BITS4(1,0,1,0) == INSN(11,8)
       && BITS4(1,1,0,0) == (INSN(7,4) & BITS4(1,1,0,1))) {
      UInt dD = INSN(15,12);
      UInt bM = (insn >> 5) & 1;
      UInt fM = (INSN(3,0) << 1) | bM;
      putDReg(dD, unop(Iop_F32toF64, getFReg(fM)), condT);
      DIP("fcvtds%s d%u, s%u\n", nCC(INSN_COND), dD, fM);
      goto decode_success;
   }

   // FCVTSD
   if (BITS8(1,1,1,0,1,0,1,1) == (INSN(27,20) & BITS8(1,1,1,1,1,0,1,1))
       && BITS4(0,1,1,1) == INSN(19,16)
       && BITS4(1,0,1,1) == INSN(11,8)
       && BITS4(1,1,0,0) == INSN(7,4)) {
      UInt   bD    = (insn >> 22) & 1;
      UInt   fD    = (INSN(15,12) << 1) | bD;
      UInt   dM    = INSN(3,0);
      IRTemp rmode = newTemp(Ity_I32);
      assign(rmode, mkexpr(mk_get_IR_rounding_mode()));
      putFReg(fD, binop(Iop_F64toF32, mkexpr(rmode), getDReg(dM)),
                  condT);
      DIP("fcvtsd%s s%u, d%u\n", nCC(INSN_COND), fD, dM);
      goto decode_success;
   }

   /* ----------------------------------------------------------- */
   /* -- ARMv6 instructions                                    -- */
   /* ----------------------------------------------------------- */

   /* --------------------- ldrex, strex --------------------- */

   // LDREX
   if (0x01900F9F == (insn & 0x0FF00FFF)) {
      UInt rT = INSN(15,12);
      UInt rN = INSN(19,16);
      if (rT == 15 || rN == 15 || rT == 14 /* || (rT & 1)*/) {
         /* undecodable; fall through */
      } else {
         IRTemp res;
         /* make unconditional */
         if (condT != IRTemp_INVALID) {
            mk_skip_over_A32_if_cond_is_false( condT );
            condT = IRTemp_INVALID;
         }
         /* Ok, now we're unconditional.  Do the load. */
         res = newTemp(Ity_I32);
         stmt( IRStmt_LLSC(Iend_LE, res, getIRegA(rN),
                           NULL/*this is a load*/) );
         putIRegA(rT, mkexpr(res), IRTemp_INVALID, Ijk_Boring);
         DIP("ldrex%s r%u, [r%u]\n", nCC(INSN_COND), rT, rN);
         goto decode_success;
      }
      /* fall through */
   }

   // STREX
   if (0x01800F90 == (insn & 0x0FF00FF0)) {
      UInt rT = INSN(3,0);
      UInt rN = INSN(19,16);
      UInt rD = INSN(15,12);
      if (rT == 15 || rN == 15 || rD == 15
          || rT == 14 /* || (rT & 1)*/
          || rD == rT || rN == rT) {
         /* undecodable; fall through */
      } else {
         IRTemp resSC1, resSC32;

         /* make unconditional */
         if (condT != IRTemp_INVALID) {
            mk_skip_over_A32_if_cond_is_false( condT );
            condT = IRTemp_INVALID;
         }

         /* Ok, now we're unconditional.  Do the store. */
         resSC1 = newTemp(Ity_I1);
         stmt( IRStmt_LLSC(Iend_LE, resSC1, getIRegA(rN), getIRegA(rT)) );

         /* Set rD to 1 on failure, 0 on success.  Currently we have
            resSC1 == 0 on failure, 1 on success. */
         resSC32 = newTemp(Ity_I32);
         assign(resSC32,
                unop(Iop_1Uto32, unop(Iop_Not1, mkexpr(resSC1))));

         putIRegA(rD, mkexpr(resSC32),
                      IRTemp_INVALID, Ijk_Boring);
         DIP("strex%s r%u, r%u, [r%u]\n", nCC(INSN_COND), rD, rT, rN);
         goto decode_success;
      }
      /* fall through */
   }

   /* --------------------- movw, movt --------------------- */
   if (0x03000000 == (insn & 0x0FF00000)
       || 0x03400000 == (insn & 0x0FF00000)) /* pray for CSE */ {
      UInt rD    = INSN(15,12);
      UInt imm16 = (insn & 0xFFF) | ((insn >> 4) & 0x0000F000);
      UInt isT   = (insn >> 22) & 1;
      if (rD == 15) {
         /* forget it */
      } else {
         if (isT) {
            putIRegA(rD,
                     binop(Iop_Or32,
                           binop(Iop_And32, getIRegA(rD), mkU32(0xFFFF)),
                           mkU32(imm16 << 16)),
                     condT, Ijk_Boring);
            DIP("movt%s r%u, #0x%04x\n", nCC(INSN_COND), rD, imm16);
            goto decode_success;
         } else {
            putIRegA(rD, mkU32(imm16), condT, Ijk_Boring);
            DIP("movw%s r%u, #0x%04x\n", nCC(INSN_COND), rD, imm16);
            goto decode_success;
         }
      }
      /* fall through */
   }

   /* ------------------- {u,s}xt{b,h}{,16} ------------------- */
   if (BITS8(0,1,1,0,1, 0,0,0) == (INSN(27,20) & BITS8(1,1,1,1,1,0,0,0))
       && BITS4(1,1,1,1) == INSN(19,16)
       && BITS4(0,1,1,1) == INSN(7,4)
       && BITS4(0,0, 0,0) == (INSN(11,8) & BITS4(0,0,1,1))) {
      UInt subopc = INSN(27,20) & BITS8(0,0,0,0,0, 1,1,1);
      if (subopc != BITS4(0,0,0,1) && subopc != BITS4(0,1,0,1)) {
         Int    rot  = (INSN(11,8) >> 2) & 3;
         UInt   rM   = INSN(3,0);
         UInt   rD   = INSN(15,12);
         IRTemp srcT = newTemp(Ity_I32);
         IRTemp rotT = newTemp(Ity_I32);
         IRTemp dstT = newTemp(Ity_I32);
         HChar* nm   = "???";
         assign(srcT, getIRegA(rM));
         assign(rotT, genROR32(srcT, 8 * rot)); /* 0, 8, 16 or 24 only */
         switch (subopc) {
            case BITS4(0,1,1,0): // UXTB
               assign(dstT, unop(Iop_8Uto32, unop(Iop_32to8, mkexpr(rotT))));
               nm = "uxtb";
               break;
            case BITS4(0,0,1,0): // SXTB
               assign(dstT, unop(Iop_8Sto32, unop(Iop_32to8, mkexpr(rotT))));
               nm = "sxtb";
               break;
            case BITS4(0,1,1,1): // UXTH
               assign(dstT, unop(Iop_16Uto32, unop(Iop_32to16, mkexpr(rotT))));
               nm = "uxth";
               break;
            case BITS4(0,0,1,1): // SXTH
               assign(dstT, unop(Iop_16Sto32, unop(Iop_32to16, mkexpr(rotT))));
               nm = "sxth";
               break;
            case BITS4(0,1,0,0): // UXTB16
               assign(dstT, binop(Iop_And32, mkexpr(rotT), mkU32(0x00FF00FF)));
               nm = "uxtb16";
               break;
            case BITS4(0,0,0,0): { // SXTB16
               IRTemp lo32 = newTemp(Ity_I32);
               IRTemp hi32 = newTemp(Ity_I32);
               assign(lo32, binop(Iop_And32, mkexpr(rotT), mkU32(0xFF)));
               assign(hi32, binop(Iop_Shr32, mkexpr(rotT), mkU8(16)));
               assign(
                  dstT,
                  binop(Iop_Or32,
                        binop(Iop_And32,
                              unop(Iop_8Sto32,
                                   unop(Iop_32to8, mkexpr(lo32))),
                              mkU32(0xFFFF)),
                        binop(Iop_Shl32,
                              unop(Iop_8Sto32,
                                   unop(Iop_32to8, mkexpr(hi32))),
                              mkU8(16))
               ));
               nm = "uxtb16";
               break;
            }
            default:
               vassert(0); // guarded by "if" above
         }
         putIRegA(rD, mkexpr(dstT), condT, Ijk_Boring);
         DIP("%s%s r%u, r%u, ROR #%u\n", nm, nCC(INSN_COND), rD, rM, rot);
         goto decode_success;
      }
      /* fall through */
   }

   /* ------------------- bfi, bfc ------------------- */
   if (BITS8(0,1,1,1,1,1,0, 0) == (INSN(27,20) & BITS8(1,1,1,1,1,1,1,0))
       && BITS4(0, 0,0,1) == (INSN(7,4) & BITS4(0,1,1,1))) {
      UInt rD  = INSN(15,12);
      UInt rN  = INSN(3,0);
      UInt msb = (insn >> 16) & 0x1F; /* 20:16 */
      UInt lsb = (insn >> 7) & 0x1F;  /* 11:7 */
      if (rD == 15 || msb < lsb) {
         /* undecodable; fall through */
      } else {
         IRTemp src    = newTemp(Ity_I32);
         IRTemp olddst = newTemp(Ity_I32);
         IRTemp newdst = newTemp(Ity_I32);
         UInt   mask = 1 << (msb - lsb);
         mask = (mask - 1) + mask;
         vassert(mask != 0); // guaranteed by "msb < lsb" check above
         mask <<= lsb;

         assign(src, rN == 15 ? mkU32(0) : getIRegA(rN));
         assign(olddst, getIRegA(rD));
         assign(newdst,
                binop(Iop_Or32,
                   binop(Iop_And32,
                         binop(Iop_Shl32, mkexpr(src), mkU8(lsb)), 
                         mkU32(mask)),
                   binop(Iop_And32,
                         mkexpr(olddst),
                         mkU32(~mask)))
               );

         putIRegA(rD, mkexpr(newdst), condT, Ijk_Boring);

         if (rN == 15) {
            DIP("bfc%s r%u, #%u, #%u\n",
                nCC(INSN_COND), rD, lsb, msb-lsb+1);
         } else {
            DIP("bfi%s r%u, r%u, #%u, #%u\n",
                nCC(INSN_COND), rD, rN, lsb, msb-lsb+1);
         }
         goto decode_success;
      }
      /* fall through */
   }

   /* ------------------- {u,s}bfx ------------------- */
   if (BITS8(0,1,1,1,1,0,1,0) == (INSN(27,20) & BITS8(1,1,1,1,1,0,1,0))
       && BITS4(0,1,0,1) == (INSN(7,4) & BITS4(0,1,1,1))) {
      UInt rD  = INSN(15,12);
      UInt rN  = INSN(3,0);
      UInt wm1 = (insn >> 16) & 0x1F; /* 20:16 */
      UInt lsb = (insn >> 7) & 0x1F;  /* 11:7 */
      UInt msb = lsb + wm1;
      UInt isU = (insn >> 22) & 1;    /* 22:22 */
      if (rD == 15 || rN == 15 || msb >= 32) {
         /* undecodable; fall through */
      } else {
         IRTemp src  = newTemp(Ity_I32);
         IRTemp tmp  = newTemp(Ity_I32);
         IRTemp res  = newTemp(Ity_I32);
         UInt   mask = ((1 << wm1) - 1) + (1 << wm1);
         vassert(msb >= 0 && msb <= 31);
         vassert(mask != 0); // guaranteed by msb being in 0 .. 31 inclusive

         assign(src, getIRegA(rN));
         assign(tmp, binop(Iop_And32,
                           binop(Iop_Shr32, mkexpr(src), mkU8(lsb)),
                           mkU32(mask)));
         assign(res, binop(isU ? Iop_Shr32 : Iop_Sar32,
                           binop(Iop_Shl32, mkexpr(tmp), mkU8(31-wm1)),
                           mkU8(31-wm1)));

         putIRegA(rD, mkexpr(res), condT, Ijk_Boring);

         DIP("%s%s r%u, r%u, #%u, #%u\n",
             isU ? "ubfx" : "sbfx",
             nCC(INSN_COND), rD, rN, lsb, wm1 + 1);
         goto decode_success;
      }
      /* fall through */
   }

   /* ------------------- smul{b,t}{b,t} ------------- */
   if (BITS8(0,0,0,1,0,1,1,0) == INSN(27,20)
       && BITS4(0,0,0,0) == INSN(15,12)
       && BITS4(1,0,0,0) == (INSN(7,4) & BITS4(1,0,0,1))) {
      UInt rD  = INSN(19,16);
      UInt rM  = INSN(11,8);
      UInt rN  = INSN(3,0);
      UInt bM = (insn >> 6) & 1;
      UInt bN = (insn >> 5) & 1;
      if (bN == 0 && bM == 1) goto decode_failure; //ATC
      if (bN == 1 && bM == 0) goto decode_failure; //ATC
      if (bN == 1 && bM == 1) goto decode_failure; //ATC
      if (rD == 15 || rN == 15 || rM == 15) {
         /* undecodable; fall through */
      } else {
         IRTemp srcL = newTemp(Ity_I32);
         IRTemp srcR = newTemp(Ity_I32);
         IRTemp res  = newTemp(Ity_I32);

         /* Extract and sign extend the two 16-bit operands */
         assign(srcL, binop(Iop_Sar32,
                            binop(Iop_Shl32, getIRegA(rN),
                                             mkU8(bN ? 0 : 16)),
                            mkU8(16)));
         assign(srcR, binop(Iop_Sar32,
                            binop(Iop_Shl32, getIRegA(rM),
                                             mkU8(bM ? 0 : 16)),
                            mkU8(16)));

         assign(res, binop(Iop_Mul32, mkexpr(srcL), mkexpr(srcR)));
         putIRegA(rD, mkexpr(res), condT, Ijk_Boring);

         DIP("smul%c%c%s r%u, r%u, r%u\n",
             bN ? 't' : 'b', bM ? 't' : 'b', nCC(INSN_COND), rD, rN, rM);
         goto decode_success;
      }
      /* fall through */
   }

   /* --------------------- Load/store doubleword ------------- */
   // LDRD STRD
   /*                 31   27   23   19 15 11   7    3     # highest bit
                        28   24   20 16 12    8    4    0
      A5-36   1 | 16  cond 0001 U100 Rn Rd im4h 11S1 im4l
      A5-38   1 | 32  cond 0001 U000 Rn Rd 0000 11S1 Rm
      A5-40   2 | 16  cond 0001 U110 Rn Rd im4h 11S1 im4l
      A5-42   2 | 32  cond 0001 U010 Rn Rd 0000 11S1 Rm
      A5-44   3 | 16  cond 0000 U100 Rn Rd im4h 11S1 im4l
      A5-46   3 | 32  cond 0000 U000 Rn Rd 0000 11S1 Rm
   */
   /* case coding:
             1   at-ea               (access at ea)
             2   at-ea-then-upd      (access at ea, then Rn = ea)
             3   at-Rn-then-upd      (access at Rn, then Rn = ea)
      ea coding
             16  Rn +/- imm8
             32  Rn +/- Rm
   */
   /* Quickly skip over all of this for hopefully most instructions */
   if ((INSN(27,24) & BITS4(1,1,1,0)) != BITS4(0,0,0,0))
      goto after_load_store_doubleword;

   /* Check the "11S1" thing. */
   if ((INSN(7,4) & BITS4(1,1,0,1)) != BITS4(1,1,0,1))
      goto after_load_store_doubleword;

   summary = 0;

   /**/ if (INSN(27,24) == BITS4(0,0,0,1) && INSN(22,20) == BITS3(1,0,0)) {
      summary = 1 | 16;
   }
   else if (INSN(27,24) == BITS4(0,0,0,1) && INSN(22,20) == BITS3(0,0,0)) {
      summary = 1 | 32;
   }
   else if (INSN(27,24) == BITS4(0,0,0,1) && INSN(22,20) == BITS3(1,1,0)) {
      summary = 2 | 16;
   }
   else if (INSN(27,24) == BITS4(0,0,0,1) && INSN(22,20) == BITS3(0,1,0)) {
      summary = 2 | 32;
   }
   else if (INSN(27,24) == BITS4(0,0,0,0) && INSN(22,20) == BITS3(1,0,0)) {
      summary = 3 | 16;
   }
   else if (INSN(27,24) == BITS4(0,0,0,0) && INSN(22,20) == BITS3(0,0,0)) {
      summary = 3 | 32;
      goto decode_failure; //ATC
   }
   else goto after_load_store_doubleword;

   { UInt rN   = (insn >> 16) & 0xF; /* 19:16 */
     UInt rD   = (insn >> 12) & 0xF; /* 15:12 */
     UInt rM   = (insn >> 0)  & 0xF; /*  3:0  */
     UInt bU   = (insn >> 23) & 1;   /* 23 U=1 offset+, U=0 offset- */
     UInt bS   = (insn >> 5) & 1;    /* S=1 store, S=0 load */
     UInt imm8 = ((insn >> 4) & 0xF0) | (insn & 0xF); /* 11:8, 3:0 */

     /* Require rD to be an even numbered register */
     if ((rD & 1) != 0)
        goto after_load_store_doubleword;

     /* Require 11:8 == 0 for Rn +/- Rm cases */
     if ((summary & 32) != 0 && (imm8 & 0xF0) != 0)
        goto after_load_store_doubleword;

     /* Skip some invalid cases, which would lead to two competing
        updates to the same register, or which are otherwise
        disallowed by the spec. */
     switch (summary) {
        case 1 | 16:
           break;
        case 1 | 32: 
           if (rM == 15) goto after_load_store_doubleword;
           break;
        case 2 | 16: case 3 | 16:
           if (rN == 15) goto after_load_store_doubleword;
           if (bS == 0 && (rN == rD || rN == rD+1))
              goto after_load_store_doubleword;
           break;
        case 2 | 32: case 3 | 32:
           if (rM == 15) goto after_load_store_doubleword;
           if (rN == 15) goto after_load_store_doubleword;
           if (rN == rM) goto after_load_store_doubleword;
           if (bS == 0 && (rN == rD || rN == rD+1))
              goto after_load_store_doubleword;
           break;
        default:
           vassert(0);
     }

     /* Now, we can't do a conditional load or store, since that very
        likely will generate an exception.  So we have to take a side
        exit at this point if the condition is false. */
     if (condT != IRTemp_INVALID) {
        mk_skip_over_A32_if_cond_is_false( condT );
        condT = IRTemp_INVALID;
     }
     /* Ok, now we're unconditional.  Do the load or store. */

     /* compute the effective address.  Bind it to a tmp since we
        may need to use it twice. */
     IRExpr* eaE = NULL;
     switch (summary & 0xF0) {
        case 16:
           eaE = mk_EA_reg_plusminus_imm8( rN, bU, imm8, dis_buf );
           break;
        case 32:
           eaE = mk_EA_reg_plusminus_reg( rN, bU, rM, dis_buf );
           break;
     }
     vassert(eaE);
     IRTemp eaT = newTemp(Ity_I32);
     assign(eaT, eaE);

     /* get the old Rn value */
     IRTemp rnT = newTemp(Ity_I32);
     assign(rnT, getIRegA(rN));

     /* decide on the transfer address */
     IRTemp taT = IRTemp_INVALID;
     switch (summary & 0x0F) {
        case 1: case 2: taT = eaT; break;
        case 3:         taT = rnT; break;
     }
     vassert(taT != IRTemp_INVALID);

     /* XXX deal with alignment constraints */
     /* XXX: but the A8 doesn't seem to trap for misaligned loads, so,
        ignore alignment issues for the time being. */

     /* doubleword store  S 1
        doubleword load   S 0
     */
     HChar* name = NULL;
     /* generate the transfers */
     if (bS == 1) { // doubleword store
        storeLE( binop(Iop_Add32, mkexpr(taT), mkU32(0)), getIRegA(rD+0) );
        storeLE( binop(Iop_Add32, mkexpr(taT), mkU32(4)), getIRegA(rD+1) );
        name = "strd";
     } else { // doubleword load
        putIRegA( rD+0,
                  loadLE(Ity_I32, binop(Iop_Add32, mkexpr(taT), mkU32(0))),
                  IRTemp_INVALID, Ijk_Boring );
        putIRegA( rD+1,
                  loadLE(Ity_I32, binop(Iop_Add32, mkexpr(taT), mkU32(4))),
                  IRTemp_INVALID, Ijk_Boring );
        name = "ldrd";
     }

     /* Update Rn if necessary. */
     switch (summary & 0x0F) {
        case 2: case 3:
           // should be assured by logic above:
           if (bS == 0) {
              vassert(rD+0 != rN); /* since we just wrote rD+0 */
              vassert(rD+1 != rN); /* since we just wrote rD+1 */
           }
           putIRegA( rN, mkexpr(eaT), IRTemp_INVALID, Ijk_Boring );
           break;
     }

     switch (summary & 0x0F) {
        case 1:  DIP("%s%s r%u, %s\n", name, nCC(INSN_COND), rD, dis_buf);
                 break;
        case 2:  DIP("%s%s r%u, %s! (at-EA-then-Rn=EA)\n",
                     name, nCC(INSN_COND), rD, dis_buf);
                 break;
        case 3:  DIP("%s%s r%u, %s! (at-Rn-then-Rn=EA)\n",
                     name, nCC(INSN_COND), rD, dis_buf);
                 break;
        default: vassert(0);
     }

     goto decode_success;
   }

  after_load_store_doubleword:

   /* ------------------- {s,u}xtab ------------- */
   if (BITS8(0,1,1,0,1,0,1,0) == (INSN(27,20) & BITS8(1,1,1,1,1,0,1,1))
       && BITS4(0,0,0,0) == (INSN(11,8) & BITS4(0,0,1,1))
       && BITS4(0,1,1,1) == INSN(7,4)) {
      UInt rN  = INSN(19,16);
      UInt rD  = INSN(15,12);
      UInt rM  = INSN(3,0);
      UInt rot = (insn >> 10) & 3;
      UInt isU = INSN(22,22);
      if (rN == 15/*it's {S,U}XTB*/ || rD == 15 || rM == 15) {
         /* undecodable; fall through */
      } else {
         IRTemp srcL = newTemp(Ity_I32);
         IRTemp srcR = newTemp(Ity_I32);
         IRTemp res  = newTemp(Ity_I32);
         assign(srcR, getIRegA(rM));
         assign(srcL, getIRegA(rN));
         assign(res,  binop(Iop_Add32,
                            mkexpr(srcL),
                            unop(isU ? Iop_8Uto32 : Iop_8Sto32,
                                 unop(Iop_32to8, 
                                      genROR32(srcR, 8 * rot)))));
         putIRegA(rD, mkexpr(res), condT, Ijk_Boring);
         DIP("%cxtab%s r%u, r%u, r%u, ror #%u\n",
             isU ? 'u' : 's', nCC(INSN_COND), rD, rN, rM, rot);
         goto decode_success;
      }
      /* fall through */
   }

   /* ------------------- {s,u}xtah ------------- */
   if (BITS8(0,1,1,0,1,0,1,1) == (INSN(27,20) & BITS8(1,1,1,1,1,0,1,1))
       && BITS4(0,0,0,0) == (INSN(11,8) & BITS4(0,0,1,1))
       && BITS4(0,1,1,1) == INSN(7,4)) {
      UInt rN  = INSN(19,16);
      UInt rD  = INSN(15,12);
      UInt rM  = INSN(3,0);
      UInt rot = (insn >> 10) & 3;
      UInt isU = INSN(22,22);
      if (rN == 15/*it's {S,U}XTH*/ || rD == 15 || rM == 15) {
         /* undecodable; fall through */
      } else {
         IRTemp srcL = newTemp(Ity_I32);
         IRTemp srcR = newTemp(Ity_I32);
         IRTemp res  = newTemp(Ity_I32);
         assign(srcR, getIRegA(rM));
         assign(srcL, getIRegA(rN));
         assign(res,  binop(Iop_Add32,
                            mkexpr(srcL),
                            unop(isU ? Iop_16Uto32 : Iop_16Sto32,
                                 unop(Iop_32to16, 
                                      genROR32(srcR, 8 * rot)))));
         putIRegA(rD, mkexpr(res), condT, Ijk_Boring);

         DIP("%cxtah%s r%u, r%u, r%u, ror #%u\n",
             isU ? 'u' : 's', nCC(INSN_COND), rD, rN, rM, rot);
         goto decode_success;
      }
      /* fall through */
   }

   /* ----------------------------------------------------------- */
   /* -- ARMv7 instructions                                    -- */
   /* ----------------------------------------------------------- */

   /* -------------- read CP15 TPIDRURO register ------------- */
   /* mrc     p15, 0, r0, c13, c0, 3  up to
      mrc     p15, 0, r14, c13, c0, 3
   */
   /* I don't know whether this is really v7-only.  But anyway, we
      have to support it since arm-linux uses TPIDRURO as a thread
      state register. */
   if (0x0E1D0F70 == (insn & 0x0FFF0FFF)) {
      UInt rD = INSN(15,12);
      if (rD <= 14) {
         /* skip r15, that's too stupid to handle */
         putIRegA(rD, IRExpr_Get(OFFB_TPIDRURO, Ity_I32),
                      condT, Ijk_Boring);
         DIP("mrc%s p15,0, r%u, c13, c0, 3\n", nCC(INSN_COND), rD);
         goto decode_success;
      }
      /* fall through */
   }

   /* Handle various kinds of barriers.  This is rather indiscriminate
      in the sense that they are all turned into an IR Fence, which
      means we don't know which they are, so the back end has to
      re-emit them all when it comes acrosss an IR Fence.
   */
   switch (insn) {
      case 0xEE070F9A: /* v6 */
         /* mcr 15, 0, r0, c7, c10, 4 (v6) equiv to DSB (v7).  Data
            Synch Barrier -- ensures completion of memory accesses. */
         stmt( IRStmt_MBE(Imbe_Fence) );
         DIP("mcr 15, 0, r0, c7, c10, 4 (data synch barrier)\n");
         goto decode_success;
      case 0xEE070FBA: /* v6 */
         /* mcr 15, 0, r0, c7, c10, 5 (v6) equiv to DMB (v7).  Data
            Memory Barrier -- ensures ordering of memory accesses. */
         stmt( IRStmt_MBE(Imbe_Fence) );
         DIP("mcr 15, 0, r0, c7, c10, 5 (data memory barrier)\n");
         goto decode_success;
      case 0xEE070F95: /* v6 */
         /* mcr 15, 0, r0, c7, c5, 4 (v6) equiv to ISB (v7).
            Instruction Synchronisation Barrier (or Flush Prefetch
            Buffer) -- a pipe flush, I think.  I suspect we could
            ignore those, but to be on the safe side emit a fence
            anyway. */
         stmt( IRStmt_MBE(Imbe_Fence) );
         DIP("mcr 15, 0, r0, c7, c5, 4 (insn synch barrier)\n");
         goto decode_success;
      default:
         break;
   }

   /* ----------------------------------------------------------- */
   /* -- Undecodable                                           -- */
   /* ----------------------------------------------------------- */

   goto decode_failure;
   /*NOTREACHED*/

  decode_failure:
   /* All decode failures end up here. */
   vex_printf("disInstr(arm): unhandled instruction: "
              "0x%x\n", insn);
   vex_printf("                 cond=%d(0x%x) 27:20=%u(0x%02x) "
                                "4:4=%d "
                                "3:0=%u(0x%x)\n",
              (Int)INSN_COND, (UInt)INSN_COND,
              (Int)INSN(27,20), (UInt)INSN(27,20),
              (Int)INSN(4,4),
              (Int)INSN(3,0), (UInt)INSN(3,0) );

   /* Tell the dispatcher that this insn cannot be decoded, and so has
      not been executed, and (is currently) the next to be executed.
      R15 should be up-to-date since it made so at the start of each
      insn, but nevertheless be paranoid and update it again right
      now. */
   vassert(0 == (guest_R15_curr_instr_notENC & 3));
   llPutIReg( 15, mkU32(guest_R15_curr_instr_notENC) );
   irsb->next     = mkU32(guest_R15_curr_instr_notENC);
   irsb->jumpkind = Ijk_NoDecode;
   dres.whatNext  = Dis_StopHere;
   dres.len       = 0;
   return dres;

  decode_success:
   /* All decode successes end up here. */
   DIP("\n");

   vassert(dres.len == 4 || dres.len == 20);

   /* Now then.  Do we have an implicit jump to r15 to deal with? */
   if (r15written) {
      /* If we get jump to deal with, we assume that there's been no
         other competing branch stuff previously generated for this
         insn.  That's reasonable, in the sense that the ARM insn set
         appears to declare as "Unpredictable" any instruction which
         generates more than one possible new value for r15.  Hence
         just assert.  The decoders themselves should check against
         all such instructions which are thusly Unpredictable, and
         decline to decode them.  Hence we should never get here if we
         have competing new values for r15, and hence it is safe to
         assert here. */
      vassert(dres.whatNext == Dis_Continue);
      vassert(irsb->next == NULL);
      vassert(irsb->jumpkind = Ijk_Boring);
      /* If r15 is unconditionally written, terminate the block by
         jumping to it.  If it's conditionally written, still
         terminate the block (a shame, but we can't do side exits to
         arbitrary destinations), but first jump to the next
         instruction if the condition doesn't hold. */
      /* We can't use getIReg(15) to get the destination, since that
         will produce r15+8, which isn't what we want.  Must use
         llGetIReg(15) instead. */
      if (r15guard == IRTemp_INVALID) {
         /* unconditional */
      } else {
         /* conditional */
         stmt( IRStmt_Exit(
                  unop(Iop_32to1,
                       binop(Iop_Xor32,
                             mkexpr(r15guard), mkU32(1))),
                  r15kind,
                  IRConst_U32(guest_R15_curr_instr_notENC + 4)
         ));
      }
      irsb->next     = llGetIReg(15);
      irsb->jumpkind = r15kind;
      dres.whatNext  = Dis_StopHere;
   }

   return dres;

#  undef INSN_COND
#  undef INSN
}


/*------------------------------------------------------------*/
/*--- Disassemble a single Thumb2 instruction              ---*/
/*------------------------------------------------------------*/

/* NB: in Thumb mode we do fetches of regs with getIRegT, which
   automagically adds 4 to fetches of r15.  However, writes to regs
   are done with putIRegT, which disallows writes to r15.  Hence any
   r15 writes and associated jumps have to be done "by hand". */

/* Disassemble a single Thumb instruction into IR.  The instruction is
   located in host memory at guest_instr, and has (decoded) guest IP
   of guest_R15_curr_instr_notENC, which will have been set before the
   call here. */

static   
DisResult disInstr_THUMB_WRK (
             Bool         put_IP,
             Bool         (*resteerOkFn) ( /*opaque*/void*, Addr64 ),
             Bool         resteerCisOk,
             void*        callback_opaque,
             UChar*       guest_instr,
             VexArchInfo* archinfo,
             VexAbiInfo*  abiinfo
          )
{
   /* A macro to fish bits out of insn0.  There's also INSN1, to fish
      bits out of insn1, but that's defined only after the end of the
      16-bit insn decoder, so as to stop it mistakenly being used
      therein. */
#  define INSN0(_bMax,_bMin)  SLICE_UInt(((UInt)insn0), (_bMax), (_bMin))

   DisResult dres;
   UShort    insn0; /* first 16 bits of the insn */
   //Bool      allow_VFP = False;
   //UInt      hwcaps = archinfo->hwcaps;
   HChar     dis_buf[128];  // big enough to hold LDMIA etc text

   /* What insn variants are we supporting today? */
   //allow_VFP  = (0 != (hwcaps & VEX_HWCAPS_ARM_VFP));
   // etc etc

   /* Set result defaults. */
   dres.whatNext   = Dis_Continue;
   dres.len        = 2;
   dres.continueAt = 0;

   /* Set default actions for post-insn handling of writes to r15, if
      required. */
   r15written = False;
   r15guard   = IRTemp_INVALID; /* unconditional */
   r15kind    = Ijk_Boring;

   /* Insns could be 2 or 4 bytes long.  Just get the first 16 bits at
      this point.  If we need the second 16, get them later.  We can't
      get them both out immediately because it risks a fault (very
      unlikely, but ..) if the second 16 bits aren't actually
      necessary. */
   insn0 = getUShortLittleEndianly( guest_instr );

   if (0) vex_printf("insn: 0x%x\n", insn0);

   DIP("\t(thumb) 0x%x:  ", (UInt)guest_R15_curr_instr_notENC);

   /* We may be asked to update the guest R15 before going further. */
   vassert(0 == (guest_R15_curr_instr_notENC & 1));
   if (put_IP) {
      llPutIReg( 15, mkU32(guest_R15_curr_instr_notENC | 1) );
   }

   /* ----------------------------------------------------------- */
#if 0
   /* Spot "Special" instructions (see comment at top of file). */
   {
      UChar* code = (UChar*)guest_instr;
      /* Spot the 16-byte preamble: 

         e1a0c1ec  mov r12, r12, ROR #3
         e1a0c6ec  mov r12, r12, ROR #13
         e1a0ceec  mov r12, r12, ROR #29
         e1a0c9ec  mov r12, r12, ROR #19
      */
      UInt word1 = 0xE1A0C1EC;
      UInt word2 = 0xE1A0C6EC;
      UInt word3 = 0xE1A0CEEC;
      UInt word4 = 0xE1A0C9EC;
      if (getUIntLittleEndianly(code+ 0) == word1 &&
          getUIntLittleEndianly(code+ 4) == word2 &&
          getUIntLittleEndianly(code+ 8) == word3 &&
          getUIntLittleEndianly(code+12) == word4) {
         /* Got a "Special" instruction preamble.  Which one is it? */
         if (getUIntLittleEndianly(code+16) == 0xE18AA00A
                                               /* orr r10,r10,r10 */) {
            /* R3 = client_request ( R4 ) */
            DIP("r3 = client_request ( %%r4 )\n");
            irsb->next     = mkU32( guest_R15_curr_instr_notENC + 20 );
            irsb->jumpkind = Ijk_ClientReq;
            dres.whatNext  = Dis_StopHere;
            goto decode_success;
         }
         else
         if (getUIntLittleEndianly(code+16) == 0xE18BB00B
                                               /* orr r11,r11,r11 */) {
            /* R3 = guest_NRADDR */
            DIP("r3 = guest_NRADDR\n");
            dres.len = 20;
            llPutIReg(3, IRExpr_Get( OFFB_NRADDR, Ity_I32 ));
            goto decode_success;
         }
         else
         if (getUIntLittleEndianly(code+16) == 0xE18CC00C
                                               /* orr r12,r12,r12 */) {
            /*  branch-and-link-to-noredir R4 */
            DIP("branch-and-link-to-noredir r4\n");
            llPutIReg(14, mkU32( guest_R15_curr_instr_notENC + 20) );
            irsb->next     = getIRegT(4);
            irsb->jumpkind = Ijk_NoRedir;
            dres.whatNext  = Dis_StopHere;
            goto decode_success;
         }
         /* We don't know what it is.  Set opc1/opc2 so decode_failure
            can print the insn following the Special-insn preamble. */
         insn = getUIntLittleEndianly(code+16);
         goto decode_failure;
         /*NOTREACHED*/
      }

   }
#endif
   /* ----------------------------------------------------------- */

   /* Main Thumb instruction decoder starts here.  It's a series of
      switches which examine ever longer bit sequences at the MSB of
      the instruction word, first for 16-bit insns, then for 32-bit
      insns. */

   /* --- BEGIN optimisation --- */
   /* This is a crucial optimisation for the ITState boilerplate that
      follows.  Examine the 9 halfwords preceding this instruction,
      and if we are absolutely sure that none of them constitute an
      'it' instruction, then we can be sure that this instruction is
      not under the control of any 'it' instruction, and so
      guest_ITSTATE must be zero.  So write zero into ITSTATE right
      now, so that iropt can fold out almost all of the resulting
      junk.

      If we aren't sure, we can always safely skip this step.  So be a
      bit conservative about it: only poke around in the same page as
      this instruction, lest we get a fault from the previous page
      that would not otherwise have happened.  The saving grace is
      that such skipping is pretty rare -- it only happens,
      statistically, 18/4096ths of the time, so is judged unlikely to
      be a performance problems.

      FIXME: do better.  Take into account the number of insns covered
      by any IT insns we find, to rule out cases where an IT clearly
      cannot cover this instruction.  This would improve behaviour for
      branch targets immediately following an IT-guarded group that is
      not of full length.  Eg, (and completely ignoring issues of 16-
      vs 32-bit insn length):

             ite cond
             insn1
             insn2
      label: insn3
             insn4

      The 'it' only conditionalises insn1 and insn2.  However, the
      current analysis is conservative and considers insn3 and insn4
      also possibly guarded.  Hence if 'label:' is the start of a hot
      loop we will get a big performance hit.
   */
   {
      /* Summary result of this analysis: False == safe but
         suboptimal. */
      Bool forceZ = False;

      UInt pc = guest_R15_curr_instr_notENC;
      vassert(0 == (pc & 1));

      UInt pageoff = pc & 0xFFF;
      if (pageoff >= 18) {
         /* It's safe to poke about in the 9 halfwords preceding this
            insn.  So, have a look at them. */
         forceZ = True; /* assume no 'it' insn found, till we do */

         UShort* hwp = (UShort*)pc;
         Int i;
         for (i = -1; i >= -9; i--) {
            /* We're in the same page.  (True, but commented out due
               to expense.) */
            /*
            vassert( ( ((UInt)(&hwp[i])) & 0xFFFFF000 )
                      == ( pc & 0xFFFFF000 ) );
            */
            if ((hwp[i] & 0xFF00) == 0xBF00) {
               /* might be an 'it' insn.  Play safe. */
               forceZ = False;
               break;
            }
         }
      }
      /* So, did we get lucky? */
      if (forceZ) {
         IRTemp t = newTemp(Ity_I32);
         assign(t, mkU32(0));
         put_ITSTATE(t);
      }
   }
   /* --- END optimisation --- */

   /* Generate the guarding condition for this insn, by examining
      ITSTATE.  Assign it to condT.  Also, generate new
      values for ITSTATE ready for stuffing back into the
      guest state, but don't actually do the Put yet, since it will
      need to stuffed back in only after the instruction gets to a
      point where it is sure to complete.  Mostly we let the code at
      decode_success handle this, but in cases where the insn contains
      a side exit, we have to update them before the exit. */

   IRTemp old_itstate = get_ITSTATE();

   IRTemp new_itstate = newTemp(Ity_I32);
   assign(new_itstate, binop(Iop_Shr32, mkexpr(old_itstate), mkU8(8)));

   put_ITSTATE(new_itstate);

   /* Same strategy as for ARM insns: generate a condition temporary
      at this point  (or IRTemp_INVALID, meaning
      unconditional).  We leave it to lower-level instruction decoders
      to decide whether they can generate straight-line code, or
      whether they must generate a side exit before the instruction.
      condT :: Ity_I32 and is always either zero or one. */
   IRTemp condT = newTemp(Ity_I32);
   assign(condT,
          mk_armg_calculate_condition_dyn(
             binop(Iop_Xor32,
                   binop(Iop_And32, mkexpr(old_itstate), mkU32(0xF0)),
                   mkU32(0xE0))
          )
   );

   /* Something we don't have in ARM: generate a 0 or 1 value
      indicating whether or not we are in an IT block (NB: 0 = in IT
      block, 1 = not in IT block).  This is used to gate condition
      code updates in 16-bit Thumb instructions. */
   IRTemp notInITt = newTemp(Ity_I32);
   assign(notInITt,
          binop(Iop_Xor32,
                binop(Iop_And32, mkexpr(old_itstate), mkU32(1)),
                mkU32(1)));

   /* Compute 'condT && notInITt' -- that is, the instruction is going
      to execute, and we're not in an IT block.  This is the gating
      condition for updating condition codes in 16-bit Thumb
      instructions, except for CMP, CMN and TST. */
   IRTemp cond_AND_notInIT_T = newTemp(Ity_I32);
   assign(cond_AND_notInIT_T,
          binop(Iop_And32, mkexpr(notInITt), mkexpr(condT)));

   /* At this point:
      * ITSTATE has been updated
      * condT holds the guarding condition for this instruction (0 or 1),
      * notInITt is 1 if we're in "normal" code, 0 if in an IT block
      * cond_AND_notInIT_T is the AND of the above two.

      If the instruction proper can't trap, then there's nothing else
      to do w.r.t. ITSTATE -- just go and and generate IR for the
      insn, taking into account the guarding condition.

      If, however, the instruction might trap, then we must back up
      ITSTATE to the old value, and re-update it after the potentially
      trapping IR section.  A trap can happen either via a memory
      reference or because we need to throw SIGILL.

      If an instruction has a side exit, we need to be sure that any
      ITSTATE backup is re-updated before the side exit.
   */

   /* ----------------------------------------------------------- */
   /* --                                                       -- */
   /* -- Thumb 16-bit integer instructions                     -- */
   /* --                                                       -- */
   /* -- IMPORTANT: references to insn1 or INSN1 are           -- */
   /* --            not allowed in this section                -- */
   /* --                                                       -- */
   /* ----------------------------------------------------------- */

   /* 16-bit instructions inside an IT block, apart from CMP, CMN and
      TST, do not set the condition codes.  Hence we must dynamically
      test for this case for every condition code update. */

   IROp   anOp   = Iop_INVALID;
   HChar* anOpNm = NULL;

   /* ================ 16-bit 15:6 cases ================ */

   switch (INSN0(15,6)) {

   case 0x10a: {
      /* ---------------- CMP Rn, Rm ---------------- */
      UInt   rN    = INSN0(2,0);
      UInt   rM    = INSN0(5,3);
      IRTemp argL  = newTemp(Ity_I32);
      IRTemp argR  = newTemp(Ity_I32);
      assign( argL, getIRegT(rN) );
      assign( argR, getIRegT(rM) );
      /* Update flags regardless of whether in an IT block or not. */
      setFlags_D1_D2( ARMG_CC_OP_SUB, argL, argR, condT );
      DIP("cmp r%u, r%u\n", rN, rM);
      goto decode_success;
   }

   case 0x108: {
      /* ---------------- TST Rn, Rm ---------------- */
      UInt   rN   = INSN0(2,0);
      UInt   rM   = INSN0(5,3);
      IRTemp oldC = newTemp(Ity_I32);
      IRTemp oldV = newTemp(Ity_I32);
      IRTemp res  = newTemp(Ity_I32);
      assign( oldC, mk_armg_calculate_flag_c() );
      assign( oldV, mk_armg_calculate_flag_v() );
      assign( res,  binop(Iop_And32, getIRegT(rN), getIRegT(rM)) );
      /* Update flags regardless of whether in an IT block or not. */
      setFlags_D1_D2_ND( ARMG_CC_OP_LOGIC, res, oldC, oldV, condT );
      DIP("tst r%u, r%u\n", rN, rM);
      goto decode_success;
   }

   case 0x109: {
      /* ---------------- NEGS Rd, Rm ---------------- */
      /* Rd = -Rm */
      UInt   rM   = INSN0(5,3);
      UInt   rD   = INSN0(2,0);
      IRTemp arg  = newTemp(Ity_I32);
      IRTemp zero = newTemp(Ity_I32);
      assign(arg, getIRegT(rM));
      assign(zero, mkU32(0));
      // rD can never be r15
      putIRegT(rD, binop(Iop_Sub32, mkexpr(zero), mkexpr(arg)), condT);
      setFlags_D1_D2( ARMG_CC_OP_SUB, zero, arg, cond_AND_notInIT_T);
      DIP("negs r%u, r%u\n", rD, rM);
      goto decode_success;
   }

   case 0x10F: {
      /* ---------------- MVNS Rd, Rm ---------------- */
      /* Rd = ~Rm */
      UInt   rM   = INSN0(5,3);
      UInt   rD   = INSN0(2,0);
      IRTemp oldV = newTemp(Ity_I32);
      IRTemp oldC = newTemp(Ity_I32);
      IRTemp res  = newTemp(Ity_I32);
      assign( oldV, mk_armg_calculate_flag_v() );
      assign( oldC, mk_armg_calculate_flag_c() );
      assign(res, unop(Iop_Not32, getIRegT(rM)));
      // rD can never be r15
      putIRegT(rD, mkexpr(res), condT);
      setFlags_D1_D2_ND( ARMG_CC_OP_LOGIC, res, oldC, oldV,
                         cond_AND_notInIT_T );
      DIP("mvns r%u, r%u\n", rD, rM);
      goto decode_success;
   }

   case 0x10C:
      /* ---------------- ORRS Rd, Rm ---------------- */
      anOp = Iop_Or32; anOpNm = "orr"; goto and_orr_eor_mul;
   case 0x100:
      /* ---------------- ANDS Rd, Rm ---------------- */
      anOp = Iop_And32; anOpNm = "and"; goto and_orr_eor_mul;
   case 0x101:
      /* ---------------- EORS Rd, Rm ---------------- */
      anOp = Iop_Xor32; anOpNm = "eor"; goto and_orr_eor_mul;
   case 0x10d:
      /* ---------------- MULS Rd, Rm ---------------- */
      anOp = Iop_Mul32; anOpNm = "mul"; goto and_orr_eor_mul;
   and_orr_eor_mul: {
      /* Rd = Rd `op` Rm */
      UInt   rM   = INSN0(5,3);
      UInt   rD   = INSN0(2,0);
      IRTemp res  = newTemp(Ity_I32);
      IRTemp oldV = newTemp(Ity_I32);
      IRTemp oldC = newTemp(Ity_I32);
      assign( oldV, mk_armg_calculate_flag_v() );
      assign( oldC, mk_armg_calculate_flag_c() );
      assign( res, binop(anOp, getIRegT(rD), getIRegT(rM) ));
      // not safe to read guest state after here
      // rD can never be r15
      putIRegT(rD, mkexpr(res), condT);
      setFlags_D1_D2_ND( ARMG_CC_OP_LOGIC, res, oldC, oldV,
                         cond_AND_notInIT_T );
      DIP("%s r%u, r%u\n", anOpNm, rD, rM);
      goto decode_success;
   }

   case 0x10E: {
      /* ---------------- BICS Rd, Rm ---------------- */
      /* Rd = Rd & ~Rm */
      UInt   rM   = INSN0(5,3);
      UInt   rD   = INSN0(2,0);
      IRTemp res  = newTemp(Ity_I32);
      IRTemp oldV = newTemp(Ity_I32);
      IRTemp oldC = newTemp(Ity_I32);
      assign( oldV, mk_armg_calculate_flag_v() );
      assign( oldC, mk_armg_calculate_flag_c() );
      assign( res, binop(Iop_And32, getIRegT(rD),
                                    unop(Iop_Not32, getIRegT(rM) )));
      // not safe to read guest state after here
      // rD can never be r15
      putIRegT(rD, mkexpr(res), condT);
      setFlags_D1_D2_ND( ARMG_CC_OP_LOGIC, res, oldC, oldV,
                         cond_AND_notInIT_T );
      DIP("bics r%u, r%u\n", rD, rM);
      goto decode_success;
   }

   case 0x105: {
      /* ---------------- ADCS Rd, Rm ---------------- */
      /* Rd = Rd + Rm + oldC */
      UInt   rM   = INSN0(5,3);
      UInt   rD   = INSN0(2,0);
      IRTemp argL = newTemp(Ity_I32);
      IRTemp argR = newTemp(Ity_I32);
      IRTemp oldC = newTemp(Ity_I32);
      IRTemp res  = newTemp(Ity_I32);
      assign(argL, getIRegT(rD));
      assign(argR, getIRegT(rM));
      assign(oldC, mk_armg_calculate_flag_c());
      assign(res, binop(Iop_Add32,
                        binop(Iop_Add32, mkexpr(argL), mkexpr(argR)),
                        mkexpr(oldC)));
      // rD can never be r15
      putIRegT(rD, mkexpr(res), condT);
      setFlags_D1_D2_ND( ARMG_CC_OP_ADC, argL, argR, oldC,
                         cond_AND_notInIT_T );
      DIP("adcs r%u, r%u\n", rD, rM);
      goto decode_success;
   }

   case 0x106: {
      /* ---------------- SBCS Rd, Rm ---------------- */
      /* Rd = Rd - Rm - (oldC ^ 1) */
      UInt   rM   = INSN0(5,3);
      UInt   rD   = INSN0(2,0);
      IRTemp argL = newTemp(Ity_I32);
      IRTemp argR = newTemp(Ity_I32);
      IRTemp oldC = newTemp(Ity_I32);
      IRTemp res  = newTemp(Ity_I32);
      assign(argL, getIRegT(rD));
      assign(argR, getIRegT(rM));
      assign(oldC, mk_armg_calculate_flag_c());
      assign(res, binop(Iop_Sub32,
                        binop(Iop_Sub32, mkexpr(argL), mkexpr(argR)),
                        binop(Iop_Xor32, mkexpr(oldC), mkU32(1))));
      // rD can never be r15
      putIRegT(rD, mkexpr(res), condT);
      setFlags_D1_D2_ND( ARMG_CC_OP_SBB, argL, argR, oldC,
                         cond_AND_notInIT_T );
      DIP("sbcs r%u, r%u\n", rD, rM);
      goto decode_success;
   }

   case 0x2CB: {
      /* ---------------- UXTB Rd, Rm ---------------- */
      /* Rd = 8Uto32(Rm) */
      UInt rM = INSN0(5,3);
      UInt rD = INSN0(2,0);
      putIRegT(rD, binop(Iop_And32, getIRegT(rM), mkU32(0xFF)),
                   condT);
      DIP("uxtb r%u, r%u\n", rD, rM);
      goto decode_success;
   }

   case 0x2CA: {
      /* ---------------- UXTH Rd, Rm ---------------- */
      /* Rd = 16Uto32(Rm) */
      UInt rM = INSN0(5,3);
      UInt rD = INSN0(2,0);
      putIRegT(rD, binop(Iop_And32, getIRegT(rM), mkU32(0xFFFF)),
                   condT);
      DIP("uxth r%u, r%u\n", rD, rM);
      goto decode_success;
   }

   case 0x102:   // LSLS
   case 0x103:   // LSRS
   case 0x104:   // ASRS
   case 0x107: { // RORS
      /* ---------------- LSLS Rs, Rd ---------------- */
      /* ---------------- LSRS Rs, Rd ---------------- */
      /* ---------------- ASRS Rs, Rd ---------------- */
      /* ---------------- RORS Rs, Rd ---------------- */
      /* Rd = Rd `op` Rs, and set flags */
      UInt   rS   = INSN0(5,3);
      UInt   rD   = INSN0(2,0);
      IRTemp oldV = newTemp(Ity_I32);
      IRTemp rDt  = newTemp(Ity_I32);
      IRTemp rSt  = newTemp(Ity_I32);
      IRTemp res  = newTemp(Ity_I32);
      IRTemp resC = newTemp(Ity_I32);
      HChar* wot  = "???";
      assign(rSt, getIRegT(rS));
      assign(rDt, getIRegT(rD));
      assign(oldV, mk_armg_calculate_flag_v());
      /* Does not appear to be the standard 'how' encoding. */
      switch (INSN0(15,6)) {
         case 0x102:
            compute_result_and_C_after_LSL_by_reg(
               dis_buf, &res, &resC, rDt, rSt, rD, rS
            );
            wot = "lsl";
            break;
         case 0x103:
            compute_result_and_C_after_LSR_by_reg(
               dis_buf, &res, &resC, rDt, rSt, rD, rS
            );
            wot = "lsr";
            break;
         case 0x104:
            compute_result_and_C_after_ASR_by_reg(
               dis_buf, &res, &resC, rDt, rSt, rD, rS
            );
            wot = "asr";
            break;
         case 0x107:
            compute_result_and_C_after_ROR_by_reg(
               dis_buf, &res, &resC, rDt, rSt, rD, rS
            );
            wot = "ror";
            break;
         default:
            /*NOTREACHED*/vassert(0);
      }
      // not safe to read guest state after this point
      putIRegT(rD, mkexpr(res), condT);
      setFlags_D1_D2_ND( ARMG_CC_OP_LOGIC, res, resC, oldV,
                         cond_AND_notInIT_T );
      DIP("%ss r%u, r%u\n", wot, rS, rD);
      goto decode_success;
   }

   default:
      break; /* examine the next shortest prefix */

   }


   /* ================ 16-bit 15:7 cases ================ */

   switch (INSN0(15,7)) {

   case BITS9(1,0,1,1,0,0,0,0,0): {
      /* ------------ ADD SP, #imm7 * 4 ------------ */
      UInt uimm7 = INSN0(6,0);
      putIRegT(13, binop(Iop_Add32, getIRegT(13), mkU32(uimm7 * 4)),
                   condT);
      DIP("add sp, #%u\n", uimm7 * 4);
      goto decode_success;
   }

   case BITS9(1,0,1,1,0,0,0,0,1): {
      /* ------------ SUB SP, #imm7 * 4 ------------ */
      UInt uimm7 = INSN0(6,0);
      putIRegT(13, binop(Iop_Sub32, getIRegT(13), mkU32(uimm7 * 4)),
                   condT);
      DIP("sub sp, #%u\n", uimm7 * 4);
      goto decode_success;
   }

   case BITS9(0,1,0,0,0,1,1,1,0): {
      /* ---------------- BX rM ---------------- */
      /* Branch to reg, and optionally switch modes.  Reg contains a
         suitably encoded address therefore (w CPSR.T at the bottom).
         Have to special-case r15, as usual. */
      UInt rM = (INSN0(6,6) << 3) | INSN0(5,3);
      if (BITS3(0,0,0) == INSN0(2,0) &&/*atc*/rM != 15) {
         IRTemp dst = newTemp(Ity_I32);
         gen_SIGILL_T_if_in_but_NLI_ITBlock(old_itstate, new_itstate);
         mk_skip_over_T16_if_cond_is_false(condT);
         condT = IRTemp_INVALID;
         // now uncond
         if (rM <= 14) {
            assign( dst, getIRegT(rM) );
         } else {
            break; // ATC
            vassert(rM == 15);
            assign( dst, mkU32(guest_R15_curr_instr_notENC + 4) );
         }
         irsb->next     = mkexpr(dst);
         irsb->jumpkind = Ijk_Boring;
         dres.whatNext  = Dis_StopHere;
         DIP("bx r%u (possibly switch to ARM mode)\n", rM);
         goto decode_success;
      }
      break;
   }

   /* ---------------- BLX rM ---------------- */
   /* Branch and link to interworking address in rM. */
   case BITS9(0,1,0,0,0,1,1,1,1): {
      if (BITS3(0,0,0) == INSN0(2,0)) {
         UInt rM = (INSN0(6,6) << 3) | INSN0(5,3);
         IRTemp dst = newTemp(Ity_I32);
         if (rM <= 14) {
            gen_SIGILL_T_if_in_but_NLI_ITBlock(old_itstate, new_itstate);
            mk_skip_over_T16_if_cond_is_false(condT);
            condT = IRTemp_INVALID;
            // now uncond
            /* We're returning to Thumb code, hence "| 1" */
            assign( dst, getIRegT(rM) );
            putIRegT( 14, mkU32( (guest_R15_curr_instr_notENC + 2) | 1 ),
                          IRTemp_INVALID );
            irsb->next     = mkexpr(dst);
            irsb->jumpkind = Ijk_Boring;
            dres.whatNext  = Dis_StopHere;
            DIP("blx r%u (possibly switch to ARM mode)\n", rM);
            goto decode_success;
         }
         /* else unpredictable, fall through */
      }
      break;
   }

   default:
      break; /* examine the next shortest prefix */

   }


   /* ================ 16-bit 15:8 cases ================ */

   switch (INSN0(15,8)) {

   case BITS8(0,1,0,0,0,1,0,0): {
      /* ---------------- ADD(HI) Rd, Rm ---------------- */
      UInt h1 = INSN0(7,7);
      UInt h2 = INSN0(6,6);
      UInt rM = (h2 << 3) | INSN0(5,3);
      UInt rD = (h1 << 3) | INSN0(2,0);
      //if (h1 == 0 && h2 == 0) { // Original T1 was more restrictive
      if (rD == 15 && rM == 15) {
         // then it's invalid
      } else {
         IRTemp res = newTemp(Ity_I32);
         assign( res, binop(Iop_Add32, getIRegT(rD), getIRegT(rM) ));
         if (rD != 15) {
            putIRegT( rD, mkexpr(res), condT );
         } else {
            /* Only allowed outside or last-in IT block; SIGILL if not so. */
            gen_SIGILL_T_if_in_but_NLI_ITBlock(old_itstate, new_itstate);
            /* jump over insn if not selected */
            mk_skip_over_T16_if_cond_is_false(condT);
            condT = IRTemp_INVALID;
            // now uncond
            /* non-interworking branch */
            irsb->next = binop(Iop_Or32, mkexpr(res), mkU32(1));
            irsb->jumpkind = Ijk_Boring;
            dres.whatNext = Dis_StopHere;
         }
         DIP("add(hi) r%u, r%u\n", rD, rM);
         goto decode_success;
      }
      break;
   }

   case BITS8(0,1,0,0,0,1,0,1): {
      /* ---------------- CMP(HI) Rd, Rm ---------------- */
      UInt h1 = INSN0(7,7);
      UInt h2 = INSN0(6,6);
      UInt rM = (h2 << 3) | INSN0(5,3);
      UInt rN = (h1 << 3) | INSN0(2,0);
      if (h1 != 0 || h2 != 0) {
         IRTemp argL  = newTemp(Ity_I32);
         IRTemp argR  = newTemp(Ity_I32);
         assign( argL, getIRegT(rN) );
         assign( argR, getIRegT(rM) );
         /* Update flags regardless of whether in an IT block or not. */
         setFlags_D1_D2( ARMG_CC_OP_SUB, argL, argR, condT );
         DIP("cmphi r%u, r%u\n", rN, rM);
         goto decode_success;
      }
      break;
   }

   case BITS8(0,1,0,0,0,1,1,0): {
      /* ---------------- MOV(HI) Rd, Rm ---------------- */
      UInt h1 = INSN0(7,7);
      UInt h2 = INSN0(6,6);
      UInt rM = (h2 << 3) | INSN0(5,3);
      UInt rD = (h1 << 3) | INSN0(2,0);
      /* The old ARM ARM seems to disallow the case where both Rd and
         Rm are "low" registers, but newer versions allow it. */
      if (1 /*h1 != 0 || h2 != 0*/) {
         IRTemp val = newTemp(Ity_I32);
         assign( val, getIRegT(rM) );
         if (rD != 15) {
            putIRegT( rD, mkexpr(val), condT );
         } else {
            /* Only allowed outside or last-in IT block; SIGILL if not so. */
            gen_SIGILL_T_if_in_but_NLI_ITBlock(old_itstate, new_itstate);
            /* jump over insn if not selected */
            mk_skip_over_T16_if_cond_is_false(condT);
            condT = IRTemp_INVALID;
            // now uncond
            /* non-interworking branch */
            irsb->next = binop(Iop_Or32, mkexpr(val), mkU32(1));
            irsb->jumpkind = Ijk_Boring;
            dres.whatNext = Dis_StopHere;
         }
         DIP("mov r%u, r%u\n", rD, rM);
         goto decode_success;
      }
      break;
   }

   case BITS8(1,0,1,1,1,1,1,1): {
      /* ---------------- IT (if-then) ---------------- */
      UInt firstcond = INSN0(7,4);
      UInt mask = INSN0(3,0);
      UInt newITSTATE = 0;
      /* This is the ITSTATE represented as described in
         libvex_guest_arm.h.  It is not the ARM ARM representation. */
      UChar c1 = '.';
      UChar c2 = '.';
      UChar c3 = '.';
      Bool valid = compute_ITSTATE( &newITSTATE, &c1, &c2, &c3,
                                    firstcond, mask );
      if (valid && firstcond != 0xF/*NV*/) {
         /* Not allowed in an IT block; SIGILL if so. */
         gen_SIGILL_T_if_in_ITBlock(old_itstate, new_itstate);

         IRTemp t = newTemp(Ity_I32);
         assign(t, mkU32(newITSTATE));
         put_ITSTATE(t);

         DIP("it%c%c%c %s\n", c1, c2, c3, nCC(firstcond));
         goto decode_success;
      }
   }

   case BITS8(1,0,1,1,0,0,0,1):
   case BITS8(1,0,1,1,0,0,1,1):
   case BITS8(1,0,1,1,1,0,0,1):
   case BITS8(1,0,1,1,1,0,1,1): {
      /* ---------------- CB{N}Z ---------------- */
      UInt rN    = INSN0(2,0);
      UInt bOP   = INSN0(11,11);
      UInt imm32 = (INSN0(9,9) << 6) | (INSN0(7,3) << 1);
      gen_SIGILL_T_if_in_ITBlock(old_itstate, new_itstate);
      /* It's a conditional branch forward. */
      IRTemp kond = newTemp(Ity_I1);
      assign( kond, binop(bOP ? Iop_CmpNE32 : Iop_CmpEQ32,
                          getIRegT(rN), mkU32(0)) );

      vassert(0 == (guest_R15_curr_instr_notENC & 1));
      /* Looks like the nearest insn we can branch to is the one after
         next.  That makes sense, as there's no point in being able to
         encode a conditional branch to the next instruction. */
      UInt dst = (guest_R15_curr_instr_notENC + 4 + imm32) | 1;
      stmt(IRStmt_Exit( mkexpr(kond),
                        Ijk_Boring,
                        IRConst_U32(toUInt(dst)) ));
      DIP("cb%s r%u, 0x%x\n", bOP ? "nz" : "z", rN, dst - 1);
      goto decode_success;
   }

   default:
      break; /* examine the next shortest prefix */

   }


   /* ================ 16-bit 15:9 cases ================ */

   switch (INSN0(15,9)) {

   case BITS7(1,0,1,1,0,1,0): {
      /* ---------------- PUSH ---------------- */
      /* This is a bit like STMxx, but way simpler. Complications we
         don't have to deal with:
         * SP being one of the transferred registers
         * direction (increment vs decrement)
         * before-vs-after-ness
      */
      Int  i, nRegs;
      UInt bitR    = INSN0(8,8);
      UInt regList = INSN0(7,0);
      if (bitR) regList |= (1 << 14);
   
      if (regList != 0) {
         /* Since we can't generate a guaranteed non-trapping IR
            sequence, (1) jump over the insn if it is gated false, and
            (2) back out the ITSTATE update. */
         mk_skip_over_T16_if_cond_is_false(condT);
         condT = IRTemp_INVALID;
         put_ITSTATE(old_itstate);
         // now uncond

         nRegs = 0;
         for (i = 0; i < 16; i++) {
            if ((regList & (1 << i)) != 0)
               nRegs++;
         }
         vassert(nRegs >= 1 && nRegs <= 8);

         /* Move SP down first of all, so we're "covered".  And don't
            mess with its alignment. */
         IRTemp newSP = newTemp(Ity_I32);
         assign(newSP, binop(Iop_Sub32, getIRegT(13), mkU32(4 * nRegs)));
         putIRegT(13, mkexpr(newSP), IRTemp_INVALID);

         /* Generate a transfer base address as a forced-aligned
            version of the final SP value. */
         IRTemp base = newTemp(Ity_I32);
         assign(base, binop(Iop_And32, mkexpr(newSP), mkU32(~3)));

         /* Now the transfers */
         nRegs = 0;
         for (i = 0; i < 16; i++) {
            if ((regList & (1 << i)) != 0) {
               storeLE( binop(Iop_Add32, mkexpr(base), mkU32(4 * nRegs)),
                        getIRegT(i) );
               nRegs++;
            }
         }

         /* Reinstate the ITSTATE update. */
         put_ITSTATE(new_itstate);

         DIP("push {%s0x%04x}\n", bitR ? "lr," : "", regList & 0xFF);
         goto decode_success;
      }
      break;
   }

   case BITS7(1,0,1,1,1,1,0): {
      /* ---------------- POP ---------------- */
      Int  i, nRegs;
      UInt bitR    = INSN0(8,8);
      UInt regList = INSN0(7,0);
   
      if (regList != 0 || bitR) {
         /* Since we can't generate a guaranteed non-trapping IR
            sequence, (1) jump over the insn if it is gated false, and
            (2) back out the ITSTATE update. */
         mk_skip_over_T16_if_cond_is_false(condT);
         condT = IRTemp_INVALID;
         put_ITSTATE(old_itstate);
         // now uncond

         nRegs = 0;
         for (i = 0; i < 8; i++) {
            if ((regList & (1 << i)) != 0)
               nRegs++;
         }
         vassert(nRegs >= 0 && nRegs <= 7);
         vassert(bitR == 0 || bitR == 1);

         IRTemp oldSP = newTemp(Ity_I32);
         assign(oldSP, getIRegT(13));

         /* Generate a transfer base address as a forced-aligned
            version of the original SP value. */
         IRTemp base = newTemp(Ity_I32);
         assign(base, binop(Iop_And32, mkexpr(oldSP), mkU32(~3)));

         /* Compute a new value for SP, but don't install it yet, so
            that we're "covered" until all the transfers are done.
            And don't mess with its alignment. */
         IRTemp newSP = newTemp(Ity_I32);
         assign(newSP, binop(Iop_Add32, mkexpr(oldSP),
                                        mkU32(4 * (nRegs + bitR))));

         /* Now the transfers, not including PC */
         nRegs = 0;
         for (i = 0; i < 8; i++) {
            if ((regList & (1 << i)) != 0) {
               putIRegT(i, loadLE( Ity_I32,
                                   binop(Iop_Add32, mkexpr(base),
                                                    mkU32(4 * nRegs))),
                           IRTemp_INVALID );
               nRegs++;
            }
         }

         IRTemp newPC = IRTemp_INVALID;
         if (bitR) {
            newPC = newTemp(Ity_I32);
            assign( newPC, loadLE( Ity_I32,
                                   binop(Iop_Add32, mkexpr(base),
                                                    mkU32(4 * nRegs))));
         }

         /* Now we can safely install the new SP value */
         putIRegT(13, mkexpr(newSP), IRTemp_INVALID);

         /* Reinstate the ITSTATE update. */
         put_ITSTATE(new_itstate);

         /* now, do we also have to do a branch?  If so, it turns out
            that the new PC value is encoded exactly as we need it to
            be -- with CPSR.T in the bottom bit.  So we can simply use
            it as is, no need to mess with it.  Note, therefore, this
            is an interworking return. */
         if (bitR) {
            irsb->next     = mkexpr(newPC);
            irsb->jumpkind = Ijk_Ret;
            dres.whatNext  = Dis_StopHere;
         }

         DIP("pop {%s0x%04x}\n", bitR ? "pc," : "", regList & 0xFF);
         goto decode_success;
      }
      break;
   }

   case BITS7(0,0,0,1,1,1,0):   /* ADDS */
   case BITS7(0,0,0,1,1,1,1): { /* SUBS */
      /* ---------------- ADDS Rd, Rn, #uimm3 ---------------- */
      /* ---------------- SUBS Rd, Rn, #uimm3 ---------------- */
      UInt   uimm3 = INSN0(8,6);
      UInt   rN    = INSN0(5,3);
      UInt   rD    = INSN0(2,0);
      UInt   isSub = INSN0(9,9);
      IRTemp argL  = newTemp(Ity_I32);
      IRTemp argR  = newTemp(Ity_I32);
      assign( argL, getIRegT(rN) );
      assign( argR, mkU32(uimm3) );
      putIRegT(rD, binop(isSub ? Iop_Sub32 : Iop_Add32,
                         mkexpr(argL), mkexpr(argR)),
                   condT);
      setFlags_D1_D2( isSub ? ARMG_CC_OP_SUB : ARMG_CC_OP_ADD,
                      argL, argR, cond_AND_notInIT_T );
      DIP("%s r%u, r%u, #%u\n", isSub ? "subs" : "adds", rD, rN, uimm3);
      goto decode_success;
   }

   case BITS7(0,0,0,1,1,0,0):   /* ADDS */
   case BITS7(0,0,0,1,1,0,1): { /* SUBS */
      /* ---------------- ADDS Rd, Rn, Rm ---------------- */
      /* ---------------- SUBS Rd, Rn, Rm ---------------- */
      UInt   rM    = INSN0(8,6);
      UInt   rN    = INSN0(5,3);
      UInt   rD    = INSN0(2,0);
      UInt   isSub = INSN0(9,9);
      IRTemp argL  = newTemp(Ity_I32);
      IRTemp argR  = newTemp(Ity_I32);
      assign( argL, getIRegT(rN) );
      assign( argR, getIRegT(rM) );
      putIRegT( rD, binop(isSub ? Iop_Sub32 : Iop_Add32,
                          mkexpr(argL), mkexpr(argR)),
                    condT );
      setFlags_D1_D2( isSub ? ARMG_CC_OP_SUB : ARMG_CC_OP_ADD,
                      argL, argR, cond_AND_notInIT_T );
      DIP("%s r%u, r%u, r%u\n", isSub ? "subs" : "adds", rD, rN, rM);
      goto decode_success;
   }

   case BITS7(0,1,0,1,0,0,0):   /* STR */
   case BITS7(0,1,0,1,1,0,0): { /* LDR */
      /* ------------- LDR Rd, [Rn, Rm] ------------- */
      /* ------------- STR Rd, [Rn, Rm] ------------- */
      /* LDR/STR Rd, [Rn + Rm] */
      UInt    rD   = INSN0(2,0);
      UInt    rN   = INSN0(5,3);
      UInt    rM   = INSN0(8,6);
      UInt    isLD = INSN0(11,11);

      mk_skip_over_T16_if_cond_is_false(condT);
      condT = IRTemp_INVALID;
      // now uncond

      IRExpr* ea = binop(Iop_Add32, getIRegT(rN), getIRegT(rM));
      put_ITSTATE(old_itstate); // backout
      if (isLD) {
         putIRegT(rD, loadLE(Ity_I32, ea), IRTemp_INVALID);
      } else {
         storeLE(ea, getIRegT(rD));
      }
      put_ITSTATE(new_itstate); // restore

      DIP("%s r%u, [r%u, r%u]\n", isLD ? "ldr" : "str", rD, rN, rM);
      goto decode_success;
   }

   case BITS7(0,1,0,1,0,0,1):
   case BITS7(0,1,0,1,1,0,1): {
      /* ------------- LDRH Rd, [Rn, Rm] ------------- */
      /* ------------- STRH Rd, [Rn, Rm] ------------- */
      /* LDRH/STRH Rd, [Rn + Rm] */
      UInt    rD   = INSN0(2,0);
      UInt    rN   = INSN0(5,3);
      UInt    rM   = INSN0(8,6);
      UInt    isLD = INSN0(11,11);

      mk_skip_over_T16_if_cond_is_false(condT);
      condT = IRTemp_INVALID;
      // now uncond

      IRExpr* ea = binop(Iop_Add32, getIRegT(rN), getIRegT(rM));
      put_ITSTATE(old_itstate); // backout
      if (isLD) {
         putIRegT(rD, unop(Iop_16Uto32, loadLE(Ity_I16, ea)),
                      IRTemp_INVALID);
      } else {
         storeLE( ea, unop(Iop_32to16, getIRegT(rD)) );
      }
      put_ITSTATE(new_itstate); // restore

      DIP("%sh r%u, [r%u, r%u]\n", isLD ? "ldr" : "str", rD, rN, rM);
      goto decode_success;
   }

   case BITS7(0,1,0,1,1,1,1): {
      /* ------------- LDRSH Rd, [Rn, Rm] ------------- */
      /* LDRSH Rd, [Rn + Rm] */
      UInt    rD = INSN0(2,0);
      UInt    rN = INSN0(5,3);
      UInt    rM = INSN0(8,6);

      mk_skip_over_T16_if_cond_is_false(condT);
      condT = IRTemp_INVALID;
      // now uncond

      IRExpr* ea = binop(Iop_Add32, getIRegT(rN), getIRegT(rM));
      put_ITSTATE(old_itstate); // backout
      putIRegT(rD, unop(Iop_16Sto32, loadLE(Ity_I16, ea)),
                   IRTemp_INVALID);
      put_ITSTATE(new_itstate); // restore

      DIP("ldrsh r%u, [r%u, r%u]\n", rD, rN, rM);
      goto decode_success;
   }

   case BITS7(0,1,0,1,0,1,0):
   case BITS7(0,1,0,1,1,1,0): {
      /* ------------- LDRB Rd, [Rn, Rm] ------------- */
      /* ------------- STRB Rd, [Rn, Rm] ------------- */
      /* LDRB/STRB Rd, [Rn + Rm] */
      UInt    rD   = INSN0(2,0);
      UInt    rN   = INSN0(5,3);
      UInt    rM   = INSN0(8,6);
      UInt    isLD = INSN0(11,11);

      mk_skip_over_T16_if_cond_is_false(condT);
      condT = IRTemp_INVALID;
      // now uncond

      IRExpr* ea = binop(Iop_Add32, getIRegT(rN), getIRegT(rM));
      put_ITSTATE(old_itstate); // backout
      if (isLD) {
         putIRegT(rD, unop(Iop_8Uto32, loadLE(Ity_I8, ea)),
                  IRTemp_INVALID);
      } else {
         storeLE( ea, unop(Iop_32to8, getIRegT(rD)) );
      }
      put_ITSTATE(new_itstate); // restore

      DIP("%sb r%u, [r%u, r%u]\n", isLD ? "ldr" : "str", rD, rN, rM);
      goto decode_success;
   }

   default:
      break; /* examine the next shortest prefix */

   }


   /* ================ 16-bit 15:11 cases ================ */

   switch (INSN0(15,11)) {

   case BITS5(0,0,1,1,0):
   case BITS5(0,0,1,1,1): {
      /* ---------------- ADDS Rn, #uimm8 ---------------- */
      /* ---------------- SUBS Rn, #uimm8 ---------------- */
      UInt   isSub = INSN0(11,11);
      UInt   rN    = INSN0(10,8);
      UInt   uimm8 = INSN0(7,0);
      IRTemp argL  = newTemp(Ity_I32);
      IRTemp argR  = newTemp(Ity_I32);
      assign( argL, getIRegT(rN) );
      assign( argR, mkU32(uimm8) );
      putIRegT( rN, binop(isSub ? Iop_Sub32 : Iop_Add32,
                          mkexpr(argL), mkexpr(argR)), condT );
      setFlags_D1_D2( isSub ? ARMG_CC_OP_SUB : ARMG_CC_OP_ADD,
                      argL, argR, cond_AND_notInIT_T );
      DIP("%s r%u, #%u\n", isSub ? "subs" : "adds", rN, uimm8);
      goto decode_success;
   }

   case BITS5(1,0,1,0,0): {
      /* ---------------- ADD rD, PC, #imm8 * 4 ---------------- */
      /* a.k.a. ADR */
      UInt rD   = INSN0(10,8);
      UInt imm8 = INSN0(7,0);
      putIRegT(rD, binop(Iop_Add32, getIRegT(15), mkU32(imm8 * 4)),
                   condT);
      DIP("add r%u, pc, #%u\n", rD, imm8 * 4);
      goto decode_success;
   }

   case BITS5(1,0,1,0,1): {
      /* ---------------- ADD rD, SP, #imm8 * 4 ---------------- */
      UInt rD   = INSN0(10,8);
      UInt imm8 = INSN0(7,0);
      putIRegT(rD, binop(Iop_Add32, getIRegT(13), mkU32(imm8 * 4)),
                   condT);
      DIP("add r%u, r13, #%u\n", rD, imm8 * 4);
      goto decode_success;
   }

   case BITS5(0,0,1,0,1): {
      /* ---------------- CMP Rn, #uimm8 ---------------- */
      UInt   rN    = INSN0(10,8);
      UInt   uimm8 = INSN0(7,0);
      IRTemp argL  = newTemp(Ity_I32);
      IRTemp argR  = newTemp(Ity_I32);
      assign( argL, getIRegT(rN) );
      assign( argR, mkU32(uimm8) );
      /* Update flags regardless of whether in an IT block or not. */
      setFlags_D1_D2( ARMG_CC_OP_SUB, argL, argR, condT );
      DIP("cmp r%u, #%u\n", rN, uimm8);
      goto decode_success;
   }

   case BITS5(0,0,1,0,0): {
      /* -------------- (T1) MOVS Rn, #uimm8 -------------- */
      UInt   rD    = INSN0(10,8);
      UInt   uimm8 = INSN0(7,0);
      IRTemp oldV  = newTemp(Ity_I32);
      IRTemp oldC  = newTemp(Ity_I32);
      IRTemp res   = newTemp(Ity_I32);
      assign( oldV, mk_armg_calculate_flag_v() );
      assign( oldC, mk_armg_calculate_flag_c() );
      assign( res, mkU32(uimm8) );
      putIRegT(rD, mkexpr(res), condT);
      setFlags_D1_D2_ND( ARMG_CC_OP_LOGIC, res, oldC, oldV,
                         cond_AND_notInIT_T );
      DIP("movs r%u, #%u\n", rD, uimm8);
      goto decode_success;
   }

   case BITS5(0,1,0,0,1): {
      /* ------------- LDR Rd, [PC, #imm8 * 4] ------------- */
      /* LDR Rd, [align4(PC) + imm8 * 4] */
      UInt   rD   = INSN0(10,8);
      UInt   imm8 = INSN0(7,0);
      IRTemp ea   = newTemp(Ity_I32);

      mk_skip_over_T16_if_cond_is_false(condT);
      condT = IRTemp_INVALID;
      // now uncond

      assign(ea, binop(Iop_Add32, 
                       binop(Iop_And32, getIRegT(15), mkU32(~3UL)),
                       mkU32(imm8 * 4)));
      put_ITSTATE(old_itstate); // backout
      putIRegT(rD, loadLE(Ity_I32, mkexpr(ea)),
                   IRTemp_INVALID);
      put_ITSTATE(new_itstate); // restore

      DIP("ldr r%u, [pc, #%u]\n", rD, imm8 * 4);
      goto decode_success;
   }

   case BITS5(0,1,1,0,0):   /* STR */
   case BITS5(0,1,1,0,1): { /* LDR */
      /* ------------- LDR Rd, [Rn, #imm5 * 4] ------------- */
      /* ------------- STR Rd, [Rn, #imm5 * 4] ------------- */
      /* LDR/STR Rd, [Rn + imm5 * 4] */
      UInt    rD   = INSN0(2,0);
      UInt    rN   = INSN0(5,3);
      UInt    imm5 = INSN0(10,6);
      UInt    isLD = INSN0(11,11);

      mk_skip_over_T16_if_cond_is_false(condT);
      condT = IRTemp_INVALID;
      // now uncond

      IRExpr* ea = binop(Iop_Add32, getIRegT(rN), mkU32(imm5 * 4));
      put_ITSTATE(old_itstate); // backout
      if (isLD) {
         putIRegT(rD, loadLE(Ity_I32, ea), IRTemp_INVALID);
      } else {
         storeLE( ea, getIRegT(rD) );
      }
      put_ITSTATE(new_itstate); // restore

      DIP("%s r%u, [r%u, #%u]\n", isLD ? "ldr" : "str", rD, rN, imm5 * 4);
      goto decode_success;
   }

   case BITS5(1,0,0,0,0):   /* STRH */
   case BITS5(1,0,0,0,1): { /* LDRH */
      /* ------------- LDRH Rd, [Rn, #imm5 * 2] ------------- */
      /* ------------- STRH Rd, [Rn, #imm5 * 2] ------------- */
      /* LDRH/STRH Rd, [Rn + imm5 * 2] */
      UInt    rD   = INSN0(2,0);
      UInt    rN   = INSN0(5,3);
      UInt    imm5 = INSN0(10,6);
      UInt    isLD = INSN0(11,11);

      mk_skip_over_T16_if_cond_is_false(condT);
      condT = IRTemp_INVALID;
      // now uncond

      IRExpr* ea = binop(Iop_Add32, getIRegT(rN), mkU32(imm5 * 2));
      put_ITSTATE(old_itstate); // backout
      if (isLD) {
         putIRegT(rD, unop(Iop_16Uto32, loadLE(Ity_I16, ea)),
                  IRTemp_INVALID);
      } else {
         storeLE( ea, unop(Iop_32to16, getIRegT(rD)) );
      }
      put_ITSTATE(new_itstate); // restore

      DIP("%sh r%u, [r%u, #%u]\n", isLD ? "ldr" : "str", rD, rN, imm5 * 2);
      goto decode_success;
   }

   case BITS5(0,1,1,1,0):   /* STRB */
   case BITS5(0,1,1,1,1): { /* LDRB */
      /* ------------- LDRB Rd, [Rn, #imm5] ------------- */
      /* ------------- STRB Rd, [Rn, #imm5] ------------- */
      /* LDRB/STRB Rd, [Rn + imm5] */
      UInt    rD   = INSN0(2,0);
      UInt    rN   = INSN0(5,3);
      UInt    imm5 = INSN0(10,6);
      UInt    isLD = INSN0(11,11);

      mk_skip_over_T16_if_cond_is_false(condT);
      condT = IRTemp_INVALID;
      // now uncond

      IRExpr* ea = binop(Iop_Add32, getIRegT(rN), mkU32(imm5));
      put_ITSTATE(old_itstate); // backout
      if (isLD) {
         putIRegT(rD, unop(Iop_8Uto32, loadLE(Ity_I8, ea)),
                  IRTemp_INVALID);
      } else {
         storeLE( ea, unop(Iop_32to8, getIRegT(rD)) );
      }
      put_ITSTATE(new_itstate); // restore

      DIP("%sb r%u, [r%u, #%u]\n", isLD ? "ldr" : "str", rD, rN, imm5);
      goto decode_success;
   }

   case BITS5(1,0,0,1,0):   /* STR */
   case BITS5(1,0,0,1,1): { /* LDR */
      /* ------------- LDR Rd, [SP, #imm8 * 4] ------------- */
      /* ------------- STR Rd, [SP, #imm8 * 4] ------------- */
      /* LDR/STR Rd, [SP + imm8 * 4] */
      UInt rD    = INSN0(10,8);
      UInt imm8  = INSN0(7,0);
      UInt isLD  = INSN0(11,11);

      mk_skip_over_T16_if_cond_is_false(condT);
      condT = IRTemp_INVALID;
      // now uncond

      IRExpr* ea = binop(Iop_Add32, getIRegT(13), mkU32(imm8 * 4));
      put_ITSTATE(old_itstate); // backout
      if (isLD) {
         putIRegT(rD, loadLE(Ity_I32, ea), IRTemp_INVALID);
      } else {
         storeLE(ea, getIRegT(rD));
      }
      put_ITSTATE(new_itstate); // restore

      DIP("%s r%u, [sp, #%u]\n", isLD ? "ldr" : "str", rD, imm8 * 4);
      goto decode_success;
   }

   case BITS5(1,1,0,0,1): {
      /* ------------- LDMIA Rn!, {reglist} ------------- */
      Int i, nRegs = 0;
      UInt rN   = INSN0(10,8);
      UInt list = INSN0(7,0);
      /* Empty lists aren't allowed. */
      if (list != 0) {
         mk_skip_over_T16_if_cond_is_false(condT);
         condT = IRTemp_INVALID;
         put_ITSTATE(old_itstate);
         // now uncond

         IRTemp oldRn = newTemp(Ity_I32);
         IRTemp base  = newTemp(Ity_I32);
         assign(oldRn, getIRegT(rN));
         assign(base, binop(Iop_And32, mkexpr(oldRn), mkU32(~3UL)));
         for (i = 0; i < 8; i++) {
            if (0 == (list & (1 << i)))
               continue;
            nRegs++;
            putIRegT(
               i, loadLE(Ity_I32,
                         binop(Iop_Add32, mkexpr(base),
                                          mkU32(nRegs * 4 - 4))),
               IRTemp_INVALID
            );
         }
         /* Only do the writeback for rN if it isn't in the list of
            registers to be transferred. */
         if (0 == (list & (1 << rN))) {
            putIRegT(rN,
                     binop(Iop_Add32, mkexpr(oldRn),
                                      mkU32(nRegs * 4)),
                     IRTemp_INVALID
            );
         }

         /* Reinstate the ITSTATE update. */
         put_ITSTATE(new_itstate);

         DIP("ldmia r%u!, {0x%04x}\n", rN, list);
         goto decode_success;
      }
      break;
   }

   case BITS5(1,1,0,0,0): {
      /* ------------- STMIA Rn!, {reglist} ------------- */
      Int i, nRegs = 0;
      UInt rN   = INSN0(10,8);
      UInt list = INSN0(7,0);
      /* Empty lists aren't allowed.  Also, if rN is in the list then
         it must be the lowest numbered register in the list. */
      Bool valid = list != 0;
      if (valid && 0 != (list & (1 << rN))) {
         for (i = 0; i < rN; i++) {
            if (0 != (list & (1 << i)))
               valid = False;
         }
      }
      if (valid) {
         mk_skip_over_T16_if_cond_is_false(condT);
         condT = IRTemp_INVALID;
         put_ITSTATE(old_itstate);
         // now uncond

         IRTemp oldRn = newTemp(Ity_I32);
         IRTemp base = newTemp(Ity_I32);
         assign(oldRn, getIRegT(rN));
         assign(base, binop(Iop_And32, mkexpr(oldRn), mkU32(~3UL)));
         for (i = 0; i < 8; i++) {
            if (0 == (list & (1 << i)))
               continue;
            nRegs++;
            storeLE( binop(Iop_Add32, mkexpr(base), mkU32(nRegs * 4 - 4)),
                     getIRegT(i) );
         }
         /* Always do the writeback. */
         putIRegT(rN,
                  binop(Iop_Add32, mkexpr(oldRn),
                                   mkU32(nRegs * 4)),
                  IRTemp_INVALID);

         /* Reinstate the ITSTATE update. */
         put_ITSTATE(new_itstate);

         DIP("stmia r%u!, {0x%04x}\n", rN, list);
         goto decode_success;
      }
      break;
   }

   case BITS5(0,0,0,0,0):   /* LSLS */
   case BITS5(0,0,0,0,1):   /* LSRS */
   case BITS5(0,0,0,1,0): { /* ASRS */
      /* ---------------- LSLS Rd, Rm, #imm5 ---------------- */
      /* ---------------- LSRS Rd, Rm, #imm5 ---------------- */
      /* ---------------- ASRS Rd, Rm, #imm5 ---------------- */
      UInt   rD   = INSN0(2,0);
      UInt   rM   = INSN0(5,3);
      UInt   imm5 = INSN0(10,6);
      IRTemp res  = newTemp(Ity_I32);
      IRTemp resC = newTemp(Ity_I32);
      IRTemp rMt  = newTemp(Ity_I32);
      IRTemp oldV = newTemp(Ity_I32);
      HChar* wot  = "???";
      assign(rMt, getIRegT(rM));
      assign(oldV, mk_armg_calculate_flag_v());
      /* Looks like INSN0(12,11) are the standard 'how' encoding.
         Could compactify if the ROR case later appears. */
      switch (INSN0(15,11)) {
         case BITS5(0,0,0,0,0):
            compute_result_and_C_after_LSL_by_imm5(
               dis_buf, &res, &resC, rMt, imm5, rM
            );
            wot = "lsl";
            break;
         case BITS5(0,0,0,0,1):
            compute_result_and_C_after_LSR_by_imm5(
               dis_buf, &res, &resC, rMt, imm5, rM
            );
            wot = "lsr";
            break;
         case BITS5(0,0,0,1,0):
            compute_result_and_C_after_ASR_by_imm5(
               dis_buf, &res, &resC, rMt, imm5, rM
            );
            wot = "asr";
            break;
         default:
            /*NOTREACHED*/vassert(0);
      }
      // not safe to read guest state after this point
      putIRegT(rD, mkexpr(res), condT);
      setFlags_D1_D2_ND( ARMG_CC_OP_LOGIC, res, resC, oldV,
                         cond_AND_notInIT_T );
      /* ignore buf and roll our own output */
      DIP("%ss r%u, r%u, #%u\n", wot, rD, rM, imm5);
      goto decode_success;
   }

   case BITS5(1,1,1,0,0): {
      /* ---------------- B #simm11 ---------------- */
      Int  simm11 = INSN0(10,0);
           simm11 = (simm11 << 21) >> 20;
      UInt dst    = simm11 + guest_R15_curr_instr_notENC + 4;
      /* Only allowed outside or last-in IT block; SIGILL if not so. */
      gen_SIGILL_T_if_in_but_NLI_ITBlock(old_itstate, new_itstate);
      // and skip this insn if not selected; being cleverer is too
      // difficult
      mk_skip_over_T16_if_cond_is_false(condT);
      condT = IRTemp_INVALID;
      // now uncond
      irsb->next     = mkU32( dst | 1 /*CPSR.T*/ );
      irsb->jumpkind = Ijk_Boring;
      dres.whatNext  = Dis_StopHere;
      DIP("b 0x%x\n", dst);
      goto decode_success;
   }

   default:
      break; /* examine the next shortest prefix */

   }


   /* ================ 16-bit 15:12 cases ================ */

   switch (INSN0(15,12)) {

   case BITS4(1,1,0,1): {
      /* ---------------- Bcond #simm8 ---------------- */
      UInt cond  = INSN0(11,8);
      Int  simm8 = INSN0(7,0);
           simm8 = (simm8 << 24) >> 23;
      UInt dst   = simm8 + guest_R15_curr_instr_notENC + 4;
      if (cond != ARMCondAL && cond != ARMCondNV) {
         /* Not allowed in an IT block; SIGILL if so. */
         gen_SIGILL_T_if_in_ITBlock(old_itstate, new_itstate);

         IRTemp kondT = newTemp(Ity_I32);
         assign( kondT, mk_armg_calculate_condition(cond) );
         stmt( IRStmt_Exit( unop(Iop_32to1, mkexpr(kondT)),
                            Ijk_Boring,
                            IRConst_U32(dst | 1/*CPSR.T*/) ));
         irsb->next = mkU32( (guest_R15_curr_instr_notENC + 2) 
                             | 1 /*CPSR.T*/ );
         irsb->jumpkind = Ijk_Boring;
         dres.whatNext  = Dis_StopHere;
         DIP("b%s 0x%x\n", nCC(cond), dst);
         goto decode_success;
      }
      break;
   }

   default:
      break; /* hmm, nothing matched */

   }

   /* ----------------------------------------------------------- */
   /* --                                                       -- */
   /* -- Thumb 32-bit integer instructions                     -- */
   /* --                                                       -- */
   /* ----------------------------------------------------------- */

#  define INSN1(_bMax,_bMin)  SLICE_UInt(((UInt)insn1), (_bMax), (_bMin))

   /* second 16 bits of the instruction, if any */
   UShort insn1 = getUShortLittleEndianly( guest_instr+2 );

   anOp   = Iop_INVALID; /* paranoia */
   anOpNm = NULL;        /* paranoia */

   /* Change result defaults to suit 32-bit insns. */
   vassert(dres.whatNext   == Dis_Continue);
   vassert(dres.len        == 2);
   vassert(dres.continueAt == 0);
   dres.len = 4;

   /* ---------------- BL/BLX simm22 ---------------- */
   if (BITS5(1,1,1,1,0) == INSN0(15,11)
       &&  BITS5(1,1,1,0,1) == (INSN1(15,11) & BITS5(1,1,1,0,1))) {
      /* Only allowed outside or last-in IT block; SIGILL if not so. */
      gen_SIGILL_T_if_in_but_NLI_ITBlock(old_itstate, new_itstate);
      // and skip this insn if not selected; being cleverer is too
      // difficult
      mk_skip_over_T32_if_cond_is_false(condT);
      condT = IRTemp_INVALID;
      // now uncond
      UInt isBL = INSN1(12,12);
      UInt hi11 = INSN0(10,0);
      UInt lo11 = INSN1(10,0);
      Int dst = hi11;
      dst = (dst << 21) >> 21; /* sign extend */
      dst = (dst << 12) + (lo11 << 1)
            + guest_R15_curr_instr_notENC + 4;
      /* We're returning to Thumb code, hence "| 1" */
      putIRegT( 14, mkU32( (guest_R15_curr_instr_notENC + 4) | 1 ),
                IRTemp_INVALID);
      if (isBL) {
         /* BL: unconditional T -> T call */
         /* we're calling Thumb code, hence "| 1" */
         irsb->next = mkU32( dst | 1 );
         DIP("bl 0x%x (stay in Thumb mode)\n", dst);
      } else {
         /* BLX: unconditional T -> A call */
         /* we're calling ARM code, hence "& 3" to align to a
            valid ARM insn address */
         irsb->next = mkU32( dst & ~3 );
         DIP("bl 0x%x (switch to ARM mode)\n", dst);
      }
      irsb->jumpkind = Ijk_Call;
      dres.whatNext = Dis_StopHere;
      goto decode_success;
   }

   /* ---------------- {LD,ST}M{IA,DB} ---------------- */
   if (0x3a2 == INSN0(15,6) // {LD,ST}MIA
       || 0x3a4 == INSN0(15,6)) { // {LD,ST}MDB
      UInt bW      = INSN0(5,5); /* writeback Rn ? */
      UInt bL      = INSN0(4,4);
      UInt rN      = INSN0(3,0);
      UInt bP      = INSN1(15,15); /* reglist entry for r15 */
      UInt bM      = INSN1(14,14); /* reglist entry for r14 */
      UInt rLmost  = INSN1(12,0);  /* reglist entry for r0 .. 12 */
      UInt rL13    = INSN1(13,13); /* must be zero */
      UInt regList = 0;
      Bool valid   = True;

      UInt bINC    = 1;
      UInt bBEFORE = 0;
      if (INSN0(15,6) == 0x3a4) {
         bINC    = 0;
         bBEFORE = 1;
      }

      /* detect statically invalid cases, and construct the final
         reglist */
      if (rL13 == 1)
         valid = False;

      if (bL == 1) {
         regList = (bP << 15) | (bM << 14) | rLmost;
         if (rN == 15)                       valid = False;
         if (popcount32(regList) < 2)        valid = False;
         if (bP == 1 && bM == 1)             valid = False;
         if (bW == 1 && (regList & (1<<rN))) valid = False;
      } else {
         regList = (bM << 14) | rLmost;
         if (bP == 1)                        valid = False;
         if (rN == 15)                       valid = False;
         if (popcount32(regList) < 2)        valid = False;
         if (bW == 1 && (regList & (1<<rN))) valid = False;
         if (regList & (1<<rN)) {
            UInt i;
            /* if Rn is in the list, then it must be the
               lowest numbered entry */
            for (i = 0; i < rN; i++) {
               if (regList & (1<<i))
                  valid = False;
            }
         }
      }

      if (valid) {
         if (bL == 1 && bP == 1) {
            // We'll be writing the PC.  Hence:
            /* Only allowed outside or last-in IT block; SIGILL if not so. */
            gen_SIGILL_T_if_in_but_NLI_ITBlock(old_itstate, new_itstate);
         }

         /* Go uncond: */
         mk_skip_over_T32_if_cond_is_false(condT);
         condT = IRTemp_INVALID;
         // now uncond

         /* Generate the IR.  This might generate a write to R15, */
         mk_ldm_stm(False/*!arm*/, rN, bINC, bBEFORE, bW, bL, regList);

         if (bL == 1 && (regList & (1<<15))) {
            // If we wrote to R15, we have an interworking return to
            // deal with.
            irsb->next     = llGetIReg(15);
            irsb->jumpkind = Ijk_Ret;
            dres.whatNext  = Dis_StopHere;
         }

         DIP("%sm%c%c r%u%s, {0x%04x}\n",
              bL == 1 ? "ld" : "st", bINC ? 'i' : 'd', bBEFORE ? 'b' : 'a',
              rN, bW ? "!" : "", regList);

         goto decode_success;
      }
   }

   /* -------------- (T3) ADD{S}.W Rd, Rn, #constT -------------- */
   if (INSN0(15,11) == BITS5(1,1,1,1,0)
       && INSN0(9,5) == BITS5(0,1,0,0,0)
       && INSN1(15,15) == 0) {
      UInt bS = INSN0(4,4);
      UInt rN = INSN0(3,0);
      UInt rD = INSN1(11,8);
      Bool valid = !isBadRegT(rN) && !isBadRegT(rD);
      /* but allow "add.w reg, sp, #constT" */ 
      if (!valid && rN == 13)
         valid = True;
      if (valid) {
         IRTemp argL  = newTemp(Ity_I32);
         IRTemp argR  = newTemp(Ity_I32);
         IRTemp res   = newTemp(Ity_I32);
         UInt   imm32 = thumbExpandImm_from_I0_I1(NULL, insn0, insn1);
         assign(argL, getIRegT(rN));
         assign(argR, mkU32(imm32));
         assign(res,  binop(Iop_Add32, mkexpr(argL), mkexpr(argR)));
         putIRegT(rD, mkexpr(res), condT);
         if (bS == 1)
            setFlags_D1_D2( ARMG_CC_OP_ADD, argL, argR, condT );
         DIP("add%s.w r%u, r%u, #%u\n",
             bS == 1 ? "s" : "", rD, rN, imm32);
         goto decode_success;
      }
   }

   /* ---------------- (T2) CMP.W Rn, #constT ---------------- */
   // Ditto CMN
   if (INSN0(15,11) == BITS5(1,1,1,1,0)
       && INSN0(9,4) == BITS6(0,1,1,0,1,1)
       && INSN1(15,15) == 0
       && INSN1(11,8) == BITS4(1,1,1,1)) {
      UInt rN = INSN0(3,0);
      if (rN != 15) {
         IRTemp argL  = newTemp(Ity_I32);
         IRTemp argR  = newTemp(Ity_I32);
         UInt   imm32 = thumbExpandImm_from_I0_I1(NULL, insn0, insn1);
         assign(argL, getIRegT(rN));
         assign(argR, mkU32(imm32));
         setFlags_D1_D2( ARMG_CC_OP_SUB, argL, argR, condT );
         DIP("cmp.w r%u, #%u\n", rN, imm32);
         goto decode_success;
      }
   }

   /* -------------- (T1) TST.W Rn, #constT -------------- */
   // Ditto TEQ
   if (INSN0(15,11) == BITS5(1,1,1,1,0)
       && INSN0(9,4) == BITS6(0,0,0,0,0,1)
       && INSN1(15,15) == 0
       && INSN1(11,8) == BITS4(1,1,1,1)) {
      UInt rN = INSN0(3,0);
      if (!isBadRegT(rN)) { // yes, really, it's inconsistent with CMP.W
         IRTemp argL  = newTemp(Ity_I32);
         IRTemp argR  = newTemp(Ity_I32);
         IRTemp res   = newTemp(Ity_I32);
         IRTemp oldV  = newTemp(Ity_I32);
         IRTemp oldC  = newTemp(Ity_I32);
         Bool   updC  = False;
         UInt   imm32 = thumbExpandImm_from_I0_I1(&updC, insn0, insn1);
         assign(argL, getIRegT(rN));
         assign(argR, mkU32(imm32));
         assign(res,  binop(Iop_And32, mkexpr(argL), mkexpr(argR)));
         assign( oldV, mk_armg_calculate_flag_v() );
         assign( oldC, updC 
                       ? mkU32((imm32 >> 31) & 1)
                       : mk_armg_calculate_flag_c() );
         setFlags_D1_D2_ND( ARMG_CC_OP_LOGIC, res, oldC, oldV, condT );
         DIP("tst.w r%u, #%u\n", rN, imm32);
         goto decode_success;
      }
   }

   /* -------------- (T3) SUB{S}.W Rd, Rn, #constT -------------- */
   /* -------------- (T3) RSB{S}.W Rd, Rn, #constT -------------- */
   if (INSN0(15,11) == BITS5(1,1,1,1,0)
       && (INSN0(9,5) == BITS5(0,1,1,0,1) // SUB
           || INSN0(9,5) == BITS5(0,1,1,1,0)) // RSB
       && INSN1(15,15) == 0) {
      Bool isRSB = INSN0(9,5) == BITS5(0,1,1,1,0);
      UInt bS    = INSN0(4,4);
      UInt rN    = INSN0(3,0);
      UInt rD    = INSN1(11,8);
      Bool valid = !isBadRegT(rN) && !isBadRegT(rD);
      /* but allow "sub.w sp, sp, #constT" */ 
      if (!valid && !isRSB && rN == 13 && rD == 13)
         valid = True;
      if (valid) {
         IRTemp argL  = newTemp(Ity_I32);
         IRTemp argR  = newTemp(Ity_I32);
         IRTemp res   = newTemp(Ity_I32);
         UInt   imm32 = thumbExpandImm_from_I0_I1(NULL, insn0, insn1);
         assign(argL, getIRegT(rN));
         assign(argR, mkU32(imm32));
         assign(res,  isRSB
                      ? binop(Iop_Sub32, mkexpr(argR), mkexpr(argL))
                      : binop(Iop_Sub32, mkexpr(argL), mkexpr(argR)));
         putIRegT(rD, mkexpr(res), condT);
         if (bS == 1) {
            if (isRSB)
               setFlags_D1_D2( ARMG_CC_OP_SUB, argR, argL, condT );
            else
               setFlags_D1_D2( ARMG_CC_OP_SUB, argL, argR, condT );
         }
         DIP("%s%s.w r%u, r%u, #%u\n",
             isRSB ? "rsb" : "sub", bS == 1 ? "s" : "", rD, rN, imm32);
         goto decode_success;
      }
   }

   /* -------------- (T1) ORR{S}.W Rd, Rn, #constT -------------- */
   /* -------------- (T1) AND{S}.W Rd, Rn, #constT -------------- */
   /* -------------- (T1) BIC{S}.W Rd, Rn, #constT -------------- */
   if (INSN0(15,11) == BITS5(1,1,1,1,0)
       && (   INSN0(9,5) == BITS5(0,0,0,1,0)  // ORR
           || INSN0(9,5) == BITS5(0,0,0,0,0)  // AND
           || INSN0(9,5) == BITS5(0,0,0,0,1)) // BIC
       && INSN1(15,15) == 0) {
      UInt bS = INSN0(4,4);
      UInt rN = INSN0(3,0);
      UInt rD = INSN1(11,8);
      if (!isBadRegT(rN) && !isBadRegT(rD)) {
         Bool   isBIC = False;
         IROp   op    = Iop_INVALID;
         HChar* nm    = "???";
         switch (INSN0(9,5)) {
            case BITS5(0,0,0,0,0): op = Iop_And32; nm = "and"; break;
            case BITS5(0,0,0,1,0): op = Iop_Or32;  nm = "orr"; break;
            case BITS5(0,0,0,0,1): op = Iop_And32; nm = "bic";
                                   isBIC = True; break;
            default: vassert(0);
         }
         IRTemp argL  = newTemp(Ity_I32);
         IRTemp argR  = newTemp(Ity_I32);
         IRTemp res   = newTemp(Ity_I32);
         Bool   updC  = False;
         UInt   imm32 = thumbExpandImm_from_I0_I1(&updC, insn0, insn1);
         assign(argL, getIRegT(rN));
         assign(argR, mkU32(isBIC ? ~imm32 : imm32));
         assign(res,  binop(op, mkexpr(argL), mkexpr(argR)));
         putIRegT(rD, mkexpr(res), condT);
         if (bS) {
            IRTemp oldV = newTemp(Ity_I32);
            IRTemp oldC = newTemp(Ity_I32);
            assign( oldV, mk_armg_calculate_flag_v() );
            assign( oldC, updC 
                          ? mkU32((imm32 >> 31) & 1)
                          : mk_armg_calculate_flag_c() );
            setFlags_D1_D2_ND( ARMG_CC_OP_LOGIC, res, oldC, oldV,
                               condT );
         }
         DIP("%s%s.w r%u, r%u, #%u\n",
             nm, bS == 1 ? "s" : "", rD, rN, imm32);
         goto decode_success;
      }
   }

   /* ---------- (T3) ADD{S}.W Rd, Rn, Rm, {shift} ---------- */
   /* ---------- (T3) SUB{S}.W Rd, Rn, Rm, {shift} ---------- */
   /* ---------- (T3) RSB{S}.W Rd, Rn, Rm, {shift} ---------- */
   if (INSN0(15,9) == BITS7(1,1,1,0,1,0,1)
       && (   INSN0(8,5) == BITS4(1,0,0,0)  // add subopc
           || INSN0(8,5) == BITS4(1,1,0,1)  // sub subopc
           || INSN0(8,5) == BITS4(1,1,1,0)) // rsb subopc
       && INSN1(15,15) == 0) {
      UInt rN = INSN0(3,0);
      UInt rD = INSN1(11,8);
      UInt rM = INSN1(3,0);
      if (!isBadRegT(rD) && !isBadRegT(rN) && !isBadRegT(rM)) {
         UInt bS   = INSN0(4,4);
         UInt imm5 = (INSN1(14,12) << 2) | INSN1(7,6);
         UInt how  = INSN1(5,4);

         Bool   swap = False;
         IROp   op   = Iop_INVALID;
         HChar* nm   = "???";
         switch (INSN0(8,5)) {
            case BITS4(1,0,0,0): op = Iop_Add32; nm = "add"; break;
            case BITS4(1,1,0,1): op = Iop_Sub32; nm = "sub"; break;
            case BITS4(1,1,1,0): op = Iop_Sub32; nm = "rsb"; 
                                 swap = True; break;
            default: vassert(0);
         }

         IRTemp argL = newTemp(Ity_I32);
         assign(argL, getIRegT(rN));

         IRTemp rMt = newTemp(Ity_I32);
         assign(rMt, getIRegT(rM));

         IRTemp argR = newTemp(Ity_I32);
         compute_result_and_C_after_shift_by_imm5(
            dis_buf, &argR, NULL, rMt, how, imm5, rM
         );

         IRTemp res = newTemp(Ity_I32);
         assign(res, swap 
                     ? binop(op, mkexpr(argR), mkexpr(argL))
                     : binop(op, mkexpr(argL), mkexpr(argR)));

         putIRegT(rD, mkexpr(res), condT);
         if (bS) {
            switch (op) {
               case Iop_Add32:
                  setFlags_D1_D2( ARMG_CC_OP_ADD, argL, argR, condT );
                  break;
               case Iop_Sub32:
                  if (swap)
                     setFlags_D1_D2( ARMG_CC_OP_SUB, argR, argL, condT );
                  else
                     setFlags_D1_D2( ARMG_CC_OP_SUB, argL, argR, condT );
                  break;
               default:
                  vassert(0);
            }
         }

         DIP("%s%s.w r%u, r%u, %s\n",
             nm, bS ? "s" : "", rD, rN, dis_buf);
         goto decode_success;
      }
   }

   /* ---------- (T3) AND{S}.W Rd, Rn, Rm, {shift} ---------- */
   /* ---------- (T3) ORR{S}.W Rd, Rn, Rm, {shift} ---------- */
   /* ---------- (T3) EOR{S}.W Rd, Rn, Rm, {shift} ---------- */
   /* ---------- (T3) BIC{S}.W Rd, Rn, Rm, {shift} ---------- */
   if (INSN0(15,9) == BITS7(1,1,1,0,1,0,1)
       && (   INSN0(8,5) == BITS4(0,0,0,0)  // and subopc
           || INSN0(8,5) == BITS4(0,0,1,0)  // orr subopc
           || INSN0(8,5) == BITS4(0,1,0,0)  // eor subopc
           || INSN0(8,5) == BITS4(0,0,0,1)) // bic subopc
       && INSN1(15,15) == 0) {
      UInt rN = INSN0(3,0);
      UInt rD = INSN1(11,8);
      UInt rM = INSN1(3,0);
      if (!isBadRegT(rD) && !isBadRegT(rN) && !isBadRegT(rM)) {
         Bool isBIC = False;
         IROp op    = Iop_INVALID;
         HChar* nm  = "???";
         switch (INSN0(8,5)) {
            case BITS4(0,0,0,0): op = Iop_And32; nm = "and"; break;
            case BITS4(0,0,1,0): op = Iop_Or32;  nm = "orr"; break;
            case BITS4(0,1,0,0): op = Iop_Xor32; nm = "eor"; break;
            case BITS4(0,0,0,1): op = Iop_And32; nm = "bic";
                                 isBIC = True; break;
            default: vassert(0);
         }
         UInt bS   = INSN0(4,4);
         UInt imm5 = (INSN1(14,12) << 2) | INSN1(7,6);
         UInt how  = INSN1(5,4);

         IRTemp rNt = newTemp(Ity_I32);
         assign(rNt, getIRegT(rN));

         IRTemp rMt = newTemp(Ity_I32);
         assign(rMt, getIRegT(rM));

         IRTemp argR = newTemp(Ity_I32);
         IRTemp oldC = bS ? newTemp(Ity_I32) : IRTemp_INVALID;

         compute_result_and_C_after_shift_by_imm5(
            dis_buf, &argR, bS ? &oldC : NULL, rMt, how, imm5, rM
         );

         IRTemp res = newTemp(Ity_I32);
         if (isBIC) {
            vassert(op == Iop_And32);
            assign(res, binop(op, mkexpr(rNt),
                                  unop(Iop_Not32, mkexpr(argR))));
         } else {
            assign(res, binop(op, mkexpr(rNt), mkexpr(argR)));
         }

         putIRegT(rD, mkexpr(res), condT);
         if (bS) {
            IRTemp oldV = newTemp(Ity_I32);
            assign( oldV, mk_armg_calculate_flag_v() );
            setFlags_D1_D2_ND( ARMG_CC_OP_LOGIC, res, oldC, oldV,
                               condT );
         }

         DIP("%s%s.w r%u, r%u, %s\n",
             nm, bS ? "s" : "", rD, rN, dis_buf);
         goto decode_success;
      }
   }

   /* -------------- (T?) LSL{S}.W Rd, Rn, Rm -------------- */
   /* -------------- (T?) LSR{S}.W Rd, Rn, Rm -------------- */
   /* -------------- (T?) ASR{S}.W Rd, Rn, Rm -------------- */
   /* -------------- (T?) ROR{S}.W Rd, Rn, Rm -------------- */
   if (INSN0(15,7) == BITS9(1,1,1,1,1,0,1,0,0)
       && INSN1(15,12) == BITS4(1,1,1,1)
       && INSN1(7,4) == BITS4(0,0,0,0)) {
      UInt how = INSN0(6,5); // standard encoding
      UInt rN  = INSN0(3,0);
      UInt rD  = INSN1(11,8);
      UInt rM  = INSN1(3,0);
      UInt bS  = INSN0(4,4);
      Bool valid = !isBadRegT(rN) && !isBadRegT(rM) && !isBadRegT(rD);
      if (how == 3) valid = False; //ATC
      if (valid) {
         IRTemp rNt    = newTemp(Ity_I32);
         IRTemp rMt    = newTemp(Ity_I32);
         IRTemp res    = newTemp(Ity_I32);
         IRTemp oldC   = bS ? newTemp(Ity_I32) : IRTemp_INVALID;
         IRTemp oldV   = bS ? newTemp(Ity_I32) : IRTemp_INVALID;
         HChar* nms[4] = { "lsl", "lsr", "asr", "ror" };
         HChar* nm     = nms[how];
         assign(rNt, getIRegT(rN));
         assign(rMt, getIRegT(rM));
         compute_result_and_C_after_shift_by_reg(
            dis_buf, &res, bS ? &oldC : NULL,
            rNt, how, rMt, rN, rM
         );
         if (bS)
            assign(oldV, mk_armg_calculate_flag_v());
         putIRegT(rD, mkexpr(res), condT);
         if (bS) {
            setFlags_D1_D2_ND( ARMG_CC_OP_LOGIC, res, oldC, oldV,
                               condT );
         }
         DIP("%s%s.w r%u, r%u, r%u\n",
             nm, bS ? "s" : "", rD, rN, rM);
         goto decode_success;
      }
   }

   /* ------------ (T?) MOV{S}.W Rd, Rn, {shift} ------------ */
   /* ------------ (T?) MVN{S}.W Rd, Rn, {shift} ------------ */
   if ((INSN0(15,0) & 0xFFCF) == 0xEA4F
       && INSN1(15,15) == 0) {
      UInt rD = INSN1(11,8);
      UInt rN = INSN1(3,0);
      if (!isBadRegT(rD) && !isBadRegT(rN)) {
         UInt bS    = INSN0(4,4);
         UInt isMVN = INSN0(5,5);
         UInt imm5  = (INSN1(14,12) << 2) | INSN1(7,6);
         UInt how   = INSN1(5,4);

         IRTemp rNt = newTemp(Ity_I32);
         assign(rNt, getIRegT(rN));

         IRTemp oldRn = newTemp(Ity_I32);
         IRTemp oldC  = bS ? newTemp(Ity_I32) : IRTemp_INVALID;
         compute_result_and_C_after_shift_by_imm5(
            dis_buf, &oldRn, bS ? &oldC : NULL, rNt, how, imm5, rN
         );

         IRTemp res = newTemp(Ity_I32);
         assign(res, isMVN ? unop(Iop_Not32, mkexpr(oldRn))
                           : mkexpr(oldRn));

         putIRegT(rD, mkexpr(res), condT);
         if (bS) {
            IRTemp oldV = newTemp(Ity_I32);
            assign( oldV, mk_armg_calculate_flag_v() );
            setFlags_D1_D2_ND( ARMG_CC_OP_LOGIC, res, oldC, oldV, condT);
         }
         DIP("%s%s.w r%u, %s\n",
             isMVN ? "mvn" : "mov", bS ? "s" : "", rD, dis_buf);
         goto decode_success;
      }
   }

   /* -------------- (T?) TST.W Rn, Rm, {shift} -------------- */
   // Ditto TEQ
   if (INSN0(15,9) == BITS7(1,1,1,0,1,0,1)
       && INSN0(8,4) == BITS5(0,0,0,0,1) // TEQ: 01001
       && INSN1(15,15) == 0
       && INSN1(11,8) == BITS4(1,1,1,1)) {
      UInt rN = INSN0(3,0);
      UInt rM = INSN1(3,0);
      if (!isBadRegT(rN) && !isBadRegT(rM)) {
         UInt how  = INSN1(5,4);
         UInt imm5 = (INSN1(14,12) << 2) | INSN1(7,6);

         IRTemp argL = newTemp(Ity_I32);
         assign(argL, getIRegT(rN));

         IRTemp rMt = newTemp(Ity_I32);
         assign(rMt, getIRegT(rM));

         IRTemp argR = newTemp(Ity_I32);
         IRTemp oldC = newTemp(Ity_I32);
         compute_result_and_C_after_shift_by_imm5(
            dis_buf, &argR, &oldC, rMt, how, imm5, rM
         );

         IRTemp oldV = newTemp(Ity_I32);
         assign( oldV, mk_armg_calculate_flag_v() );

         IRTemp res = newTemp(Ity_I32);
         assign(res, binop(Iop_And32, mkexpr(argL), mkexpr(argR)));

         setFlags_D1_D2_ND( ARMG_CC_OP_LOGIC, res, oldC, oldV,
                            condT );
         DIP("tst.w r%u, %s\n", rN, dis_buf);
         goto decode_success;
      }
   }

   /* -------------- (T?) CMP.W Rn, Rm, {shift} -------------- */
   // Ditto CMN
   if (INSN0(15,9) == BITS7(1,1,1,0,1,0,1)
       && INSN0(8,4) == BITS5(1,1,0,1,1) // CMN: 10001
       && INSN1(15,15) == 0
       && INSN1(11,8) == BITS4(1,1,1,1)) {
      UInt rN = INSN0(3,0);
      UInt rM = INSN1(3,0);
      if (!isBadRegT(rN) && !isBadRegT(rM)) {
         UInt how  = INSN1(5,4);
         UInt imm5 = (INSN1(14,12) << 2) | INSN1(7,6);

         IRTemp argL = newTemp(Ity_I32);
         assign(argL, getIRegT(rN));

         IRTemp rMt = newTemp(Ity_I32);
         assign(rMt, getIRegT(rM));

         IRTemp argR = newTemp(Ity_I32);
         compute_result_and_C_after_shift_by_imm5(
            dis_buf, &argR, NULL, rMt, how, imm5, rM
         );

         setFlags_D1_D2( ARMG_CC_OP_SUB, argL, argR, condT );

         DIP("cmp.w r%u, %s\n", rN, dis_buf);
         goto decode_success;
      }
   }

   /* -------------- (T2) MOV{S}.W Rd, #constT -------------- */
   /* -------------- (T2) MVN{S}.W Rd, #constT -------------- */
   if (INSN0(15,11) == BITS5(1,1,1,1,0)
       && (   INSN0(9,5) == BITS5(0,0,0,1,0)  // MOV
           || INSN0(9,5) == BITS5(0,0,0,1,1)) // MVN
       && INSN0(3,0) == BITS4(1,1,1,1)
       && INSN1(15,15) == 0) {
      UInt rD = INSN1(11,8);
      if (!isBadRegT(rD)) {
         Bool   updC  = False;
         UInt   bS    = INSN0(4,4);
         Bool   isMVN = INSN0(5,5) == 1;
         UInt   imm32 = thumbExpandImm_from_I0_I1(&updC, insn0, insn1);
         IRTemp res   = newTemp(Ity_I32);
         assign(res, mkU32(isMVN ? ~imm32 : imm32));
         putIRegT(rD, mkexpr(res), condT);
         if (bS) {
            IRTemp oldV = newTemp(Ity_I32);
            IRTemp oldC = newTemp(Ity_I32);
            assign( oldV, mk_armg_calculate_flag_v() );
            assign( oldC, updC 
                          ? mkU32((imm32 >> 31) & 1)
                          : mk_armg_calculate_flag_c() );
            setFlags_D1_D2_ND( ARMG_CC_OP_LOGIC, res, oldC, oldV,
                               condT );
         }
         DIP("%s%s.w r%u, #%u\n",
             isMVN ? "mvn" : "mov", bS ? "s" : "", rD, imm32);
         goto decode_success;
      }
   }

   /* -------------- (T3) MOVW Rd, #imm16 -------------- */
   if (INSN0(15,11) == BITS5(1,1,1,1,0)
       && INSN0(9,4) == BITS6(1,0,0,1,0,0)
       && INSN1(15,15) == 0) {
      UInt rD = INSN1(11,8);
      if (!isBadRegT(rD)) {
         UInt imm16 = (INSN0(3,0) << 12) | (INSN0(10,10) << 11)
                      | (INSN1(14,12) << 8) | INSN1(7,0);
         putIRegT(rD, mkU32(imm16), condT);
         DIP("movw r%u, #%u\n", rD, imm16);
         goto decode_success;
      }
   }

   /* ---------------- MOVT Rd, #imm16 ---------------- */
   if (INSN0(15,11) == BITS5(1,1,1,1,0)
       && INSN0(9,4) == BITS6(1,0,1,1,0,0)
       && INSN1(15,15) == 0) {
      UInt rD = INSN1(11,8);
      if (!isBadRegT(rD)) {
         UInt imm16 = (INSN0(3,0) << 12) | (INSN0(10,10) << 11)
                      | (INSN1(14,12) << 8) | INSN1(7,0);
         IRTemp res = newTemp(Ity_I32);
         assign(res,
                binop(Iop_Or32,
                      binop(Iop_And32, getIRegT(rD), mkU32(0xFFFF)),
                      mkU32(imm16 << 16)));
         putIRegT(rD, mkexpr(res), condT);
         DIP("movt r%u, #%u\n", rD, imm16);
         goto decode_success;
      }
   }

   /* ---------------- LD/ST reg+/-#imm8 ---------------- */
   /* Loads and stores of the form:
         op  Rt, [Rn, #-imm8]      or
         op  Rt, [Rn], #+/-imm8    or
         op  Rt, [Rn, #+/-imm8]!  
      where op is one of
         ldrb ldrh ldr  ldrsb ldrsh
         strb strh str
   */
   if (INSN0(15,9) == BITS7(1,1,1,1,1,0,0) && INSN1(11,11) == 1) {
      Bool   valid  = True;
      Bool   syned  = False;
      Bool   isST   = False;
      IRType ty     = Ity_I8;
      HChar* nm     = "???";

      switch (INSN0(8,4)) {
         case BITS5(0,0,0,0,0):   // strb
            nm = "strb"; isST = True; break;
         case BITS5(0,0,0,0,1):   // ldrb
            nm = "ldrb"; break;
         case BITS5(1,0,0,0,1):   // ldrsb
            nm = "ldrsb"; syned = True; break;
         case BITS5(0,0,0,1,0):   // strh
            nm = "strh"; ty = Ity_I16; isST = True; break;
         case BITS5(0,0,0,1,1):   // ldrh
            nm = "ldrh"; ty = Ity_I16; break;
         case BITS5(1,0,0,1,1):   // ldrsh
            nm = "ldrsh"; ty = Ity_I16; syned = True; break;
         case BITS5(0,0,1,0,0):   // str
            nm = "str"; ty = Ity_I32; isST = True; break;
         case BITS5(0,0,1,0,1):
            nm = "ldr"; ty = Ity_I32; break;  // ldr
         default:
            valid = False; break;
      }

      UInt rN      = INSN0(3,0);
      UInt rT      = INSN1(15,12);
      UInt bP      = INSN1(10,10);
      UInt bU      = INSN1(9,9);
      UInt bW      = INSN1(8,8);
      UInt imm8    = INSN1(7,0);
      Bool loadsPC = False;

      if (valid) {
         if (bP == 1 && bU == 1 && bW == 0)
            valid = False;
         if (bP == 0 && bW == 0)
            valid = False;
         if (rN == 15)
            valid = False;
         if (bW == 1 && rN == rT)
            valid = False;
         if (ty == Ity_I8 || ty == Ity_I16) {
            if (isBadRegT(rT))
               valid = False;
         } else {
            /* ty == Ity_I32 */
            if (isST && rT == 15)
               valid = False;
            if (!isST && rT == 15)
               loadsPC = True;
         }
      }

      if (valid) {
         // if it's a branch, it can't happen in the middle of an IT block
         if (loadsPC)
            gen_SIGILL_T_if_in_but_NLI_ITBlock(old_itstate, new_itstate);
         // go uncond
         mk_skip_over_T32_if_cond_is_false(condT);
         condT = IRTemp_INVALID;
         // now uncond

         IRTemp preAddr = newTemp(Ity_I32);
         assign(preAddr, getIRegT(rN));

         IRTemp postAddr = newTemp(Ity_I32);
         assign(postAddr, binop(bU == 1 ? Iop_Add32 : Iop_Sub32,
                                mkexpr(preAddr), mkU32(imm8)));

         IRTemp transAddr = bP == 1 ? postAddr : preAddr;

         if (isST) {
            IRTemp oldRt = newTemp(Ity_I32);
            assign(oldRt, getIRegT(rT));
            switch (ty) {
               case Ity_I8:
                  storeLE(mkexpr(transAddr),
                                 unop(Iop_32to8, mkexpr(oldRt)));
                  break;
               case Ity_I16:
                  storeLE(mkexpr(transAddr),
                          unop(Iop_32to16, mkexpr(oldRt)));
                  break;
              case Ity_I32:
                  storeLE(mkexpr(transAddr), mkexpr(oldRt));
                  break;
              default:
                 vassert(0);
            }
         } else {
            IRTemp newRt = newTemp(Ity_I32);
            IROp   widen = Iop_INVALID;
            switch (ty) {
               case Ity_I8:
                  widen = syned ? Iop_8Sto32 : Iop_8Uto32; break;
               case Ity_I16:
                  widen = syned ? Iop_16Sto32 : Iop_16Uto32; break;
               case Ity_I32:
                  break;
               default:
                  vassert(0);
            }
            if (widen == Iop_INVALID) {
               assign(newRt, loadLE(ty, mkexpr(transAddr)));
            } else {
               assign(newRt, unop(widen, loadLE(ty, mkexpr(transAddr))));
            }
            putIRegT(rT, mkexpr(newRt), IRTemp_INVALID);

            if (loadsPC) {
               /* Presumably this is an interworking branch. */
               irsb->next = mkexpr(newRt);
               irsb->jumpkind = Ijk_Boring;  /* or _Ret ? */
               dres.whatNext  = Dis_StopHere;
            }
         }

         if (bW == 1) {
            putIRegT(rN, mkexpr(postAddr), IRTemp_INVALID);
         }

         if (bP == 1 && bW == 0) {
            DIP("%s.w r%u, [r%u, #%c%u]\n",
                nm, rT, rN, bU ? '+' : '-', imm8);
         }
         else if (bP == 1 && bW == 1) {
            DIP("%s.w r%u, [r%u, #%c%u]!\n",
                nm, rT, rN, bU ? '+' : '-', imm8);
         }
         else {
            vassert(bP == 0 && bW == 1);
            DIP("%s.w r%u, [r%u], #%c%u\n",
                nm, rT, rN, bU ? '+' : '-', imm8);
         }

         goto decode_success;
      }
   }

   /* ------------- LD/ST reg+(reg<<imm2) ------------- */
   /* Loads and stores of the form:
         op  Rt, [Rn, Rm, LSL #imm8]
      where op is one of
         ldrb ldrh ldr  ldrsb ldrsh
         strb strh str
   */
   if (INSN0(15,9) == BITS7(1,1,1,1,1,0,0)
       && INSN1(11,6) == BITS6(0,0,0,0,0,0)) {
      Bool   valid  = True;
      Bool   syned  = False;
      Bool   isST   = False;
      IRType ty     = Ity_I8;
      HChar* nm     = "???";

      switch (INSN0(8,4)) {
         case BITS5(0,0,0,0,0):   // strb
            nm = "strb"; isST = True; break;
         case BITS5(0,0,0,0,1):   // ldrb
            nm = "ldrb"; break;
         case BITS5(1,0,0,0,1):   // ldrsb
            nm = "ldrsb"; syned = True; break;
         case BITS5(0,0,0,1,0):   // strh
            nm = "strh"; ty = Ity_I16; isST = True; break;
         case BITS5(0,0,0,1,1):   // ldrh
            nm = "ldrh"; ty = Ity_I16; break;
         case BITS5(1,0,0,1,1):   // ldrsh
            nm = "ldrsh"; ty = Ity_I16; syned = True; break;
         case BITS5(0,0,1,0,0):   // str
            nm = "str"; ty = Ity_I32; isST = True; break;
         case BITS5(0,0,1,0,1):
            nm = "ldr"; ty = Ity_I32; break;  // ldr
         default:
            valid = False; break;
      }

      UInt rN      = INSN0(3,0);
      UInt rM      = INSN1(3,0);
      UInt rT      = INSN1(15,12);
      UInt imm2    = INSN1(5,4);
      Bool loadsPC = False;

      if (ty == Ity_I8 || ty == Ity_I16) {
         /* all 8- and 16-bit load and store cases have the
            same exclusion set. */
         if (rN == 15 || isBadRegT(rT) || isBadRegT(rM))
            valid = False;
      } else {
         vassert(ty == Ity_I32);
         if (rN == 15 || isBadRegT(rM))
            valid = False;
         if (isST && rT == 15)
            valid = False;
         /* If it is a load and rT is 15, that's only allowable if we
            not in an IT block, or are the last in it.  Need to insert
            a dynamic check for that. */
         if (!isST && rT == 15)
            loadsPC = True;
      }

      if (valid) {
         // if it's a branch, it can't happen in the middle of an IT block
         if (loadsPC)
            gen_SIGILL_T_if_in_but_NLI_ITBlock(old_itstate, new_itstate);
         // go uncond
         mk_skip_over_T32_if_cond_is_false(condT);
         condT = IRTemp_INVALID;
         // now uncond

         IRTemp transAddr = newTemp(Ity_I32);
         assign(transAddr,
                binop( Iop_Add32,
                       getIRegT(rN),
                       binop(Iop_Shl32, getIRegT(rM), mkU8(imm2)) ));

         if (isST) {
            IRTemp oldRt = newTemp(Ity_I32);
            assign(oldRt, getIRegT(rT));
            switch (ty) {
               case Ity_I8:
                  storeLE(mkexpr(transAddr),
                                 unop(Iop_32to8, mkexpr(oldRt)));
                  break;
               case Ity_I16:
                  storeLE(mkexpr(transAddr),
                          unop(Iop_32to16, mkexpr(oldRt)));
                  break;
              case Ity_I32:
                  storeLE(mkexpr(transAddr), mkexpr(oldRt));
                  break;
              default:
                 vassert(0);
            }
         } else {
            IRTemp newRt = newTemp(Ity_I32);
            IROp   widen = Iop_INVALID;
            switch (ty) {
               case Ity_I8:
                  widen = syned ? Iop_8Sto32 : Iop_8Uto32; break;
               case Ity_I16:
                  widen = syned ? Iop_16Sto32 : Iop_16Uto32; break;
               case Ity_I32:
                  break;
               default:
                  vassert(0);
            }
            if (widen == Iop_INVALID) {
               assign(newRt, loadLE(ty, mkexpr(transAddr)));
            } else {
               assign(newRt, unop(widen, loadLE(ty, mkexpr(transAddr))));
            }

            /* If we're loading the PC, putIRegT will assert.  So go
               direct via llPutIReg.  In all other cases use putIRegT
               as it is safer (although could simply use llPutIReg for
               _all_ cases here.) */
            if (loadsPC) {
               vassert(rT == 15);
               llPutIReg(rT, mkexpr(newRt));
            } else {
               putIRegT(rT, mkexpr(newRt), IRTemp_INVALID);
            }

            if (loadsPC) {
               /* Presumably this is an interworking branch. */
               irsb->next = mkexpr(newRt);
               irsb->jumpkind = Ijk_Boring;  /* or _Ret ? */
               dres.whatNext  = Dis_StopHere;
            }
         }

         DIP("%s.w r%u, [r%u, r%u, LSL #%u]\n",
             nm, rT, rN, rM, imm2);

         goto decode_success;
      }
   }

   /* --------------- LD/ST reg+imm12 --------------- */
   /* Loads and stores of the form:
         op  Rt, [Rn, +#imm12]
      where op is one of
         ldrb ldrh ldr  ldrsb ldrsh
         strb strh str
   */
   if (INSN0(15,9) == BITS7(1,1,1,1,1,0,0)) {
      Bool   valid  = True;
      Bool   syned  = False;
      Bool   isST   = False;
      IRType ty     = Ity_I8;
      HChar* nm     = "???";

      switch (INSN0(8,4)) {
         case BITS5(0,1,0,0,0):   // strb
            nm = "strb"; isST = True; break;
         case BITS5(0,1,0,0,1):   // ldrb
            nm = "ldrb"; break;
         case BITS5(1,1,0,0,1):   // ldrsb
            nm = "ldrsb"; syned = True; break;
         case BITS5(0,1,0,1,0):   // strh
            nm = "strh"; ty = Ity_I16; isST = True; break;
         case BITS5(0,1,0,1,1):   // ldrh
            nm = "ldrh"; ty = Ity_I16; break;
         case BITS5(1,1,0,1,1):   // ldrsh
            nm = "ldrsh"; ty = Ity_I16; syned = True; break;
         case BITS5(0,1,1,0,0):   // str
            nm = "str"; ty = Ity_I32; isST = True; break;
         case BITS5(0,1,1,0,1):
            nm = "ldr"; ty = Ity_I32; break;  // ldr
         default:
            valid = False; break;
      }

      UInt rN      = INSN0(3,0);
      UInt rT      = INSN1(15,12);
      UInt imm12   = INSN1(11,0);
      Bool loadsPC = False;

      if (ty == Ity_I8 || ty == Ity_I16) {
         /* all 8- and 16-bit load and store cases have the
            same exclusion set. */
         if (rN == 15 || isBadRegT(rT))
            valid = False;
      } else {
         vassert(ty == Ity_I32);
         if (isST) {
            if (rN == 15 || rT == 15)
               valid = False;
         } else {
            /* For a 32-bit load, rT == 15 is only allowable if we not
               in an IT block, or are the last in it.  Need to insert
               a dynamic check for that.  Also, in this particular
               case, rN == 15 is allowable.  In this case however, the
               value obtained for rN is (apparently)
               "word-align(address of current insn + 4)". */
            if (rT == 15)
               loadsPC = True;
         }
      }

      if (valid) {
         // if it's a branch, it can't happen in the middle of an IT block
         if (loadsPC)
            gen_SIGILL_T_if_in_but_NLI_ITBlock(old_itstate, new_itstate);
         // go uncond
         mk_skip_over_T32_if_cond_is_false(condT);
         condT = IRTemp_INVALID;
         // now uncond

         IRTemp rNt = newTemp(Ity_I32);
         if (rN == 15) {
            vassert(ty == Ity_I32 && !isST);
            assign(rNt, binop(Iop_And32, getIRegT(rN), mkU32(~3)));
         } else {
            assign(rNt, getIRegT(rN));
         }

         IRTemp transAddr = newTemp(Ity_I32);
         assign(transAddr,
                binop( Iop_Add32, mkexpr(rNt), mkU32(imm12) ));

         if (isST) {
            IRTemp oldRt = newTemp(Ity_I32);
            assign(oldRt, getIRegT(rT));
            switch (ty) {
               case Ity_I8:
                  storeLE(mkexpr(transAddr),
                                 unop(Iop_32to8, mkexpr(oldRt)));
                  break;
               case Ity_I16:
                  storeLE(mkexpr(transAddr),
                          unop(Iop_32to16, mkexpr(oldRt)));
                  break;
              case Ity_I32:
                  storeLE(mkexpr(transAddr), mkexpr(oldRt));
                  break;
              default:
                 vassert(0);
            }
         } else {
            IRTemp newRt = newTemp(Ity_I32);
            IROp   widen = Iop_INVALID;
            switch (ty) {
               case Ity_I8:
                  widen = syned ? Iop_8Sto32 : Iop_8Uto32; break;
               case Ity_I16:
                  widen = syned ? Iop_16Sto32 : Iop_16Uto32; break;
               case Ity_I32:
                  break;
               default:
                  vassert(0);
            }
            if (widen == Iop_INVALID) {
               assign(newRt, loadLE(ty, mkexpr(transAddr)));
            } else {
               assign(newRt, unop(widen, loadLE(ty, mkexpr(transAddr))));
            }
            putIRegT(rT, mkexpr(newRt), IRTemp_INVALID);

            if (loadsPC) {
               /* Presumably this is an interworking branch. */
               irsb->next = mkexpr(newRt);
               irsb->jumpkind = Ijk_Boring;  /* or _Ret ? */
               dres.whatNext  = Dis_StopHere;
            }
         }

         DIP("%s.w r%u, [r%u, +#%u]\n", nm, rT, rN, imm12);

         goto decode_success;
      }
   }

   /* -------------- LDRD/STRD reg+/-#imm8 -------------- */
   /* Doubleword loads and stores of the form:
         ldrd/strd  Rt, Rt2, [Rn, #-imm8]      or
         ldrd/strd  Rt, Rt2, [Rn], #+/-imm8    or
         ldrd/strd  Rt, Rt2, [Rn, #+/-imm8]!  
   */
   if (INSN0(15,9) == BITS7(1,1,1,0,1,0,0) && INSN0(6,6) == 1) {
      UInt bP   = INSN0(8,8);
      UInt bU   = INSN0(7,7);
      UInt bW   = INSN0(5,5);
      UInt bL   = INSN0(4,4);  // 1: load  0: store
      UInt rN   = INSN0(3,0);
      UInt rT   = INSN1(15,12);
      UInt rT2  = INSN1(11,8);
      UInt imm8 = INSN1(7,0);

      Bool valid = True;
      if (bP == 0 && bW == 0)                 valid = False;
      if (bW == 1 && (rN == rT || rN == rT2)) valid = False;
      if (isBadRegT(rT) || isBadRegT(rT2))    valid = False;
      if (rN == 15)                           valid = False;
      if (bL == 1 && rT == rT2)               valid = False;

      if (valid) {
         // go uncond
         mk_skip_over_T32_if_cond_is_false(condT);
         condT = IRTemp_INVALID;
         // now uncond

         IRTemp preAddr = newTemp(Ity_I32);
         assign(preAddr, getIRegT(rN));

         IRTemp postAddr = newTemp(Ity_I32);
         assign(postAddr, binop(bU == 1 ? Iop_Add32 : Iop_Sub32,
                                mkexpr(preAddr), mkU32(imm8 << 2)));

         IRTemp transAddr = bP == 1 ? postAddr : preAddr;

         if (bL == 0) {
            IRTemp oldRt  = newTemp(Ity_I32);
            IRTemp oldRt2 = newTemp(Ity_I32);
            assign(oldRt,  getIRegT(rT));
            assign(oldRt2, getIRegT(rT2));
            storeLE(mkexpr(transAddr),
                    mkexpr(oldRt));
            storeLE(binop(Iop_Add32, mkexpr(transAddr), mkU32(4)),
                    mkexpr(oldRt2));
         } else {
            IRTemp newRt  = newTemp(Ity_I32);
            IRTemp newRt2 = newTemp(Ity_I32);
            assign(newRt,
                   loadLE(Ity_I32,
                          mkexpr(transAddr)));
            assign(newRt2,
                   loadLE(Ity_I32,
                          binop(Iop_Add32, mkexpr(transAddr), mkU32(4))));
            putIRegT(rT,  mkexpr(newRt), IRTemp_INVALID);
            putIRegT(rT2, mkexpr(newRt2), IRTemp_INVALID);
         }

         if (bW == 1) {
            putIRegT(rN, mkexpr(postAddr), IRTemp_INVALID);
         }

         HChar* nm = bL ? "ldrd" : "strd";

         if (bP == 1 && bW == 0) {
            DIP("%s.w r%u, r%u, [r%u, #%c%u]\n",
                nm, rT, rT2, rN, bU ? '+' : '-', imm8 << 2);
         }
         else if (bP == 1 && bW == 1) {
            DIP("%s.w r%u, r%u, [r%u, #%c%u]!\n",
                nm, rT, rT2, rN, bU ? '+' : '-', imm8 << 2);
         }
         else {
            vassert(bP == 0 && bW == 1);
            DIP("%s.w r%u, r%u, [r%u], #%c%u\n",
                nm, rT, rT2, rN, bU ? '+' : '-', imm8 << 2);
         }

         goto decode_success;
      }
   }

   /* -------------- (T3) Bcond.W label -------------- */
   /* This variant carries its own condition, so can't be part of an
      IT block ... */
   if (INSN0(15,11) == BITS5(1,1,1,1,0)
       && INSN1(15,14) == BITS2(1,0)
       && INSN1(12,12) == 0) {
      UInt cond = INSN0(9,6);
      if (cond != ARMCondAL && cond != ARMCondNV) {
         Int simm21
            =   (INSN0(10,10) << (1 + 1 + 6 + 11 + 1))
              | (INSN1(11,11) << (1 + 6 + 11 + 1))
              | (INSN1(13,13) << (6 + 11 + 1))
              | (INSN0(5,0)   << (11 + 1))
              | (INSN1(10,0)  << 1);
         simm21 = (simm21 << 11) >> 11;

         vassert(0 == (guest_R15_curr_instr_notENC & 1));
         UInt dst = simm21 + guest_R15_curr_instr_notENC + 4;

         /* Not allowed in an IT block; SIGILL if so. */
         gen_SIGILL_T_if_in_ITBlock(old_itstate, new_itstate);

         IRTemp kondT = newTemp(Ity_I32);
         assign( kondT, mk_armg_calculate_condition(cond) );
         stmt( IRStmt_Exit( unop(Iop_32to1, mkexpr(kondT)),
                            Ijk_Boring,
                            IRConst_U32(dst | 1/*CPSR.T*/) ));
         irsb->next = mkU32( (guest_R15_curr_instr_notENC + 4) 
                             | 1 /*CPSR.T*/ );
         irsb->jumpkind = Ijk_Boring;
         dres.whatNext  = Dis_StopHere;
         DIP("b%s.w 0x%x\n", nCC(cond), dst);
         goto decode_success;
      }
   }

   /* ---------------- (T4) B.W label ---------------- */
   /* ... whereas this variant doesn't carry its own condition, so it
      has to be either unconditional or the conditional by virtue of
      being the last in an IT block.  The upside is that there's 4
      more bits available for the jump offset, so it has a 16-times
      greater branch range than the T3 variant. */
   if (INSN0(15,11) == BITS5(1,1,1,1,0)
       && INSN1(15,14) == BITS2(1,0)
       && INSN1(12,12) == 1) {
      if (1) {
         UInt bS  = INSN0(10,10);
         UInt bJ1 = INSN1(13,13);
         UInt bJ2 = INSN1(11,11);
         UInt bI1 = 1 ^ (bJ1 ^ bS);
         UInt bI2 = 1 ^ (bJ2 ^ bS);
         Int simm25
            =   (bS          << (1 + 1 + 10 + 11 + 1))
              | (bI1         << (1 + 10 + 11 + 1))
              | (bI2         << (10 + 11 + 1))
              | (INSN0(9,0)  << (11 + 1))
              | (INSN1(10,0) << 1);
         simm25 = (simm25 << 7) >> 7;

         vassert(0 == (guest_R15_curr_instr_notENC & 1));
         UInt dst = simm25 + guest_R15_curr_instr_notENC + 4;

         /* If in an IT block, must be the last insn. */
         gen_SIGILL_T_if_in_but_NLI_ITBlock(old_itstate, new_itstate);

         // go uncond
         mk_skip_over_T32_if_cond_is_false(condT);
         condT = IRTemp_INVALID;
         // now uncond

         // branch to dst
         irsb->next = mkU32( dst | 1 /*CPSR.T*/ );
         irsb->jumpkind = Ijk_Boring;
         dres.whatNext  = Dis_StopHere;
         DIP("b.w 0x%x\n", dst);
         goto decode_success;
      }
   }

   /* ------------------ TBB, TBH ------------------ */
   if (INSN0(15,4) == 0xE8D && INSN1(15,5) == 0x780) {
      UInt rN = INSN0(3,0);
      UInt rM = INSN1(3,0);
      UInt bH = INSN1(4,4);
      if (bH/*ATC*/ || (rN != 13 && !isBadRegT(rM))) {
         /* Must be last or not-in IT block */
         gen_SIGILL_T_if_in_but_NLI_ITBlock(old_itstate, new_itstate);
         /* Go uncond */
         mk_skip_over_T32_if_cond_is_false(condT);
         condT = IRTemp_INVALID;

         IRExpr* ea
             = binop(Iop_Add32,
                     getIRegT(rN),
                     bH ? binop(Iop_Shl32, getIRegT(rM), mkU8(1))
                        : getIRegT(rM));

         IRTemp delta = newTemp(Ity_I32);
         if (bH) {
            assign(delta, unop(Iop_16Uto32, loadLE(Ity_I16, ea)));
         } else {
            assign(delta, unop(Iop_8Uto32, loadLE(Ity_I8, ea)));
         }

         irsb->next
            = binop(Iop_Or32,
                    binop(Iop_Add32,
                          getIRegT(15),
                          binop(Iop_Shl32, mkexpr(delta), mkU8(1))
                    ),
                    mkU32(1)
              );
         irsb->jumpkind = Ijk_Boring;
         dres.whatNext = Dis_StopHere;
         DIP("tb%c [r%u, r%u%s]\n",
             bH ? 'h' : 'b', rN, rM, bH ? ", LSL #1" : "");
         goto decode_success;
      }
   }

   /* ------------------ UBFX ------------------ */
   /* There's also ARM versions of same, but it doesn't seem worth the
      hassle to common up the handling (it's only a couple of C
      statements). */
   if (INSN0(15,4) == 0xF3C && INSN1(15,15) == 0 && INSN1(5,5) == 0) {
      UInt rN  = INSN0(3,0);
      UInt rD  = INSN1(11,8);
      UInt lsb = (INSN1(14,12) << 2) | INSN1(7,6);
      UInt wm1 = INSN1(4,0);
      UInt msb =  lsb + wm1;
      if (!isBadRegT(rD) && !isBadRegT(rN) && msb <= 31) {
         Bool isU = True;
         IRTemp src  = newTemp(Ity_I32);
         IRTemp tmp  = newTemp(Ity_I32);
         IRTemp res  = newTemp(Ity_I32);
         UInt   mask = ((1 << wm1) - 1) + (1 << wm1);
         vassert(msb >= 0 && msb <= 31);
         vassert(mask != 0); // guaranteed by msb being in 0 .. 31 inclusive

         assign(src, getIRegT(rN));
         assign(tmp, binop(Iop_And32,
                           binop(Iop_Shr32, mkexpr(src), mkU8(lsb)),
                           mkU32(mask)));
         assign(res, binop(isU ? Iop_Shr32 : Iop_Sar32,
                           binop(Iop_Shl32, mkexpr(tmp), mkU8(31-wm1)),
                           mkU8(31-wm1)));

         putIRegT(rD, mkexpr(res), condT);

         DIP("%s r%u, r%u, #%u, #%u\n",
             isU ? "ubfx" : "sbfx", rD, rN, lsb, wm1 + 1);
         goto decode_success;
      }
   }

   /* ------------------ UXTB ------------------ */
   if (INSN0(15,0) == 0xFA5F
       && INSN1(15,12) == BITS4(1,1,1,1)
       && INSN1(7,6) == BITS2(1,0)) {
      UInt rD = INSN1(11,8);
      UInt rM = INSN1(3,0);
      UInt rot = INSN1(5,4);
      if (!isBadRegT(rD) && !isBadRegT(rM)) {
         IRTemp srcT = newTemp(Ity_I32);
         IRTemp rotT = newTemp(Ity_I32);
         IRTemp dstT = newTemp(Ity_I32);
         assign(srcT, getIRegT(rM));
         assign(rotT, genROR32(srcT, 8 * rot));
         assign(dstT, unop(Iop_8Uto32, unop(Iop_32to8, mkexpr(rotT))));
         putIRegT(rD, mkexpr(dstT), condT);
         DIP("uxtb r%u, r%u, ror #%u\n", rD, rM, 8 * rot);
         goto decode_success;
      }
   }

   /* -------------- MUL.W Rd, Rn, Rm -------------- */
   if (INSN0(15,4) == 0xFB0
       && (INSN1(15,0) & 0xF0F0) == 0xF000) {
      UInt rN = INSN0(3,0);
      UInt rD = INSN1(11,8);
      UInt rM = INSN1(3,0);
      if (!isBadRegT(rD) && !isBadRegT(rN) && !isBadRegT(rM)) {
         IRTemp res = newTemp(Ity_I32);
         assign(res, binop(Iop_Mul32, getIRegT(rN), getIRegT(rM)));
         putIRegT(rD, mkexpr(res), condT);
         DIP("mul.w r%u, r%u, r%u\n", rD, rN, rM);
         goto decode_success;
      }
   }

   /* ------------------ {U,S}MULL ------------------ */
   if ((INSN0(15,4) == 0xFB8 || INSN0(15,4) == 0xFBA)
       && INSN1(7,4) == BITS4(0,0,0,0)) {
      UInt isU  = INSN0(5,5);
      UInt rN   = INSN0(3,0);
      UInt rDlo = INSN1(15,12);
      UInt rDhi = INSN1(11,8);
      UInt rM   = INSN1(3,0);
      if (!isBadRegT(rDhi) && !isBadRegT(rDlo)
          && !isBadRegT(rN) && !isBadRegT(rM) && rDlo != rDhi) {
         IRTemp res   = newTemp(Ity_I64);
         assign(res, binop(isU ? Iop_MullU32 : Iop_MullS32,
                           getIRegT(rN), getIRegT(rM)));
         putIRegT( rDhi, unop(Iop_64HIto32, mkexpr(res)), condT );
         putIRegT( rDlo, unop(Iop_64to32, mkexpr(res)), condT );
         DIP("%cmull r%u, r%u, r%u, r%u\n",
             isU ? 'u' : 's', rDlo, rDhi, rN, rM);
         goto decode_success;
      }
   }

   /* ------------------ ML{A,S} ------------------ */
   if (INSN0(15,4) == 0xFB0
       && INSN1(7,4) == BITS4(0,0,0,0)) { // MLS: 0001
      UInt rN = INSN0(3,0);
      UInt rA = INSN1(15,12);
      UInt rD = INSN1(11,8);
      UInt rM = INSN1(3,0);
      if (!isBadRegT(rD) && !isBadRegT(rN)
          && !isBadRegT(rM) && !isBadRegT(rA)) {
         IRTemp res = newTemp(Ity_I32);
         assign(res,
                binop(Iop_Add32, getIRegT(rA),
                      binop(Iop_Mul32, getIRegT(rN), getIRegT(rM))));
         putIRegT(rD, mkexpr(res), condT);
         DIP("%s r%u, r%u, r%u, r%u\n", "mla", rD, rN, rM, rA);
         goto decode_success;
      }
   }

   /* ----------------------------------------------------------- */
   /* -- Undecodable                                           -- */
   /* ----------------------------------------------------------- */

   goto decode_failure;
   /*NOTREACHED*/

  decode_failure:
   /* All decode failures end up here. */
   vex_printf("disInstr(thumb): unhandled instruction: "
              "0x%x\n", (UInt)insn0);

   /* Back up ITSTATE to the initial value for this instruction.
      If we don't do that, any subsequent restart of the instruction
      will restart with the wrong value. */
   put_ITSTATE(old_itstate);
   /* Tell the dispatcher that this insn cannot be decoded, and so has
      not been executed, and (is currently) the next to be executed.
      R15 should be up-to-date since it made so at the start of each
      insn, but nevertheless be paranoid and update it again right
      now. */
   vassert(0 == (guest_R15_curr_instr_notENC & 1));
   llPutIReg( 15, mkU32(guest_R15_curr_instr_notENC | 1) );
   irsb->next     = mkU32(guest_R15_curr_instr_notENC | 1 /* CPSR.T */);
   irsb->jumpkind = Ijk_NoDecode;
   dres.whatNext  = Dis_StopHere;
   dres.len       = 0;
   return dres;

  decode_success:
   /* All decode successes end up here. */
   DIP("\n");

   vassert(dres.len == 2 || dres.len == 4);

#if 0
   // XXX is this necessary on Thumb?
   /* Now then.  Do we have an implicit jump to r15 to deal with? */
   if (r15written) {
      /* If we get jump to deal with, we assume that there's been no
         other competing branch stuff previously generated for this
         insn.  That's reasonable, in the sense that the ARM insn set
         appears to declare as "Unpredictable" any instruction which
         generates more than one possible new value for r15.  Hence
         just assert.  The decoders themselves should check against
         all such instructions which are thusly Unpredictable, and
         decline to decode them.  Hence we should never get here if we
         have competing new values for r15, and hence it is safe to
         assert here. */
      vassert(dres.whatNext == Dis_Continue);
      vassert(irsb->next == NULL);
      vassert(irsb->jumpkind = Ijk_Boring);
      /* If r15 is unconditionally written, terminate the block by
         jumping to it.  If it's conditionally written, still
         terminate the block (a shame, but we can't do side exits to
         arbitrary destinations), but first jump to the next
         instruction if the condition doesn't hold. */
      /* We can't use getIRegT(15) to get the destination, since that
         will produce r15+4, which isn't what we want.  Must use
         llGetIReg(15) instead. */
      if (r15guard == IRTemp_INVALID) {
         /* unconditional */
      } else {
         /* conditional */
         stmt( IRStmt_Exit(
                  unop(Iop_32to1,
                       binop(Iop_Xor32,
                             mkexpr(r15guard), mkU32(1))),
                  r15kind,
                  IRConst_U32(guest_R15_curr_instr_notENC + 4)
         ));
      }
      irsb->next     = llGetIReg(15);
      irsb->jumpkind = r15kind;
      dres.whatNext  = Dis_StopHere;
   }
#endif

   return dres;

#  undef INSN0
#  undef INSN1
}

#undef DIP
#undef DIS


/*------------------------------------------------------------*/
/*--- Top-level fn                                         ---*/
/*------------------------------------------------------------*/

/* Disassemble a single instruction into IR.  The instruction
   is located in host memory at &guest_code[delta]. */

DisResult disInstr_ARM ( IRSB*        irsb_IN,
                         Bool         put_IP,
                         Bool         (*resteerOkFn) ( void*, Addr64 ),
                         Bool         resteerCisOk,
                         void*        callback_opaque,
                         UChar*       guest_code_IN,
                         Long         delta_ENCODED,
                         Addr64       guest_IP_ENCODED,
                         VexArch      guest_arch,
                         VexArchInfo* archinfo,
                         VexAbiInfo*  abiinfo,
                         Bool         host_bigendian_IN )
{
   DisResult dres;
   Bool isThumb = (Bool)(guest_IP_ENCODED & 1);

   /* Set globals (see top of this file) */
   vassert(guest_arch == VexArchARM);

   irsb              = irsb_IN;
   host_is_bigendian = host_bigendian_IN;

   if (isThumb) {
      guest_R15_curr_instr_notENC = (Addr32)guest_IP_ENCODED - 1;
   } else {
      guest_R15_curr_instr_notENC = (Addr32)guest_IP_ENCODED;
   }

   if (isThumb) {
      dres = disInstr_THUMB_WRK ( put_IP, resteerOkFn,
                                  resteerCisOk, callback_opaque,
                                  &guest_code_IN[delta_ENCODED - 1],
                                  archinfo, abiinfo );
   } else {
      dres = disInstr_ARM_WRK ( put_IP, resteerOkFn,
                                resteerCisOk, callback_opaque,
                                &guest_code_IN[delta_ENCODED],
                                archinfo, abiinfo );
   }

   return dres;
}

/* Test program for the conversion of IRCmpF64Result values to VFP
   nzcv values.  See handling of FCMPD et al above. */
/*
UInt foo ( UInt x )
{
   UInt ix    = ((x >> 5) & 3) | (x & 1);
   UInt termL = (((((ix ^ 1) << 30) - 1) >> 29) + 1);
   UInt termR = (ix & (ix >> 1) & 1);
   return termL  -  termR;
}

void try ( char* s, UInt ir, UInt req )
{
   UInt act = foo(ir);
   printf("%s 0x%02x -> req %d%d%d%d act %d%d%d%d (0x%x)\n",
          s, ir, (req >> 3) & 1, (req >> 2) & 1, 
                 (req >> 1) & 1, (req >> 0) & 1, 
                 (act >> 3) & 1, (act >> 2) & 1, 
                 (act >> 1) & 1, (act >> 0) & 1, act);

}

int main ( void )
{
   printf("\n");
   try("UN", 0x45, 0b0011);
   try("LT", 0x01, 0b1000);
   try("GT", 0x00, 0b0010);
   try("EQ", 0x40, 0b0110);
   printf("\n");
   return 0;
}
*/

/*--------------------------------------------------------------------*/
/*--- end                                         guest_arm_toIR.c ---*/
/*--------------------------------------------------------------------*/
