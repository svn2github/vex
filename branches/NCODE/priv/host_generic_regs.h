
/*---------------------------------------------------------------*/
/*--- begin                               host_generic_regs.h ---*/
/*---------------------------------------------------------------*/

/*
   This file is part of Valgrind, a dynamic binary instrumentation
   framework.

   Copyright (C) 2004-2013 OpenWorks LLP
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

   Neither the names of the U.S. Department of Energy nor the
   University of California nor the names of its contributors may be
   used to endorse or promote products derived from this software
   without prior written permission.
*/

#ifndef __VEX_HOST_GENERIC_REGS_H
#define __VEX_HOST_GENERIC_REGS_H

#include "libvex_basictypes.h"


/*---------------------------------------------------------*/
/*--- Representing HOST REGISTERS                       ---*/
/*---------------------------------------------------------*/

/* Host registers.  Stuff to represent:

   - The register number
   - The register class
   - Whether or not the register is a virtual reg.

   Registers are a 32-bit Int, thusly:

     bits 31-28  are the register class.
     bits 27-23  are 0000b for real register, 0001b for virtual register
     bits 23-0   register number

   Note (importantly) that by arranging that the class field is never
   0000b, any valid register looks like an extremely large int -- at
   least 2^28 -- and so there is little chance of confusing it with an
   integer array index in the register allocator.

   Note further that since the class field is never 1111b, no valid
   register can have the value HReg_INVALID.

   There are currently 6 register classes:

     int32 int64 float32 float64 simd64 simd128
*/

typedef
   struct {
      UInt reg;
   }
   HReg;

/* When extending this, do not use any value > 14 or < 0. */
/* HRegClass describes host register classes which the instruction
   selectors can speak about.  We would not expect all of them to be
   available on any specific host.  For example on x86, the available
   classes are: Int32, Flt64, Vec128 only.

   IMPORTANT NOTE: host_generic_reg_alloc2.c needs how much space is
   needed to spill each class of register.  It allocates the following
   amount of space:

      HRcInt32     64 bits
      HRcInt64     64 bits
      HRcFlt32     64 bits
      HRcFlt64     128 bits (on x86 these are spilled by fstpt/fldt and
                             so won't fit in a 64-bit slot)
      HRcVec64     64 bits
      HRcVec128    128 bits

   If you add another regclass, you must remember to update
   host_generic_reg_alloc2.c accordingly.
*/
typedef
   enum { 
      HRcINVALID=1,   /* NOT A VALID REGISTER CLASS */
      HRcInt32=3,     /* 32-bit int */
      HRcInt64=4,     /* 64-bit int */
      HRcFlt32=5,     /* 32-bit float */
      HRcFlt64=6,     /* 64-bit float */
      HRcVec64=7,     /* 64-bit SIMD */
      HRcVec128=8     /* 128-bit SIMD */
   }
   HRegClass;

extern void ppHRegClass ( HRegClass );


/* Print an HReg in a generic (non-target-specific) way. */
extern void ppHReg ( HReg );

/* Construct/destruct. */
static inline HReg mkHReg ( UInt regno, HRegClass rc, Bool virtual ) {
   UInt r24 = regno & 0x00FFFFFF;
   /* This is critical.  The register number field may only
      occupy 24 bits. */
   if (r24 != regno)
      vpanic("mkHReg: regno exceeds 2^24");
   HReg r;
   r.reg = regno | (((UInt)rc) << 28) | (virtual ? (1<<24) : 0);
   return r;
}

static inline HRegClass hregClass ( HReg r ) {
   UInt rc = r.reg;
   rc = (rc >> 28) & 0x0F;
   vassert(rc >= HRcInt32 && rc <= HRcVec128);
   return (HRegClass)rc;
}

static inline UInt hregNumber ( HReg r ) {
   return r.reg & 0x00FFFFFF;
}

static inline Bool hregIsVirtual ( HReg r ) {
   return toBool(r.reg & (1<<24));
}

static inline Bool sameHReg ( HReg r1, HReg r2 )
{
   return toBool(r1.reg == r2.reg);
}

static const HReg HReg_INVALID = { 0xFFFFFFFF };

static inline Bool hregIsInvalid ( HReg r )
{
   return sameHReg(r, HReg_INVALID);
}


/*---------------------------------------------------------*/
/*--- Representing register sets                        ---*/
/*---------------------------------------------------------*/

/* This is a very un-clever representation, but we need
   to start somewhere. */

#define N_HREG_SET 20

typedef
   struct {
      HReg regs[N_HREG_SET];
      UInt regsUsed; /* 0 .. N_HREG_SET inclusive */
   }
   HRegSet;

/* Print a register set, using the arch-specific register printing
   function |regPrinter| supplied. */
extern void HRegSet__pp ( HRegSet* set, void (*regPrinter)(HReg) );

/* Create a new, empty, set. */
extern HRegSet* HRegSet__new ( void );

/* Install elements from vec[0 .. nVec-1].  The previous contents of
   |dst| are lost. */
extern void HRegSet__fromVec ( /*MOD*/HRegSet* dst,
                               const HReg* vec, UInt nVec );

/* Copy the contents of |regs| into |dst|.  The previous contents of
   |dst| are lost. */
extern void HRegSet__copy ( /*MOD*/HRegSet* dst, const HRegSet* regs );

/* Add |reg| to |dst|. */
extern void HRegSet__add ( /*MOD*/HRegSet* dst, HReg reg );

/* Remove |reg| from |dst|. */
extern void HRegSet__del ( /*MOD*/HRegSet* dst, HReg reg );

/* Add |regs| to |dst|. */
extern void HRegSet__plus ( /*MOD*/HRegSet* dst, const HRegSet* regs );

/* Remove |regs| from |dst|. */
extern void HRegSet__minus ( /*MOD*/HRegSet* dst, const HRegSet* regs );

/* Returns the number of elements in |set|. */
extern UInt HRegSet__size ( const HRegSet* set );

/* Returns the |ix|th element of |set|, where |ix| is zero-based. */
extern HReg HRegSet__index ( const HRegSet* set, UInt ix );


/*---------------------------------------------------------*/
/*--- Recording register usage (for reg-alloc)          ---*/
/*---------------------------------------------------------*/

typedef
   enum { HRmRead, HRmWrite, HRmModify }
   HRegMode;


/* A struct for recording the usage of registers in instructions.
   This can get quite large, but we don't expect to allocate them
   dynamically, so there's no problem. 
*/
#define N_HREG_USAGE 25

typedef
   struct {
      HReg     hreg[N_HREG_USAGE];
      HRegMode mode[N_HREG_USAGE];
      Int      n_used;
   }
   HRegUsage;

extern void ppHRegUsage ( HRegUsage* );

static inline void initHRegUsage ( HRegUsage* tab ) {
   tab->n_used = 0;
}

/* Add a register to a usage table.  Combine incoming read uses with
   existing write uses into a modify use, and vice versa.  Do not
   create duplicate entries -- each reg should only be mentioned once.  
*/
extern void addHRegUse ( HRegUsage*, HRegMode, HReg );


/*---------------------------------------------------------*/
/*--- Indicating register remappings (for reg-alloc)    ---*/
/*---------------------------------------------------------*/

/* Note that such maps can only map virtual regs to real regs.
   addToHRegRenap will barf if given a pair not of that form.  As a
   result, no valid HRegRemap will bind a real reg to anything, and so
   if lookupHRegMap is given a real reg, it returns it unchanged.
   This is precisely the behaviour that the register allocator needs
   to impose its decisions on the instructions it processes.  */

#define N_HREG_REMAP 6

typedef
   struct {
      HReg orig       [N_HREG_REMAP];
      HReg replacement[N_HREG_REMAP];
      Int  n_used;
   }
   HRegRemap;

extern void ppHRegRemap     ( HRegRemap* );
extern void initHRegRemap   ( HRegRemap* );
extern void addToHRegRemap  ( HRegRemap*, HReg, HReg );
extern HReg lookupHRegRemap ( HRegRemap*, HReg );


/*---------------------------------------------------------*/
/*--- Abstract instructions                             ---*/
/*---------------------------------------------------------*/

/* A type is needed to refer to pointers to instructions of any
   target.  Defining it like this means that HInstr* can stand in for
   X86Instr*, ArmInstr*, etc. */

typedef  void  HInstr;


/* An expandable array of HInstr*'s.  Handy for insn selection and
   register allocation.  n_vregs indicates the number of virtual
   registers mentioned in the code, something that reg-alloc needs to
   know.  These are required to be numbered 0 .. n_vregs-1. 
*/
typedef
   struct {
      HInstr** arr;
      Int      arr_size;
      Int      arr_used;
      Int      n_vregs;
   }
   HInstrArray;

extern HInstrArray* newHInstrArray ( void );
extern void         addHInstr ( HInstrArray*, HInstr* );


/*---------------------------------------------------------*/
/*--- C-Call return-location descriptions               ---*/
/*---------------------------------------------------------*/

/* This is common to all back ends.  It describes where the return
   value from a C call is located.  This is important in the case that
   the call is conditional, since the return locations will need to be
   set to 0x555..555 in the case that the call does not happen. */

typedef
   enum {
      RLPri_INVALID,   /* INVALID */
      RLPri_None,      /* no return value (a.k.a C "void") */
      RLPri_Int,       /* in the primary int return reg */
      RLPri_2Int,      /* in both primary and secondary int ret regs */
      RLPri_V128SpRel, /* 128-bit value, on the stack */
      RLPri_V256SpRel  /* 256-bit value, on the stack */
   }
   RetLocPrimary;

typedef
   struct {
      /* Primary description */
      RetLocPrimary pri;
      /* For .pri == RLPri_V128SpRel or RLPri_V256SpRel only, gives
         the offset of the lowest addressed byte of the value,
         relative to the stack pointer.  For all other .how values,
         has no meaning and should be zero. */
      Int spOff;
   }
   RetLoc;

extern void ppRetLoc ( RetLoc rloc );

static inline RetLoc mk_RetLoc_simple ( RetLocPrimary pri ) {
   vassert(pri >= RLPri_INVALID && pri <= RLPri_2Int);
   return (RetLoc){pri, 0};
}

static inline RetLoc mk_RetLoc_spRel ( RetLocPrimary pri, Int off ) {
   vassert(pri >= RLPri_V128SpRel && pri <= RLPri_V256SpRel);
   return (RetLoc){pri, off};
}

static inline Bool is_sane_RetLoc ( RetLoc rloc ) {
   switch (rloc.pri) {
      case RLPri_None: case RLPri_Int: case RLPri_2Int:
         return rloc.spOff == 0;
      case RLPri_V128SpRel: case RLPri_V256SpRel:
         return True;
      default:
         return False;
   }
}

static inline RetLoc mk_RetLoc_INVALID ( void ) {
   return (RetLoc){RLPri_INVALID, 0};
}

static inline Bool is_RetLoc_INVALID ( RetLoc rl ) {
   return rl.pri == RLPri_INVALID && rl.spOff == 0;
}


/*---------------------------------------------------------*/
/*--- Assembly buffers                                  ---*/
/*---------------------------------------------------------*/

/* This describes a buffer into which instructions are assembled. */

typedef
   struct {
      UChar* buf;     /* buffer */
      UInt   bufSize; /* max allowable size */
      UInt   bufUsed; /* next free location */
   }
   AssemblyBuffer;

static inline void AssemblyBuffer__init ( /*OUT*/AssemblyBuffer* abuf,
                                          UChar* buf, UInt bufSize )
{
   abuf->buf     = buf;
   abuf->bufSize = bufSize;
   abuf->bufUsed = 0;
}

static inline UChar* AssemblyBuffer__getCursor ( const AssemblyBuffer* abuf )
{
   return &abuf->buf[abuf->bufUsed];
}

static inline UInt AssemblyBuffer__getNext ( const AssemblyBuffer* abuf )
{
   return abuf->bufUsed;
}

static 
inline Int AssemblyBuffer__getRemainingSize ( const AssemblyBuffer* abuf )
{
   return (Int)abuf->bufSize - (Int)abuf->bufUsed;
}


/*---------------------------------------------------------*/
/*--- Relocations.  Move somewhere else?                ---*/
/*---------------------------------------------------------*/

/* This describes a place at which a relocation is to be performed, by
   pairing a hot/cold zone descriptor and an offset in an assembly
   buffer.
*/
typedef
   struct {
      NLabelZone zone;
      UInt       offset; // in the AssemblyBuffer associated with |zone|
   }
   RelocWhere;

static inline RelocWhere mkRelocWhere ( NLabelZone zone, UInt offset ) {
   RelocWhere rw = { zone, offset };
   return rw;
}


/* This describes a place which is the target of a relocation, that
   is, a jump target.  The target is in the hot or cold code buffer,
   hence |zone|, and is further characterised by |num| either as an
   instruction number (that is, an NLabel) when |isOffset| == False,
   or as an offset in the assembly buffer when |isOffset| == True.

   RelocDsts are initially created with |isOffset| == False, that is,
   as an NLabel.  Once we know the know the AssemblyBuffer offsets for
   each NLabel, |isOffset| is set to True and |num| becomes the
   offset.  Once it is in that form, it is possible to compute the
   distance in bytes between it and a RelocWhere, and hence perform
   the relocation.
*/
typedef
   struct {
      NLabelZone zone;
      UInt       num;
      Bool       isOffset;
   }
   RelocDst;

static inline RelocDst mkRelocDst_from_NLabel ( NLabel nl ) {
   RelocDst rd = { nl.zone, nl.ino, False/*!isOffset*/ };
   return rd;
}


/* What this describes is as follows.  Let |whereA| be an host address
   that |where| evaluates to, by whatever means, and let |dstA|
   likewise be a host address that |dst| evaluates to.

   What this then describes is a modification of a 32 bit integer
   located at whereA[0..3], interpreted in the host's endianness.  The
   32 bit value at that location has bits [bitNoMax .. bitNoMin]
   inclusive replaced by the least significant bits of the following
   expression

      E = (dstA - whereA + sign_extend(bias)) >>signed rshift

   and all other bits of that 32 bit value are left unchanged.
   Observe that this description assumes the relocation expression E
   is signed.  If the bits that we copy out of E and into the 32 bit
   word do not sign extend back to E, then the offset is too large to
   be represented and the relocation cannot be performed.

   The use of |bitNo{Max,Min}| facilitates writing an arbitrary bitfield
   in the middle of (eg) an ARM branch instruction.  For amd64-style
   32-bit branch offsets we expect the values to be 0 and 31
   respectively.

   The use of |rshift| facilitates architectures (eg ARM) that use fixed
   length instructions, and hence require the offset to be stated in
   number of instructions instead of (eg on amd64) number of bytes.

   The use of |bias| is necessary because on some targets (eg amd64) the
   processor expects the branch offset to be stated relative to the
   first byte of the instruction, but |where| points somewhere further
   along the instruction.  Hence we have to add a small negative bias
   to "back up" |where| to the start of the instruction.

   So far, so good.  This does assume that the offset bitfield is
   contiguous (not split into pieces) inside the target instruction.
*/
typedef
   struct {
      RelocWhere where;     // where the relocation should be applied
      UChar      bitNoMin;  // 0 .. 31 inclusive
      UChar      bitNoMax;  // bitNoMin .. 31 inclusive
      RelocDst   dst;       // destination of the (presumed) jump
      Int        bias;      // arbitrary, but in practice very small
      UChar      rshift;    // 0, 1 or 2 only
   }
   Relocation;

static
inline Relocation mkRelocation ( RelocWhere where,
                                 UChar bitNoMin, UChar bitNoMax,
                                 RelocDst dst, Int bias, UChar rshift ) {
   Relocation rl = { where, bitNoMin, bitNoMax, dst, bias, rshift };
   return rl;
}

extern void ppRelocation ( Relocation* rl );


/*---------------------------------------------------------*/
/*--- Relocation buffers                                ---*/
/*---------------------------------------------------------*/

/* This describes a buffer in which relocations are stored. */

typedef
   struct {
      Relocation* buf;     /* buffer */
      UInt        bufSize; /* max allowable size */
      UInt        bufUsed; /* next free location */
   }
   RelocationBuffer;

static inline void RelocationBuffer__init ( /*OUT*/RelocationBuffer* rbuf,
                                            Relocation* buf, UInt bufSize )
{
   rbuf->buf     = buf;
   rbuf->bufSize = bufSize;
   rbuf->bufUsed = 0;
}

static inline UInt RelocationBuffer__getNext ( const RelocationBuffer* rbuf )
{
   return rbuf->bufUsed;
}

static 
inline Int RelocationBuffer__getRemainingSize ( const RelocationBuffer* rbuf )
{
   return (Int)rbuf->bufSize - (Int)rbuf->bufUsed;
}


/*---------------------------------------------------------*/
/*--- Reg alloc: TODO: move somewhere else              ---*/
/*---------------------------------------------------------*/

extern
HInstrArray* doRegisterAllocation (

   /* Incoming virtual-registerised code. */ 
   HInstrArray* instrs_in,

   /* An array listing all the real registers the allocator may use,
      in no particular order. */
   HReg* available_real_regs,
   Int   n_available_real_regs,

   /* Return True iff the given insn is a reg-reg move, in which
      case also return the src and dst regs. */
   Bool (*isMove) (const HInstr*, HReg*, HReg*),

   /* Get info about register usage in this insn. */
   void (*getRegUsage) (HRegUsage*, const HInstr*, Bool),

   /* Apply a reg-reg mapping to an insn. */
   void (*mapRegs) (HRegRemap*, HInstr*, Bool),

   /* Return insn(s) to spill/restore a real reg to a spill slot
      offset.  And optionally a function to do direct reloads. */
   void    (*genSpill) (  HInstr**, HInstr**, HReg, Bool, Int, Bool ),
   void    (*genReload) ( HInstr**, HInstr**, HReg, Bool, Int, Bool ),
   HInstr* (*directReload) ( HInstr*, HReg, Short ),
   Int     guest_sizeB,

   /* For debug printing only. */
   void (*ppInstr) ( const HInstr*, Bool ),
   void (*ppReg) ( HReg ),

   /* 32/64bit mode */
   Bool mode64
);


#endif /* ndef __VEX_HOST_GENERIC_REGS_H */

/*---------------------------------------------------------------*/
/*---                                     host_generic_regs.h ---*/
/*---------------------------------------------------------------*/
