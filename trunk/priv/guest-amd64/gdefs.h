
/*---------------------------------------------------------------*/
/*---                                                         ---*/
/*--- This file (guest-amd64/gdefs.h) is                      ---*/
/*--- Copyright (c) 2005 OpenWorks LLP.  All rights reserved. ---*/
/*---                                                         ---*/
/*---------------------------------------------------------------*/

/*
   This file is part of LibVEX, a library for dynamic binary
   instrumentation and translation.

   Copyright (C) 2005 OpenWorks, LLP.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; Version 2 dated June 1991 of the
   license.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE, or liability
   for damages.  See the GNU General Public License for more details.

   Neither the names of the U.S. Department of Energy nor the
   University of California nor the names of its contributors may be
   used to endorse or promote products derived from this software
   without prior written permission.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
   USA.
*/

/* Only to be used within the guest-amd64 directory. */

#ifndef __LIBVEX_GUEST_AMD64_DEFS_H
#define __LIBVEX_GUEST_AMD64_DEFS_H


/*---------------------------------------------------------*/
/*--- amd64 to IR conversion                            ---*/
/*---------------------------------------------------------*/

extern
IRBB* bbToIR_AMD64 ( UChar*           amd64code, 
                     Addr64           eip, 
                     VexGuestExtents* vge,
                     Bool             (*byte_accessible)(Addr64),
                     Bool             (*resteerOkFn)(Addr64),
                     Bool             host_bigendian,
                     VexSubArch       subarch_guest );

/* Used by the optimiser to specialise calls to helpers. */
extern
IRExpr* guest_amd64_spechelper ( Char* function_name,
                                 IRExpr** args );

/* Describes to the optimiser which part of the guest state require
   precise memory exceptions.  This is logically part of the guest
   state description. */
extern 
Bool guest_amd64_state_requires_precise_mem_exns ( Int, Int );

extern
VexGuestLayout amd64guest_layout;


/*---------------------------------------------------------*/
/*--- amd64 guest helpers                               ---*/
/*---------------------------------------------------------*/

/* --- CLEAN HELPERS --- */

extern ULong amd64g_calculate_rflags_all ( 
                ULong cc_op, 
                ULong cc_dep1, ULong cc_dep2, ULong cc_ndep 
             );

extern Ulong amd64g_calculate_eflags_c ( 
                ULong cc_op, 
                ULong cc_dep1, ULong cc_dep2, ULong cc_ndep 
             );

extern ULong amd64g_calculate_condition ( 
                ULong/*AMD64Condcode*/ cond, 
                ULong cc_op, 
                ULong cc_dep1, ULong cc_dep2, ULong cc_ndep 
             );

//extern ULong amd64g_calculate_FXAM ( ULong tag, ULong dbl );

// Hmm.  This is going to be a problem as it needs to return
// 64bits and rflags.
//extern ULong amd64g_calculate_RCR  ( 
//                UInt arg, UInt rot_amt, UInt eflags_in, UInt sz 
//             );

//extern ULong amd64g_check_fldcw ( ULong fpucw );

//extern ULong amd64g_create_fpucw ( ULong fpround );

//extern ULong amd64g_check_ldmxcsr ( ULong mxcsr );

//extern ULong amd64g_create_mxcsr ( ULong sseround );

/* Translate a guest virtual_addr into a guest linear address by
   consulting the supplied LDT/GDT structures.  Their representation
   must be as specified in pub/libvex_guest_amd64.h.  To indicate a
   translation failure, 1<<32 is returned.  On success, the lower 32
   bits of the returned result indicate the linear address.  
*/
//extern 
//ULong amd64g_use_seg_selector ( HWord ldt, HWord gdt, 
//                              UInt seg_selector, UInt virtual_addr );

extern ULong amd64g_calculate_mmx_pmaddwd  ( ULong, ULong );
extern ULong amd64g_calculate_mmx_psadbw   ( ULong, ULong );
extern UInt  amd64g_calculate_mmx_pmovmskb ( ULong );
extern UInt  amd64g_calculate_sse_pmovmskb ( ULong w64hi, ULong w64lo );


/* --- DIRTY HELPERS --- */

//extern ULong amd64g_loadF80le  ( ULong/*addr*/ );

//extern void  amd64g_storeF80le ( ULong/*addr*/, ULong );

//extern void  amd64g_dirtyhelper_CPUID_sse0 ( VexGuestAMD64State* );
//extern void  amd64g_dirtyhelper_CPUID_sse1 ( VexGuestAMD64State* );
//extern void  amd64g_dirtyhelper_CPUID_sse2 ( VexGuestAMD64State* );

//extern void  amd64g_dirtyhelper_FSAVE ( VexGuestAMD64State*, HWord );

//extern void  amd64g_dirtyhelper_FINIT ( VexGuestAMD64State* );

//extern VexEmWarn
//            amd64g_dirtyhelper_FRSTOR ( VexGuestAMD64State*, HWord );

//extern void amd64g_dirtyhelper_FSTENV ( VexGuestAMD64State*, HWord );

//extern VexEmWarn 
//            amd64g_dirtyhelper_FLDENV ( VexGuestAMD64State*, HWord );

//extern void  amd64g_dirtyhelper_FXSAVE ( VexGuestAMD64State*, HWord );


/*---------------------------------------------------------*/
/*--- Condition code stuff                              ---*/
/*---------------------------------------------------------*/

/* rflags masks */
#define AMD64G_CC_SHIFT_O   11
#define AMD64G_CC_SHIFT_S   7
#define AMD64G_CC_SHIFT_Z   6
#define AMD64G_CC_SHIFT_A   4
#define AMD64G_CC_SHIFT_C   0
#define AMD64G_CC_SHIFT_P   2

#define AMD64G_CC_MASK_O    (1 << AMD64G_CC_SHIFT_O)
#define AMD64G_CC_MASK_S    (1 << AMD64G_CC_SHIFT_S)
#define AMD64G_CC_MASK_Z    (1 << AMD64G_CC_SHIFT_Z)
#define AMD64G_CC_MASK_A    (1 << AMD64G_CC_SHIFT_A)
#define AMD64G_CC_MASK_C    (1 << AMD64G_CC_SHIFT_C)
#define AMD64G_CC_MASK_P    (1 << AMD64G_CC_SHIFT_P)

/* FPU flag masks */
//#define AMD64G_FC_MASK_C3   (1 << 14)
//#define AMD64G_FC_MASK_C2   (1 << 10)
//#define AMD64G_FC_MASK_C1   (1 << 9)
//#define AMD64G_FC_MASK_C0   (1 << 8)

/* %RFLAGS thunk descriptors.  A four-word thunk is used to record
   details of the most recent flag-setting operation, so the flags can
   be computed later if needed.  It is possible to do this a little
   more efficiently using a 3-word thunk, but that makes it impossible
   to describe the flag data dependencies sufficiently accurately for
   Memcheck.  Hence 4 words are used, with minimal loss of efficiency.

   The four words are:

      CC_OP, which describes the operation.

      CC_DEP1 and CC_DEP2.  These are arguments to the operation.
         We want Memcheck to believe that the resulting flags are
         data-dependent on both CC_DEP1 and CC_DEP2, hence the 
         name DEP.

      CC_NDEP.  This is a 3rd argument to the operation which is
         sometimes needed.  We arrange things so that Memcheck does
         not believe the resulting flags are data-dependent on CC_NDEP
         ("not dependent").

   To make Memcheck believe that (the definedness of) the encoded
   flags depends only on (the definedness of) CC_DEP1 and CC_DEP2
   requires two things:

   (1) In the guest state layout info (amd64guest_layout), CC_OP and
       CC_NDEP are marked as always defined.

   (2) When passing the thunk components to an evaluation function
       (calculate_condition, calculate_eflags, calculate_eflags_c) the
       IRCallee's mcx_mask must be set so as to exclude from
       consideration all passed args except CC_DEP1 and CC_DEP2.

   Strictly speaking only (2) is necessary for correctness.  However,
   (1) helps efficiency in that since (2) means we never ask about the
   definedness of CC_OP or CC_NDEP, we may as well not even bother to
   track their definedness.

   When building the thunk, it is always necessary to write words into
   CC_DEP1 and CC_DEP2, even if those args are not used given the
   CC_OP field (eg, CC_DEP2 is not used if CC_OP is CC_LOGIC1/2/4).
   This is important because otherwise Memcheck could give false
   positives as it does not understand the relationship between the
   CC_OP field and CC_DEP1 and CC_DEP2, and so believes that the 
   definedness of the stored flags always depends on both CC_DEP1 and
   CC_DEP2.

   However, it is only necessary to set CC_NDEP when the CC_OP value
   requires it, because Memcheck ignores CC_NDEP, and the evaluation
   functions do understand the CC_OP fields and will only examine
   CC_NDEP for suitable values of CC_OP.

   A summary of the field usages is:

   Operation          DEP1               DEP2               NDEP
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   add/sub/mul        first arg          second arg         unused

   adc/sbb            first arg          (second arg)
                                         XOR old_carry      old_carry

   and/or/xor         result             zero               unused

   inc/dec            result             zero               old_carry

   shl/shr/sar        result             subshifted-        unused
                                         result

   rol/ror            result             zero               old_flags

   copy               old_flags          zero               unused.


   Therefore Memcheck will believe the following:

   * add/sub/mul -- definedness of result flags depends on definedness
     of both args.

   * adc/sbb -- definedness of result flags depends on definedness of
     both args and definedness of the old C flag.  Because only two
     DEP fields are available, the old C flag is XOR'd into the second
     arg so that Memcheck sees the data dependency on it.  That means
     the NDEP field must contain a second copy of the old C flag
     so that the evaluation functions can correctly recover the second
     arg.

   * and/or/xor are straightforward -- definedness of result flags
     depends on definedness of result value.

   * inc/dec -- definedness of result flags depends only on
     definedness of result.  This isn't really true -- it also depends
     on the old C flag.  However, we don't want Memcheck to see that,
     and so the old C flag must be passed in NDEP and not in DEP2.
     It's inconceivable that a compiler would generate code that puts
     the C flag in an undefined state, then does an inc/dec, which
     leaves C unchanged, and then makes a conditional jump/move based
     on C.  So our fiction seems a good approximation.

   * shl/shr/sar -- straightforward, again, definedness of result
     flags depends on definedness of result value.  The subshifted
     value (value shifted one less) is also needed, but its
     definedness is the same as the definedness of the shifted value.

   * rol/ror -- these only set O and C, and leave A Z C P alone.
     However it seems prudent (as per inc/dec) to say the definedness
     of all resulting flags depends on the definedness of the result,
     hence the old flags must go in as NDEP and not DEP2.

   * rcl/rcr are too difficult to do in-line, and so are done by a
     helper function.  They are not part of this scheme.  The helper
     function takes the value to be rotated, the rotate amount and the
     old flags, and returns the new flags and the rotated value.
     Since the helper's mcx_mask does not have any set bits, Memcheck
     will lazily propagate undefinedness from any of the 3 args into 
     both results (flags and actual value).
*/
enum {
    AMD64G_CC_OP_COPY,    /* DEP1 = current flags, DEP2 = 0, NDEP = unused */
                          /* just copy DEP1 to output */

    AMD64G_CC_OP_ADDB,    /* 1 */
    AMD64G_CC_OP_ADDW,    /* 2 DEP1 = argL, DEP2 = argR, NDEP = unused */
    AMD64G_CC_OP_ADDL,    /* 3 */

    AMD64G_CC_OP_SUBB,    /* 4 */
    AMD64G_CC_OP_SUBW,    /* 5 DEP1 = argL, DEP2 = argR, NDEP = unused */
    AMD64G_CC_OP_SUBL,    /* 6 */

    AMD64G_CC_OP_ADCB,    /* 7 */
    AMD64G_CC_OP_ADCW,    /* 8 DEP1 = argL, DEP2 = argR ^ oldCarry, NDEP = oldCarry */
    AMD64G_CC_OP_ADCL,    /* 9 */

    AMD64G_CC_OP_SBBB,    /* 10 */
    AMD64G_CC_OP_SBBW,    /* 11 DEP1 = argL, DEP2 = argR ^ oldCarry, NDEP = oldCarry */
    AMD64G_CC_OP_SBBL,    /* 12 */

    AMD64G_CC_OP_LOGICB,  /* 13 */
    AMD64G_CC_OP_LOGICW,  /* 14 DEP1 = result, DEP2 = 0, NDEP = unused */
    AMD64G_CC_OP_LOGICL,  /* 15 */

    AMD64G_CC_OP_INCB,    /* 16 */
    AMD64G_CC_OP_INCW,    /* 17 DEP1 = result, DEP2 = 0, NDEP = oldCarry (0 or 1) */
    AMD64G_CC_OP_INCL,    /* 18 */

    AMD64G_CC_OP_DECB,    /* 19 */
    AMD64G_CC_OP_DECW,    /* 20 DEP1 = result, DEP2 = 0, NDEP = oldCarry (0 or 1) */
    AMD64G_CC_OP_DECL,    /* 21 */

    AMD64G_CC_OP_SHLB,    /* 22 DEP1 = res, DEP2 = res', NDEP = unused */
    AMD64G_CC_OP_SHLW,    /* 23 where res' is like res but shifted one bit less */
    AMD64G_CC_OP_SHLL,    /* 24 */

    AMD64G_CC_OP_SHRB,    /* 25 DEP1 = res, DEP2 = res', NDEP = unused */
    AMD64G_CC_OP_SHRW,    /* 26 where res' is like res but shifted one bit less */
    AMD64G_CC_OP_SHRL,    /* 27 */

    AMD64G_CC_OP_ROLB,    /* 28 */
    AMD64G_CC_OP_ROLW,    /* 29 DEP1 = res, DEP2 = 0, NDEP = old flags */
    AMD64G_CC_OP_ROLL,    /* 30 */

    AMD64G_CC_OP_RORB,    /* 31 */
    AMD64G_CC_OP_RORW,    /* 32 DEP1 = res, DEP2 = 0, NDEP = old flags */
    AMD64G_CC_OP_RORL,    /* 33 */

    AMD64G_CC_OP_UMULB,   /* 34 */
    AMD64G_CC_OP_UMULW,   /* 35 DEP1 = argL, DEP2 = argR, NDEP = unused */
    AMD64G_CC_OP_UMULL,   /* 36 */

    AMD64G_CC_OP_SMULB,   /* 37 */
    AMD64G_CC_OP_SMULW,   /* 38 DEP1 = argL, DEP2 = argR, NDEP = unused */
    AMD64G_CC_OP_SMULL,   /* 39 */

    AMD64G_CC_OP_NUMBER
};

typedef
   enum {
      AMD64CondO      = 0,  /* overflow           */
      AMD64CondNO     = 1,  /* no overflow        */

      AMD64CondB      = 2,  /* below              */
      AMD64CondNB     = 3,  /* not below          */

      AMD64CondZ      = 4,  /* zero               */
      AMD64CondNZ     = 5,  /* not zero           */

      AMD64CondBE     = 6,  /* below or equal     */
      AMD64CondNBE    = 7,  /* not below or equal */

      AMD64CondS      = 8,  /* negative           */
      AMD64CondNS     = 9,  /* not negative       */

      AMD64CondP      = 10, /* parity even        */
      AMD64CondNP     = 11, /* not parity even    */

      AMD64CondL      = 12, /* jump less          */
      AMD64CondNL     = 13, /* not less           */

      AMD64CondLE     = 14, /* less or equal      */
      AMD64CondNLE    = 15, /* not less or equal  */

      AMD64CondAlways = 16  /* HACK */
   }
   AMD64Condcode;

#endif /* ndef __LIBVEX_GUEST_AMD64_DEFS_H */

/*---------------------------------------------------------------*/
/*--- end                                 guest-amd64/gdefs.h ---*/
/*---------------------------------------------------------------*/