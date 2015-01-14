
/*---------------------------------------------------------------*/
/*--- begin                               host_generic_regs.c ---*/
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

#include "libvex_basictypes.h"
#include "libvex.h"

#include "main_util.h"
#include "host_generic_regs.h"


/*---------------------------------------------------------*/
/*--- Helpers for printing registers                    ---*/
/*---------------------------------------------------------*/

void ppHRegClass ( HRegClass hrc )
{
   switch (hrc) {
      case HRcInt32:   vex_printf("HRcInt32"); break;
      case HRcInt64:   vex_printf("HRcInt64"); break;
      case HRcFlt32:   vex_printf("HRcFlt32"); break;
      case HRcFlt64:   vex_printf("HRcFlt64"); break;
      case HRcVec64:   vex_printf("HRcVec64"); break;
      case HRcVec128:  vex_printf("HRcVec128"); break;
      default: vpanic("ppHRegClass");
   }
}

/* Generic printing for registers. */
void ppHReg ( HReg r ) 
{
   const HChar* maybe_v = hregIsVirtual(r) ? "v" : "";
   Int    regNo   = hregNumber(r);
   switch (hregClass(r)) {
      case HRcInt32:   vex_printf("%%%sr%d", maybe_v, regNo); return;
      case HRcInt64:   vex_printf("%%%sR%d", maybe_v, regNo); return;
      case HRcFlt32:   vex_printf("%%%sF%d", maybe_v, regNo); return;
      case HRcFlt64:   vex_printf("%%%sD%d", maybe_v, regNo); return;
      case HRcVec64:   vex_printf("%%%sv%d", maybe_v, regNo); return;
      case HRcVec128:  vex_printf("%%%sV%d", maybe_v, regNo); return;
      default: vpanic("ppHReg");
   }
}


/*---------------------------------------------------------*/
/*--- A simple implementation of register sets          ---*/
/*---------------------------------------------------------*/

/* Helper function, to sort HReg values in an array. */
static void sortHRegArray ( HReg* arr, Int nArr )
{
   Int  incs[14] = { 1, 4, 13, 40, 121, 364, 1093, 3280,
                     9841, 29524, 88573, 265720,
                     797161, 2391484 };
   Int  lo = 0;
   Int  hi = nArr-1;
   Int  i, j, h, bigN, hp;
   HReg v;

   vassert(nArr >= 0);
   if (nArr == 0) return;

   bigN = hi - lo + 1; if (bigN < 2) return;
   hp = 0; while (hp < 14 && incs[hp] < bigN) hp++; hp--;

   for ( ; hp >= 0; hp--) {
      h = incs[hp];
      for (i = lo + h; i <= hi; i++) {
         v = arr[i];
         j = i;
         while (arr[j-h].reg > v.reg) {
            arr[j] = arr[j-h];
            j = j - h;
            if (j <= (lo + h - 1)) break;
         }
         arr[j] = v;
      }
   }
}

/* Print a register set, using the arch-specific register printing
   function |regPrinter| supplied. */
void HRegSet__pp ( HRegSet* set, void (*regPrinter)(HReg) )
{
   UInt i;
   vex_printf("{");
   for (i = 0; i < set->regsUsed; i++) {
      regPrinter(set->regs[i]);
      if (i+1 != set->regsUsed)
         vex_printf(",");
   }
   vex_printf("}");
}

/* Create a new, empty, set. */
HRegSet* HRegSet__new ( void )
{
   HRegSet* set = LibVEX_Alloc(sizeof(HRegSet));
   set->regsUsed = 0;
   return set;
}

/* Install elements from vec[0 .. nVec-1].  The previous contents of
   |dst| are lost.  vec[0 .. nVec-1] may not contain any
   duplicates. */
void HRegSet__fromVec ( /*MOD*/HRegSet* dst, const HReg* vec, UInt nVec )
{
   UInt i;
   vassert(nVec <= N_HREG_SET);
   for (i = 0; i < nVec; i++) {
      dst->regs[i] = vec[i];
   }
   dst->regsUsed = nVec;
   sortHRegArray(&dst->regs[0], dst->regsUsed);
   /* Assert no duplicates (and, as a side effect, in-order) */
   for (i = 1; i < dst->regsUsed; i++) {
      /* If this fails, your vec[] contains duplicates. */
      vassert(dst->regs[i-1].reg < dst->regs[i].reg);
   }
}

/* Copy the contents of |regs| into |dst|.  The previous contents of
   |dst| are lost. */
void HRegSet__copy ( /*MOD*/HRegSet* dst, const HRegSet* regs )
{
   UInt i;
   dst->regsUsed = regs->regsUsed;
   for (i = 0; i < regs->regsUsed; i++)
      dst->regs[i] = regs->regs[i];
}

/* Add |reg| to |dst|. */
void HRegSet__add ( /*MOD*/HRegSet* dst, HReg reg )
{
   UInt i, j;
   for (i = 0; i < dst->regsUsed; i++) {
      if (reg.reg <= dst->regs[i].reg)
         break;
   }
   /* Is it already present? */
   if (i < dst->regsUsed && reg.reg == dst->regs[i].reg) {
      /* Yes.  Do nothing more. */
      return;
   }
   /* No.  Add it at position |i|. */
   vassert(dst->regsUsed < N_HREG_SET);
   dst->regsUsed++;
   for (j = dst->regsUsed-1; j > i; j--) {
      dst->regs[j] = dst->regs[j-1];
   }
   dst->regs[i] = reg;
}

/* Remove |reg| from |dst|. */
void HRegSet__del ( /*MOD*/HRegSet* dst, HReg reg )
{
   UInt i, j;
   for (i = 0; i < dst->regsUsed; i++) {
      if (reg.reg <= dst->regs[i].reg)
         break;
   }
   /* Is it already present? */
   if (i < dst->regsUsed && reg.reg == dst->regs[i].reg) {
      /* Yes, at position |i|. */;
      vassert(dst->regsUsed > 0);
      for (j = i+1; j < dst->regsUsed; j++) {
         dst->regs[j-1] = dst->regs[j];
      }
      dst->regsUsed--;
   }
}

/* Add |regs| to |dst|. */
void HRegSet__plus ( /*MOD*/HRegSet* dst, const HRegSet* regs )
{
   /* We'll need to create the result into a temp vector,
      since |dst| is also one of the sources. */
   HReg tmp[N_HREG_SET];
   UInt iD, iR, iT;
   UInt usedD = dst->regsUsed;
   UInt usedR = regs->regsUsed;
   iD = iR = iT = 0;

   while (1) {
      vassert(iD <= usedD && iR <= usedR);
      if (iD == usedD && iR == usedR) {
         /* both empty -- done */
         break;
      }
      vassert(iT < N_HREG_SET);
      if (iD == usedD && iR != usedR) {
         /* D empty, use up R */
         tmp[iT++] = regs->regs[iR++];
         continue;
      }
      if (iD != usedD && iR == usedR) {
         /* R empty, use up D */
         tmp[iT++] = dst->regs[iD++];
         continue;
      }
      /* both not empty; use the lowest valued HReg */
      HReg candD = dst->regs[iD];
      HReg candR = regs->regs[iR];
      if (candD.reg < candR.reg) {
         tmp[iT++] = candD;
         iD++;
      }
      else if (candD.reg > candR.reg) {
         tmp[iT++] = candR;
         iR++;
      }
      else {
         tmp[iT++] = candD;
         iD++; iR++;
      }
   }

   /* Copy result back into place. */
   vassert((iT >= usedD || iT >= usedR) && iT <= N_HREG_SET);
   UInt i;
   for (i = 0; i < iT; i++) {
      dst->regs[i] = tmp[i];
   }
   dst->regsUsed = iT;
}

/* Remove |regs| from |dst|. */
void HRegSet__minus ( /*MOD*/HRegSet* dst, const HRegSet* regs )
{
   /* We'll need to create the result into a temp vector,
      since |dst| is also one of the sources. */
   HReg tmp[N_HREG_SET];
   UInt iD, iR, iT;
   UInt usedD = dst->regsUsed;
   UInt usedR = regs->regsUsed;
   iD = iR = iT = 0;

   while (1) {
      vassert(iD <= usedD && iR <= usedR);
      if (iD == usedD) {
         /* D empty -- done */
         break;
      }
      vassert(iT < N_HREG_SET);
      if (iR == usedR) {
         /* R empty, use up D */
         tmp[iT++] = dst->regs[iD++];
         continue;
      }
      /* both not empty */
      HReg candD = dst->regs[iD];
      HReg candR = regs->regs[iR];
      if (candD.reg < candR.reg) {
         /* candD can't possibly be in the part of R that we
            haven't yet visited, so keep it. */
         tmp[iT++] = candD;
         iD++;
      }
      else if (candD.reg > candR.reg) {
         /* We don't know yet if we can retain candD, but for sure,
            candR won't be able to delete anything in the unvisited
            part of D.  So skip over candR. */
         iR++;
      }
      else {
         /* The register appears in both lists, so skip it. */
         iR++; iD++;
      }
   }

   /* Copy result back into place. */
   vassert((iT <= usedD || iT <= usedR) && iT <= N_HREG_SET);
   UInt i;
   for (i = 0; i < iT; i++) {
      dst->regs[i] = tmp[i];
   }
   dst->regsUsed = iT;
}

/* Returns the number of elements in |set|. */
UInt HRegSet__size ( const HRegSet* set ) {
   return set->regsUsed;
}

/* Returns the |ix|th element of |set|, where |ix| is zero-based. */
HReg HRegSet__index ( const HRegSet* set, UInt ix ) {
   vassert(ix < set->regsUsed);
   return set->regs[ix];
}


/*---------------------------------------------------------*/
/*--- Helpers for recording reg usage (for reg-alloc)   ---*/
/*---------------------------------------------------------*/

void ppHRegUsage ( HRegUsage* tab )
{
   Int    i;
   const HChar* str;
   vex_printf("HRegUsage {\n");
   for (i = 0; i < tab->n_used; i++) {
      switch (tab->mode[i]) {
         case HRmRead:   str = "Read   "; break;
         case HRmWrite:  str = "Write  "; break;
         case HRmModify: str = "Modify "; break;
         default: vpanic("ppHRegUsage");
      }
      vex_printf("   %s ", str);
      ppHReg(tab->hreg[i]);
      vex_printf("\n");
   }
   vex_printf("}\n");
}


/* Add a register to a usage table.  Combine incoming read uses with
   existing write uses into a modify use, and vice versa.  Do not
   create duplicate entries -- each reg should only be mentioned once.  
*/
void addHRegUse ( HRegUsage* tab, HRegMode mode, HReg reg )
{
   Int i;
   /* Find it ... */
   for (i = 0; i < tab->n_used; i++)
      if (sameHReg(tab->hreg[i], reg))
         break;
   if (i == tab->n_used) {
      /* Not found, add new entry. */
      vassert(tab->n_used < N_HREG_USAGE);
      tab->hreg[tab->n_used] = reg;
      tab->mode[tab->n_used] = mode;
      tab->n_used++;
   } else {
      /* Found: combine or ignore. */
      /* This is a greatest-lower-bound operation in the poset:

            R   W
             \ /
              M

         Need to do: tab->mode[i] = GLB(tab->mode, mode).  In this
         case very simple -- if tab->mode[i] != mode then result must
         be M.
      */
      if (tab->mode[i] == mode) {
         /* duplicate, ignore */
      } else {
         tab->mode[i] = HRmModify;
      }
   }
}


/*---------------------------------------------------------*/
/*--- Indicating register remappings (for reg-alloc)    ---*/
/*---------------------------------------------------------*/

void ppHRegRemap ( HRegRemap* map )
{
   Int   i;
   vex_printf("HRegRemap {\n");
   for (i = 0; i < map->n_used; i++) {
      vex_printf("   ");
      ppHReg(map->orig[i]);
      vex_printf("  -->  ");
      ppHReg(map->replacement[i]);
      vex_printf("\n");
   }
   vex_printf("}\n");
}


void initHRegRemap ( HRegRemap* map )
{
   map->n_used = 0;
}


void addToHRegRemap ( HRegRemap* map, HReg orig, HReg replacement )
{
   Int i;
   for (i = 0; i < map->n_used; i++)
      if (sameHReg(map->orig[i], orig))
         vpanic("addToHRegMap: duplicate entry");
   if (!hregIsVirtual(orig))
      vpanic("addToHRegMap: orig is not a vreg");
   if (hregIsVirtual(replacement))
      vpanic("addToHRegMap: replacement is a vreg");

   vassert(map->n_used+1 < N_HREG_REMAP);
   map->orig[map->n_used]        = orig;
   map->replacement[map->n_used] = replacement;
   map->n_used++;
}


HReg lookupHRegRemap ( HRegRemap* map, HReg orig )
{
   Int i;
   if (!hregIsVirtual(orig))
      return orig;
   for (i = 0; i < map->n_used; i++)
      if (sameHReg(map->orig[i], orig))
         return map->replacement[i];
   vpanic("lookupHRegRemap: not found");
}

/*---------------------------------------------------------*/
/*--- Abstract instructions                             ---*/
/*---------------------------------------------------------*/

HInstrArray* newHInstrArray ( void )
{
   HInstrArray* ha = LibVEX_Alloc(sizeof(HInstrArray));
   ha->arr_size = 4;
   ha->arr_used = 0;
   ha->arr      = LibVEX_Alloc(ha->arr_size * sizeof(HInstr*));
   ha->n_vregs  = 0;
   return ha;
}

void addHInstr ( HInstrArray* ha, HInstr* instr )
{
   vassert(ha->arr_used <= ha->arr_size);
   if (ha->arr_used < ha->arr_size) {
      ha->arr[ha->arr_used] = instr;
      ha->arr_used++;
   } else {
      Int      i;
      HInstr** arr2 = LibVEX_Alloc(ha->arr_size * 2 * sizeof(HInstr*));
      for (i = 0; i < ha->arr_size; i++)
         arr2[i] = ha->arr[i];
      ha->arr_size *= 2;
      ha->arr = arr2;
      addHInstr(ha, instr);
   }
}


/*---------------------------------------------------------*/
/*--- C-Call return-location actions                    ---*/
/*---------------------------------------------------------*/

void ppRetLoc ( RetLoc ska )
{
   switch (ska.pri) {
      case RLPri_INVALID:
         vex_printf("RLPri_INVALID"); return;
      case RLPri_None:
         vex_printf("RLPri_None");    return;
      case RLPri_Int:
         vex_printf("RLPri_Int");     return;
      case RLPri_2Int:
         vex_printf("RLPri_2Int");    return;
      case RLPri_V128SpRel:
         vex_printf("RLPri_V128SpRel(%d)", ska.spOff); return;
      case RLPri_V256SpRel:
         vex_printf("RLPri_V256SpRel(%d)", ska.spOff); return;
      default:
         vpanic("ppRetLoc");
   }
}


/*---------------------------------------------------------*/
/*--- Helpers for Relocations                           ---*/
/*---------------------------------------------------------*/

static void ppRelocWhere ( RelocWhere rlw )
{
   ppNLabelZone(rlw.zone);
   vex_printf("[%u]", rlw.offset);
}

static void ppRelocDst ( RelocDst rdst )
{
   if (rdst.isOffset) {
      ppRelocWhere( mkRelocWhere(rdst.zone, rdst.num) );
   } else {
      ppNLabel( mkNLabel(rdst.zone, rdst.num) );
   }
}

void ppRelocation ( Relocation* rl )
{
   vex_printf("(");
   ppRelocWhere(rl->where);
   vex_printf(" bits[%u..%u]) refers-to (", rl->bitNoMax, rl->bitNoMin);
   ppRelocDst(rl->dst);
   vex_printf(") bias %d rshift %u", rl->bias, (UInt)rl->rshift);
}


/*---------------------------------------------------------------*/
/*--- end                                 host_generic_regs.c ---*/
/*---------------------------------------------------------------*/
