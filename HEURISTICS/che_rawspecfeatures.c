/*-----------------------------------------------------------------------

File  : che_rawspecfeatures.c

Author: Stephan Schulz (schulz@eprover.org)

Contents
 
  Code and datatypes for handling rough classification of raw problem
  specs.

  Copyright 2012 by the author.
  This code is released under the GNU General Public Licence.
  See the file COPYING in the main CLIB directory for details.
  Run "eprover -h" for contact information.

Changes

<1> Tue May 22 01:16:15 CEST 2012
    New

-----------------------------------------------------------------------*/

#include "che_rawspecfeatures.h"



/*---------------------------------------------------------------------*/
/*                        Global Variables                             */
/*---------------------------------------------------------------------*/


/*---------------------------------------------------------------------*/
/*                      Forward Declarations                           */
/*---------------------------------------------------------------------*/


/*---------------------------------------------------------------------*/
/*                         Internal Functions                          */
/*---------------------------------------------------------------------*/



/*---------------------------------------------------------------------*/
/*                         Exported Functions                          */
/*---------------------------------------------------------------------*/

/*-----------------------------------------------------------------------
//
// Function: 
//
//   
//
// Global Variables: 
//
// Side Effects    : 
//
/----------------------------------------------------------------------*/

void RawSpecFeaturesCompute(RawSpecFeature_p features, ProofState_p state)
{
      features->sentence_no = ClauseSetCardinality(state->axioms)+
         ClauseSetCardinality(state->f_axioms);
      features->term_size   = ClauseSetStandardWeight(state->axioms)+
         FormulaSetStandardWeight(state->f_axioms);
      features->sig_size    = SigCountSymbols(state->terms->sig, true)+
         SigCountSymbols(state->terms->sig,false);
}


/*-----------------------------------------------------------------------
//
// Function: 
//
//   
//
// Global Variables: 
//
// Side Effects    : 
//
/----------------------------------------------------------------------*/

void RawSpecFeaturesClassify(RawSpecFeature_p features, SpecLimits_p limits)
{
   if(features->sentence_no < limits->ax_some_limit)
   {
      features->class[0] = 'S';
   }
   else if(features->sentence_no < limits->ax_many_limit)
   {
      features->class[0] = 'M';
   }
   else
   {
      features->class[0] = 'L';
   }
   
   if(features->term_size < limits->term_medium_limit)
   {
      features->class[1] = 'S';
   }
   else if(features->term_size < limits->term_large_limit)
   {
      features->class[1] = 'M';
   }
   else
   {
      features->class[1] = 'L';
   }
   
   if(features->sig_size < limits->symbols_medium_limit)
   {
      features->class[2] = 'S';
   }
   else if(features->sig_size < limits->symbols_large_limit)
   {
      features->class[2] = 'M';
   }
   else
   {
      features->class[2] = 'L';
   }
   features->class[3] = '\0';
}

/*-----------------------------------------------------------------------
//
// Function: 
//
//   
//
// Global Variables: 
//
// Side Effects    : 
//
/----------------------------------------------------------------------*/

void RawSPecFeaturesPrint(FILE* out, RawSpecFeature_p features)
{
      fprintf(out, "(%7ld, %7lld, %6d): %s",
              features->sentence_no, 
              features->term_size,
              features->sig_size, 
              features->class);
}



/*---------------------------------------------------------------------*/
/*                        End of File                                  */
/*---------------------------------------------------------------------*/

