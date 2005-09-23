/*-----------------------------------------------------------------------

File  : ccl_inferencedoc.h

Author: Stephan Schulz

Contents
 
  Functions and constants for reporting on the proof process.

  Copyright 1998, 1999 by the author.
  This code is released under the GNU General Public Licence.
  See the file COPYING in the main CLIB directory for details.
  Run "eprover -h" for contact information.

Changes

<1> Tue Jan  5 15:27:37 MET 1999
    Partially new, partially lifted from ccl_clauses.[ch]

-----------------------------------------------------------------------*/

#ifndef CCL_INFERENCEDOC

#define CCL_INFERENCEDOC

#include <ccl_clausepos.h>
#include <ccl_formula_wrapper.h>

/*---------------------------------------------------------------------*/
/*                    Data type declarations                           */
/*---------------------------------------------------------------------*/


typedef enum 
{
   inf_noinf,
   inf_initial,
   inf_quote,
   inf_paramod,
   inf_sim_paramod,
   inf_efactor,
   inf_factor,
   inf_eres,
   inf_split,
   inf_simplify_reflect,
   inf_context_simplify_reflect,
   inf_ac_resolution,
   inf_minimize,
   inf_rewrite,

   inf_fof_simpl,
   inf_fof_nnf,
   inf_fof_intro_def,
   inf_fof_apply_def,
   inf_shift_quantors,
   inf_fof_distrib,
   inf_var_rename,
   inf_skolemize_out,
   inf_neg_conjecture
}InfType;
   
typedef enum
{
   no_format,
   pcl_format,
   tstp_format,
   xml_format
}OutputFormatType;
 

#define PCL_QUOTE NULL
#define PCL_ER    "er"
#define PCL_PM    "pm"
#define PCL_SPM    "spm"
#define PCL_EF    "ef"
#define PCL_OF    "of"
#define PCL_SPLIT "split"
#define TSTP_SPLIT_REFINED "esplit"
#define TSTP_SPLIT_BASE    "split"
#define PCL_RW    "rw"
#define PCL_SR    "sr"
#define PCL_CSR   "csr"
#define PCL_ACRES "ar"
#define PCL_CN    "cn"

#define PCL_SC    "split_conjunct"
#define PCL_FS    "fof_simplification"
#define PCL_NNF   "fof_nnf"
#define PCL_ID    "intro_def"
#define PCL_AD    "apply_def"
#define PCL_SQ    "shift_quantors"
#define PCL_VR    "variable_rename"
#define PCL_SK    "skolemize"
#define PCL_DSTR  "distribute"
#define PCL_NC    "assume_negation"

/*---------------------------------------------------------------------*/
/*                Exported Functions and Variables                     */
/*---------------------------------------------------------------------*/

extern OutputFormatType DocOutputFormat;
extern bool             PCLFullTerms;
extern bool             PCLStepCompact;

void DocClauseCreation(FILE* out, long level, Clause_p clause,
			    InfType op, Clause_p parent1,
			    Clause_p parent2, char* comment);
#define DocClauseCreationDefault(clause, op, parent1, parent2)\
        DocClauseCreation(GlobalOut, OutputLevel, (clause),\
		       (op), (parent1), (parent2), NULL)

void    DocClauseFromForm(FILE* out, long level, Clause_p clause, 
                          WFormula_p parent);

void    DocClauseModification(FILE* out, long level, Clause_p clause, InfType
		     op, Clause_p partner, Sig_p sig, char* comment);
#define DocClauseModificationDefault(clause, op, partner)\
        DocClauseModification(GlobalOut, OutputLevel, (clause), (op),\
		     (partner), NULL, NULL)

void    DocClauseQuote(FILE* out, long level, long target_level,
		       Clause_p clause, char* comment, Clause_p
		       opt_partner);

#define DocClauseQuoteDefault(target_level, clause, comment)\
        DocClauseQuote(GlobalOut, OutputLevel, (target_level),\
		       (clause), (comment), NULL)

void    DocClauseRewrite(FILE* out, long level, ClausePos_p rewritten,
			 Term_p old_term, char* comment);

#define DocClauseRewriteDefault(rewritten, old_term)\
        DocClauseRewrite(GlobalOut, OutputLevel, (rewritten),\
			 (old_term), NULL);
void    DocClauseEqUnfold(FILE* out, long level, Clause_p rewritten,
			  ClausePos_p demod, PStack_p demod_pos);

 
void    DocFormulaCreation(FILE* out, long level, WFormula_p formula, 
                           InfType op, WFormula_p parent1,
                           WFormula_p parent2, char* comment);

#define DocFormulaCreationDefault(formula, op, parent1, parent2)\
        DocFormulaCreation(GlobalOut, OutputLevel, (formula),\
        (op), (parent1), (parent2), NULL) 

void    DocFormulaModification(FILE* out, long level, WFormula_p form, 
                                InfType op, char* comment);

#define DocFormulaModificationDefault(form, op)\
        DocFormulaModification(GlobalOut, OutputLevel, (form), (op), NULL)


#endif

/*---------------------------------------------------------------------*/
/*                        End of File                                  */
/*---------------------------------------------------------------------*/





