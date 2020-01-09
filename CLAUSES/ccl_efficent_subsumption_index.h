/*-----------------------------------------------------------------------

File  : ccl_efficent_subsumption_index.h

Author: Constantin Ruhdorfer

Contents

  Interface for indexing clauses for subsumption.

Copyright 2019-2020 by the author.
  This code is released under the GNU General Public Licence and
  the GNU Lesser General Public License.
  See the file COPYING in the main E directory for details..
  Run "eprover -h" for contact information.

-----------------------------------------------------------------------*/

#ifndef CCL_EFFICENT_SUBSUMPTION_INDEX
#define CCL_EFFICENT_SUBSUMPTION_INDEX

#include <ccl_fcvindexing.h>
#include <ccl_unitclause_index.h>

/*---------------------------------------------------------------------*/
/*                    Data type declarations                           */
/*---------------------------------------------------------------------*/

typedef struct efficent_subsumption_index
{
   FVIAnchor_p       fvindex;          /* Used for non-unit subsumption */
   UnitclauseIndex_p unitclasue_index; /* Used for unit clauses subsuption */
} EfficentSubsumptionIndex, *EfficentSubsumptionIndex_p;


/*---------------------------------------------------------------------*/
/*                Exported Functions and Variables                     */
/*---------------------------------------------------------------------*/

#define EfficentSubsumptionIndexAllocRaw() (EfficentSubsumptionIndex*)SizeMalloc(sizeof(EfficentSubsumptionIndex))
#define EfficentSubsumptionIndexFreeRaw(junk) SizeFree(efficent_subsumption_index, sizeof(efficent_subsumption_index))

EfficentSubsumptionIndex_p EfficentSubsumptionIndexAlloc();
void ClausesetIndexInsertNewClause(EfficentSubsumptionIndex_p clauseset_indexes, FVPackedClause_p newclause);
Clause_p ClausesetIndexExtractEntry(EfficentSubsumptionIndex_p clauseset_indexes, Clause_p junk);
void EfficentSubsumptionIndexFree(EfficentSubsumptionIndex_p clauseset_indexes);
void EfficentSubsumptionIndexUCIndexededInsert(EfficentSubsumptionIndex_p clauseset_indexes, Clause_p newclause);
void EfficentSubsumptionIndexPDTIndexedInsert(EfficentSubsumptionIndex_p clauseset_indexes, Clause_p newclause);


/*---------------------------------------------------------------------*/
/*                         Internal Functions                          */
/*---------------------------------------------------------------------*/

/*---------------------------------------------------------------------*/
/*                        End of File                                  */
/*---------------------------------------------------------------------*/

#endif