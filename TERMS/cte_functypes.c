/*-----------------------------------------------------------------------

File  : cte_functypes.c

Author: Stephan Schulz (schulz@eprover.org)

Contents

  Simple code for handling function symbols, both encoded and in
  external representation. Most of this is factored out of
  cte_signature.c, which is already overbloated.

  Copyright 2007 by the author.
  This code is released under the GNU General Public Licence and
  the GNU Lesser General Public License.
  See the file COPYING in the main E directory for details..
  Run "eprover -h" for contact information.

Changes

<1> Sat Sep  8 01:11:32 EDT 2007
    New

-----------------------------------------------------------------------*/

#include "cte_functypes.h"



/*---------------------------------------------------------------------*/
/*                        Global Variables                             */
/*---------------------------------------------------------------------*/

#define ATOMIC_FUNC_SYM_TOK (Identifier | SemIdent | SQString | String)

/* Tokens that always are stand-alone identifiers */
TokenType FuncSymbToken = ATOMIC_FUNC_SYM_TOK;
/* Tokens that may start a (composite or atomic) identifier */
TokenType FuncSymbStartToken = ATOMIC_FUNC_SYM_TOK| PosInt | String | Plus | Hyphen;


/*---------------------------------------------------------------------*/
/*                      Forward Declarations                           */
/*---------------------------------------------------------------------*/


/*---------------------------------------------------------------------*/
/*                         Internal Functions                          */
/*---------------------------------------------------------------------*/

/*-----------------------------------------------------------------------
//
// Function: normalize_int_rep()
//
//    Take a string representation of an integer and turn it into a
//    normal form. This is done by dropping the optional leading + and
//    all leading zeros (except for the case of plain '0', of
//    course).
//
// Global Variables: -
//
// Side Effects    : Memory operations
//
/----------------------------------------------------------------------*/

static void normalize_int_rep(DStr_p int_rep)
{
   char* work, *sign="";
   DStr_p tmp = DStrAlloc();

   work = DStrView(int_rep);

   if(*work=='+')
   {
      work++;
   }
   else if(*work=='-')
   {
      sign = "-";
      work++;
   }

   while(*work == '0')
   {
      work++;
   }
   /* Check if there is anything left */
   if(*work)
   {
      DStrAppendStr(tmp, sign);
      DStrAppendStr(tmp, work);
      DStrSet(int_rep, DStrView(tmp));
   }
   else
   {
      DStrSet(int_rep, "0");
   }
   DStrFree(tmp);
}

/*-----------------------------------------------------------------------
//
// Function: normalize_rational_rep()
//
//    Take a string representation of an integer and turn it into a
//    normal form. This is done by dropping optional leading +es and
//    all leading zeros (except for the case of plain '0', of
//    course), and moving any remaining '-' to the very front.
//
// Global Variables: -
//
// Side Effects    : Memory operations
//
/----------------------------------------------------------------------*/

static void normalize_rational_rep(DStr_p int_rep)
{
   char* work;
   bool  negative = false;
   DStr_p tmp = DStrAlloc();

   work = DStrView(int_rep);

   if(*work=='+')
   {
      work++;
   }
   else if(*work=='-')
   {
      negative = true;
      work++;
   }
   while(*work == '0')
   {
      work++;
   }
   /* Check if there is anything left */
   if(*work!= '/')
   {
      while(*work != '/')
      {
         DStrAppendChar(tmp, *work);
         work++;
      }
   }
   else
   {
      DStrSet(tmp, "0");
   }
   assert(*work == '/');
   DStrAppendChar(tmp, '/');
   work++;

   if(*work=='+')
   {
      work++;
   }
   else if(*work=='-')
   {
      negative = !negative;
      work++;
   }
   while(*work == '0')
   {
      work++;
   }
   /* Check if there is anything left */
   if(*work)
   {
      while(*work)
      {
         DStrAppendChar(tmp, *work);
         work++;
      }
   }
   else
   {
      DStrAppendChar(tmp, '0');
   }

   DStrReset(int_rep);
   if(negative)
   {
      DStrAppendChar(int_rep, '-');
   }
   DStrAppendStr(int_rep, DStrView(tmp));

   DStrFree(tmp);
}


/*-----------------------------------------------------------------------
//
// Function: normalize_float_rep()
//
//    Take a string representation of a floating point number and turn
//    it into a normal form. The normal form is whatever sprintf()
//    makes of it. Over- and underflow are accepted and ingnored (this
//    is floating point math, after all - what do you expect?).
//
// Global Variables: -
//
// Side Effects    : Memory operations
//
/----------------------------------------------------------------------*/

static void normalize_float_rep(DStr_p float_rep)
{
   double value;
   char* endptr;
   char buff[128];
   int res;

   value = strtod(DStrView(float_rep), &endptr);

   if(fabs(value)>=1000.0)
   {
      res = snprintf(buff, 128, "%e", value);
   }
   else
   {
      res = snprintf(buff, 128, "%f", value);
   }
   UNUSED(res); assert(res < 128);

   DStrSet(float_rep, buff);
}





/*---------------------------------------------------------------------*/
/*                         Exported Functions                          */
/*---------------------------------------------------------------------*/

/*-----------------------------------------------------------------------
//
// Function: FuncSymbParse()
//
//   Parse a function or predicate symbol (or, currently, variable)
//   and store the representation into id.
//
//   Operators are now of the types
//
//   - Identifier
//   - SemIdent
//   - String
//   - SQString
//   - Integers, potentially signed
//   - Reals, potentially signed
//   - Rationals (fractions)
//
//
// Global Variables: SigIdentToken
//
// Side Effects    : Reads input, changes id
//
/----------------------------------------------------------------------*/

FuncSymbType FuncSymbParse(Scanner_p in, DStr_p id)
{
   FuncSymbType res = FSNone;
   StrNumType numtype;

   CheckInpTok(in, FuncSymbStartToken);
   printf("\n*********In FuncSymbParse**********\n");
   printf("%s\n", AktToken(in)->literal->string);
   
   if(TestInpTok(in, FuncSymbToken))
   {
      printf("\nHier werden 'Termsymbole' erkannt\n");
      //Hier sollte ich des ansetzen des ite zu finden und dann dementsprechen "handeln"
      DStrAppendStr(id, DStrView(AktToken(in)->literal));

      if(TestInpTok(in, Identifier))
      {
         if((isupper(DStrView(AktToken(in)->literal)[0])
             ||
             DStrView(AktToken(in)->literal)[0] == '_'))
         {
	    printf("FSIdentVar\n");
            res = FSIdentVar;
         }
         else
         {
	    printf("FSIdentFreeFun\n");
            res = FSIdentFreeFun;
         }
      }
      else
      {
         switch(AktTokenType(in))
         {
         case SemIdent:
 	       printf("\nSemIdent\n");
               res = FSIdentInterpreted;
               break;
         case SQString:
               res = FSIdentFreeFun;
               break;
         case String:
               res = FSIdentObject;
               break;
         default:
               assert(false && "Unexpected token in FuncSymbParse()");
               break;
         }
      }
      AcceptInpTok(in, FuncSymbToken);
   }
   else
   {
      CheckInpTok(in, PosInt|Plus|Hyphen);

      numtype = ParseNumString(in);
      switch(numtype)
      {
      case SNInteger:
            normalize_int_rep(in->accu);
            DStrAppendStr(id, DStrView(in->accu));
            res = FSIdentInt;
            break;
      case SNRational:
            normalize_rational_rep(in->accu);
            DStrAppendStr(id, DStrView(in->accu));
            res = FSIdentRational;
            break;
      case SNFloat:
            normalize_float_rep(in->accu);
            DStrAppendStr(id, DStrView(in->accu));
            res = FSIdentFloat;
            break;
      default:
            assert(false);
            break;
      }
   }
   return res;
}


/*---------------------------------------------------------------------*/
/*                        End of File                                  */
/*---------------------------------------------------------------------*/


