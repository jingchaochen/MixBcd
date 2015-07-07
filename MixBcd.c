/*----------------------------------------------- 
  MixDecompose
see the paper: Fast Blocked Clause Decomposition with High Quality 
Author: Jingchao Chen

Copyright (c) 2015, Jingchao Chen, Donghua University

Permission is hereby granted, free of charge, to use this software for
evaluation and research purposes.

This license does not allow this software to be used in a commercial context.

It is further prohibited to use this software or a substantial portion of it
in a competition or a similar competitive event, such as the SAT, SMT or QBF
competitions or evaluations, without explicit written permission by the
copyright holder.

However, competition organizers are allowed to use this software as part of
the evaluation process of a particular competition, evaluation or
competitive event, if the copyright holder of this software submitted this
software to this particular competition, evaluation or event explicitly.

This permission of using the software as part of a submission by the
copyright holder to a competition, evaluation or competitive event is only
granted for one year and only for one particular instance of the competition
to which this software was submitted by the copyright holder.

If a competition, evaluation or competitive event has multiple tracks,
categories or sub-competitions, this license is only granted for the tracks
respectively categories or sub-competitions, to which the software was
explicitly submitted by the copyright holder.

All other usage is reserved.

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
IN THE SOFTWARE.

--------------------------------------------------
*/

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>
#include <sys/time.h>
#include <sys/times.h>
#include <string.h>
#include <limits.h>
#include <float.h>
#include <getopt.h>
#include <signal.h>

#define ABS(x) ((x)>0?(x):(-x))
#define LLONG long long int

char *fileName;
int nVars;          // numbers of variables. 
int doubleVars;
int nClauses;       // number of clauses.
int *value;         // value of variables : 0=false  1=true 
int nBlocked2;      // number of the first blocked clauses
int *label,*clauseScore;
void flipClause(int *clause);
int maxCsize;       // max clause size
int minCsize;       // min clause size
int **clauses;      // CNF formula: clauses[0..n-1][last] -> clauses[1..n][last],each clause ends at 0
int sumLit;         // the total number of literals
int *clauseMem;
int *marks;
int *lookup_mem;
int unitsum;

int **lookup;       //  clause No. where each literal occurs, lookup[lit][j]:  the j'th clause of literal lit or -lit  
int *occurrences;   // number each literal occurs

long ticks_per_second;
FILE* output;

void readCNFfile() 
{	int i, j;
	printf("c file=%s\n",fileName);
	FILE *fp = fopen(fileName, "r");
	if (fp == NULL) {
		fprintf(stderr, "c Error: cannot open the file: %s\n", fileName);
		exit(-1);
	}
	while(1) {
		char c = fgetc(fp);
		if (c == 'c') //skip comment line
			do {
				c = fgetc(fp); //read the complete comment line
			} while ((c != '\n') && (c != EOF));
		else if (c == 'p') { //paser p-line 
			if ((fscanf(fp, "%*s %d %d", &nVars, &nClauses))) //%*s = "cnf"
			break;
		} else {
			printf("c line <p cnf #vars #clauses> has not found! \n");
            		exit(-1);
		}
	}

	doubleVars = nVars * 2;
        minCsize=100000;
	maxCsize = sumLit=0;
        int  memsize = 2 * nClauses;
	int *cp= (int*) malloc(sizeof(int) * memsize);
        int *tmpClause = (int*) malloc(sizeof(int) *(nVars+1));
	for (i = 0; i < nClauses; i++) {
		int cSize=0;
                int lit;
		do {	fscanf(fp, "%i", &lit);
			tmpClause[cSize++] = lit;
		} while (lit);
                if(sumLit + cSize > memsize){
                    memsize = sumLit + cSize + sumLit/2;
                    cp=(int *)realloc (cp, sizeof(int) * memsize);
        	}
                for (j = 0; j < cSize; j++) cp[sumLit++]=tmpClause[j];
           	if (cSize > maxCsize) maxCsize = cSize;
           	if (cSize < minCsize) minCsize = cSize;
        }
	fclose(fp);
        clauseMem=cp;

        maxCsize--;
        minCsize--;
        free(tmpClause);
        clauses = (int**) malloc(sizeof(int*) * (nClauses+1));

        for (i = 0; i < nClauses; i++) {
               clauses[i] = cp;
               while(*cp) cp++;
               cp++;
        }
        nBlocked2=0;
}

void dispclause(int *pLit)
{  printf("\n");
   while (*pLit) {
       printf("%d ",*pLit);
       pLit++;
   }
}   

void checkData()
{
   int *NewMem =clauseMem;
   readCNFfile();
   int i,lit;
   for (i = -nVars; i <= nVars; ++i) marks[i] = 0;
   int pos=0;
   for(i=0; i<nClauses; i++){
         int *clause = clauses[i];
         int size=0;
         while ((lit=*clause)) {
             clause++;
             if(marks[lit]) break;
             marks[lit]=1;
             size++;
         }
         int size2=0;
         if(lit==0){
              clause = NewMem+pos;
              while ((lit=*clause)) {
                    clause++;
                    if(marks[lit]!=1) break;
                    marks[lit]=0;
                    size2++;
              }
         }

         if(lit || size!=size2){
              dispclause(clauses[i]);
              dispclause(NewMem+pos);
         }
         
         pos += size2 +1;
   }
   printf("c data check is done! \n");        
}

double elapsed_time(void) 
{
	double seconds;
	static struct tms now_tms;
	long prev_times = 0;
	(void) times(&now_tms);
	seconds = ((double) (((long) now_tms.tms_utime) - prev_times)) / ((double) ticks_per_second);
	prev_times = (long) now_tms.tms_utime;
	return seconds;
}

void handle_interrupt() 
{
	printf("\ns UNKNOWN: (%-15.5fsec)\n", elapsed_time());
	exit(-1);
}

void buildSignalHandler() 
{
	signal(SIGTERM, handle_interrupt);
	signal(SIGINT,  handle_interrupt);
	signal(SIGQUIT, handle_interrupt);
	signal(SIGABRT, handle_interrupt);
	signal(SIGKILL, handle_interrupt);
}


void lookup_Mem()
{
     occurrences = (int*) malloc(sizeof(int) * (doubleVars + 1));
     lookup = (int**) malloc(sizeof(int*) * (doubleVars + 1));

     occurrences += nVars;
     lookup  +=  nVars;
 
     int i;
     for (i = -nVars; i <= nVars; i++) occurrences[i] =0;
     int *litp = clauses[0];
     for (i = 0; i <  sumLit; i++) occurrences[*litp++]++;	
     
     occurrences[0]=0;
    
     lookup_mem   = (int*) malloc (sizeof(int) * (sumLit+doubleVars+1));
     int loc= 0;
     for (i = -nVars; i <= nVars; ++i) { 
         lookup[ i ] = lookup_mem + loc;
         loc += occurrences[ i ]+1; // end at 0
     }
}

//BCD ------------------------------------------------------------------------
int *next, last, start, *touched,*stack;
int nBlocked1,nBlocked,nMoved, nRemoved, nRank;
   
inline void addClauseIdx (int index) {
  int *clause = clauses[ index ];
  while (*clause) { int lit = *(clause++); lookup[ lit ][ occurrences[ lit ]++ ] = index; }
}

void removeBlocked_addcandidate (int index, int cut)
{   int* clause = clauses[index];
    while (*clause) {
           int j,lit  = *(clause++);
           for (j = 0; j < occurrences[ lit ]; ++j)
	      if (lookup[ lit ][ j ] == index){
	           lookup[ lit ][ j-- ] = lookup[ lit ][ --occurrences[ lit ] ];
                   break;
              }
              if(occurrences[lit]>1 && (nClauses>800000 || (nVars>900 && cut>0))) continue;
              for (j = 0; j < occurrences[ -lit ]; ++j){
               int cls = lookup[ -lit ][ j ];
	       if (touched[cls]== 0) {
                 touched[ cls ] = 1;
                 if (last == -1) start = cls;
                 else            next[ last ] = cls;
                 last = cls;
                 next[ last ] = last;
             }
          }
    }
}

void part_init()
{ int i;
  for (i = -nVars; i <= nVars; ++i) { 
        occurrences[ i ] = 0; 
        marks[i] = -1; 
  }

  last = -1;
  for (i = 0; i < nClauses; ++i) {
         if(label[i]== 0) continue;
         if (last == -1) start = i;
         else            next[last]= i;
         last = i;
         label[i] = 0;
         addClauseIdx(i);
         touched[i] = 1;
  }
  next[last] = last;
  nMoved = nRemoved = nBlocked = 0;
}

void simple_bce(int cut);

void bcd_init();
void PureDecompose();

void moveBlockable(int *Bstack, int *bcnt)
{    int i,j;

     *bcnt=0;
     for (i = -nVars; i <= nVars; ++i) occurrences[ i ] = 0;
     for (i = 0; i < nClauses; ++i)  if (label[ i ] == 1) addClauseIdx(i);
   
     for (i = 0; i < nClauses; ++i) 
          if (label[ i ] == 2) {
             int *clause = clauses[ i ];
             int sum=0;
             while (*clause) 
             { int lit = *(clause++); marks[ -lit ] = i; 
                   sum += occurrences[-lit];
             }
             if(sum>30000 && nClauses>1000000) continue;
             clause = clauses[ i ];
             int first = *clause;
             int blockable=1;
             while (*clause) {
                 int flag = 1;
                 int lit  = *(clause++);
                 for (j = 0; j < occurrences[ -lit ]; ++j) {
                      int count  = 0;
                      int cls = lookup[ -lit ][ j ];
                      if (label[ cls] != 1) continue;
	              int *check = clauses[ cls ];
                      while (*check) {
	                 if (marks[ *(check++) ] == i) count++;
                         if (count == 2) goto next_check_pure;
                      }
                      flag = 0;
                      if(clauses[ cls ][0]==-lit) blockable=0;
                      if(blockable==0) break; //not blockable
	              next_check_pure:;
                  }
                  if (flag) {
	             label   [ i ]       = 1;
                     clauses [ i ][ 0 ] = lit;
                     clause   [-1 ]     = first;
                     Bstack[(*bcnt)++]=i,
                     addClauseIdx(i);
                     goto next_clause_pure;
                  }
             }

             if(blockable){
	            label[i] = 1;
                    stack[ nBlocked++ ] = i;
                    addClauseIdx(i);
             }
             next_clause_pure:;
       }
}

void PureDecompose()
{    int i,j;
     int *remaining   = (int* ) malloc (sizeof(int ) * (2*nVars+1)); 
     remaining   += nVars;
     for (i = -nVars; i <= nVars; ++i) remaining[ i ] = occurrences[ i ];
     int *priority = (int* ) malloc (sizeof(int ) * (2*nVars+1));
     int p_size = 0;
     for (i =1; i<= nVars; i++) {
         int decision = i;
         if (p_size != 0) decision = priority[ --p_size ], i--;
         if (remaining[decision] < remaining[-decision]) decision *= -1;
         if (remaining[ decision ] == 0) continue;
         for (j = 0; j < occurrences[ decision ]; ++j) {
             int cls = lookup[ decision ][ j ];
             if (label[ cls ] != 0) continue;
             label[ cls ] = 1;
             stack[ nBlocked++ ] = cls;
             int *clause = clauses[ cls ];
             int first = *clause;
             while (*clause) {
                int lit = *(clause++);
                remaining[ lit ]--;
                if (lit != decision){
                      if(remaining[ lit ] == 0) priority[ p_size++ ] = lit;
                }
                else {
                     clauses [ cls ][ 0 ] = lit;
                     clause   [-1 ]      = first;
                }
             }
         }

         for (j = 0; j < occurrences[ -decision ]; ++j) {
             int cls = lookup[ -decision ][ j ];
             if (label[ cls ] != 0) continue;
             label[ cls ] = 2;
             int *clause = clauses[ cls ];
             while (*clause) {
                int lit = *(clause++);
                remaining[ lit ]--;
                if (lit != -decision && remaining[ lit ] == 0) priority[ p_size++ ] = lit;
             }
         }
     }

   nBlocked1=nBlocked;
   free(priority);
   remaining -=  nVars;
   free(remaining);
   return;
}

void MinPureDecompose(int isRand)
{    int i,j;
     int *clauseSize = (int* ) malloc (sizeof(int ) * ( nClauses ));
     int *litsize    = (int* ) malloc (sizeof(int ) * (2*nVars+1)); 
     int *remaining  = (int* ) malloc (sizeof(int ) * (2*nVars+1)); 
 
     litsize    += nVars;
     remaining  += nVars;
     
     for (i = -nVars; i <= nVars; ++i){
            remaining[i] = occurrences[i];
            litsize[i]=0;
     }
     for (i = 0; i < nClauses; ++i) {
          int *clause = clauses[i];
          int size=0;
          while (*clause) { clause++; size++;}
          clauseSize[i]=size;
          clause = clauses[i];
          while (*clause) {litsize[*clause] += size; clause++;}
     }     
 
     int *priority = (int* ) malloc (sizeof(int ) * (2*nVars+1));
     int p_size = 0;
     int decision;
     int dcnt=0;
     int start=-nVars;
     int range;
     if(nVars<70000) range=30000;
     else range=1500;
     for (i =1; i<= nVars; i++) {
         while(p_size){
                  decision = priority[--p_size ];
                  if (remaining[decision] < remaining[-decision]) decision = -decision;
                  if (remaining[decision]) goto split;
         }
         int minLit;
         for (minLit=start; minLit <= nVars; minLit++){
                  if(remaining[minLit]) break;
         }
         if(minLit > nVars) goto done;
         start=minLit;
         if(dcnt%5 || isRand){
              int diff=ABS(remaining[minLit]-remaining[-minLit]);
                  for (j = minLit+1; j <= nVars && j<start+range; j++){
                     if(remaining[j]==0) continue;
                     if(remaining[minLit] > remaining[j]) minLit=j;
                     else {
                        if(remaining[minLit] == remaining[j]){
                             if(litsize[j] < litsize[minLit]) minLit=j;
                        }
                        else{
                             int d2=remaining[j]-remaining[-j];
                             if(diff > ABS(d2)){
                                 minLit=j;
                                 diff=ABS(d2);
                             }
                        }
                     }
                  }
         }
         dcnt++;
         decision = minLit;
         if (remaining[decision] < remaining[-decision]) decision = -decision;
split:
         for (j = 0; j < occurrences[ decision ]; ++j) {
             int cls = lookup[ decision ][ j ];
             if (label[ cls ] != 0) continue;
             label[ cls ] = 1;
             stack[ nBlocked++ ] = cls;
             int *clause = clauses[ cls ];
             int first = *clause;
             while (*clause) {
                int lit = *(clause++);
                remaining[lit ]--;
                litsize[lit] -= clauseSize[cls];
                if (lit != decision){
                      if(remaining[ lit ] == 0) priority[ p_size++ ] = lit;
                }
                else {
                     clauses [ cls ][ 0 ] = lit;
                     clause   [-1 ]       = first;
                }
             }
         }

         for (j = 0; j < occurrences[ -decision ]; ++j) {
             int cls = lookup[ -decision ][ j ];
             if (label[ cls ] != 0) continue;
             label[ cls ] = 2;
             int *clause = clauses[ cls ];
             while (*clause) {
                int lit = *(clause++);
                remaining[lit ]--;
                litsize[lit] -= clauseSize[cls];
                if (lit != -decision && remaining[ lit ] == 0) priority[ p_size++ ] = lit;
             }
         }
     }
done:
   nBlocked1=nBlocked;

   free(priority);
   remaining -=  nVars;
   free(remaining);  
   litsize  -= nVars;
   free(litsize);
   free(clauseSize);
   return;
}

void MaxPureDecompose()
{    int i,j;
     int *remaining  = (int* ) malloc (sizeof(int ) * (2*nVars+1)); 
     remaining  += nVars;
     for (i = -nVars; i <= nVars; ++i) remaining[i] = occurrences[i];
     int *priority = (int* ) malloc (sizeof(int ) * (2*nVars+1));
     int p_size = 0;
     int decision;
     int start=1;
     int range=5000;
     if(nVars > 800000) range=500; 
     for (i =1; i<= nVars; i++) {
         while (p_size){
                  decision = priority[--p_size];
                  if (remaining[decision] < remaining[-decision]) decision = -decision;
                  if (remaining[decision]) goto split;
         }
         int maxLit;
         for (maxLit=start; maxLit <= nVars; maxLit++){
                  if(remaining[maxLit]) break;
         }
         if(maxLit > nVars) goto done;
         start=maxLit;
         int diff=ABS(remaining[maxLit]-remaining[-maxLit]);
         for (j = maxLit+1; j <= nVars && j<start+range; j++){
                  if(remaining[j]==0 && remaining[-j]==0) continue;
                  if(remaining[maxLit] < remaining[j]) maxLit=j;
                  else {
                       int d2=remaining[j]-remaining[-j];
                       if(diff > ABS(d2)){
                               maxLit=j;
                               diff=ABS(d2);
                       }
                    }

         }
         decision = maxLit;
         if (remaining[decision] < remaining[-decision]) decision = -decision;
split:
         for (j = 0; j < occurrences[ decision ]; ++j) {
             int cls = lookup[ decision ][ j ];
             if (label[ cls ] != 0) continue;
             label[ cls ] = 1;
             stack[ nBlocked++ ] = cls;
             int *clause = clauses[ cls ];
             int first = *clause;
             while (*clause) {
                int lit = *(clause++);
                remaining[lit ]--;
                if (lit != decision){
                      if(remaining[lit] == 0) priority[ p_size++ ] = lit;
                }
                else {
                     clauses [ cls ][ 0 ] = lit;
                     clause   [-1 ]      = first;
                }
             }
         }

         for (j = 0; j < occurrences[-decision ]; ++j) {
             int cls = lookup[ -decision ][ j ];
             if (label[ cls ] != 0) continue;
             label[ cls ] = 2;
             int *clause = clauses[ cls ];
             while (*clause) {
                int lit = *(clause++);
                remaining[lit ]--;
                if (lit != -decision && remaining[ lit ] == 0) priority[ p_size++ ] = lit;
             }
         }
     }
done:
   nBlocked1=nBlocked;

   free(priority);
   remaining -=  nVars;
   free(remaining);  
   return;
}

void remove_pure_lit()
{    int i,j;
     int *remaining   = (int* ) malloc (sizeof(int ) * (2*nVars+1)); 
     remaining += nVars;
     for (i = -nVars; i <= nVars; ++i) remaining[ i ] = occurrences[ i ];
     int *priority = (int* ) malloc (sizeof(int ) * (2*nVars+1));
     int p_size = 0;
     for (i =1; i<= nVars; i++) {
         int decision = i;
         if (p_size != 0) decision = priority[--p_size ], i--;
         if (remaining[decision] < remaining[-decision]) decision = -decision;
         if (remaining[ decision ] == 0) continue;
         if (remaining[-decision ]) continue;
         for (j=0; j< occurrences[ decision ]; ++j) {
             int cls = lookup[ decision ][ j ];
             if (label[ cls ] != 2) continue;
             label[ cls ] = 1;
             stack[ nBlocked++ ] = cls;
             int *clause = clauses[ cls ];
             int first = *clause;
             while (*clause) {
                int lit = *(clause++);
                remaining[ lit ]--;
                if (lit != decision){
                      if(remaining[ lit ] == 0) priority[ p_size++ ] = lit;
                }
                else {
                     clauses [ cls ][ 0 ] = lit;
                     clause   [-1 ]      = first;
                }
             }
         }
   }

   nBlocked1=nBlocked;

   free(priority);
   remaining -=  nVars;
   free(remaining);
   return;
}

void simple_bce(int cut)
{  int i,j;
   i = start;
  
  while (1) {
      if (touched[ i ] == 0) goto next_i;
      int *clause = clauses[ i ];
      touched[ i ] = 0;
      while (*clause) { int lit = *(clause++); marks[ -lit ] = i; }

      clause = clauses[ i ];
      int first = *clause;
      while (*clause) {
        int lit  = *(clause++);
     
        if(cut >= 0){
            if (occurrences[-lit]>1 && (nClauses-nBlocked>300000 ||cut)) continue;
        }

        int flag = 1;
        for (j = 0; j < occurrences[ -lit ]; ++j) {
          int count  = 0;
	  int *check = clauses[ lookup[ -lit ][ j ] ];
	  while (*check) {
	    if (marks[ *(check++) ] == i) count++;
            if (count == 2) goto next_check;
          }
          flag = 0; break;
          next_check:;
        }
        if (flag) { // found a blocked clause, update data-structures
           label   [ i ]      = 1;
           clauses  [ i ][ 0 ] = lit;
           clause   [-1 ]      = first;
           stack[ nBlocked++ ] = i;
           nRemoved++;
           removeBlocked_addcandidate (i,cut);
           break;
        }
      }
    next_i:;
    if (next[ i ] == i) break;
    i = next[ i ];
  }
}

inline int equalkey(int *st, int n)
{    int i,eq=0;
     int pivot=clauseScore[st[n/2]];
     for(i=0; i<n; i++)   
         if (clauseScore[st[i]]==pivot) eq++;
     return eq;
}
void find_k_largest(int *st, int n, int k)
{
     if(k>=n-1) return;
    int pivot=clauseScore[st[n/2]];
     int i=0, j=n-1;
     while(i<=j){
         while(clauseScore[st[i]]>pivot && i<=j) i++;
         while(clauseScore[st[j]]<pivot && i<=j) j--;
         if(i>j) break;
         int t=st[i];
         st[i]=st[j];
         st[j]=t;
         i++; j--;
     }
     if(i>=k) find_k_largest(st, i, k);
     else find_k_largest(st+i, n-i, k-i);
}

void re_touch()
{ int i;
  for (i = 0; i < nClauses; ++i) {
         if(label[i]) continue;
         if (last == -1) start = i;
         else            next[last]= i;
         last = i;
         touched[i] = 1;
  }
  next[last] = last;
}

void LessInterfereDecompose(int cut)
{   int i,j,bce=0;
    int p;

    if(maxCsize != minCsize) p=nClauses/200; 
    else p=nClauses/400;
    if(nClauses <= 200000) p=18;
    else if(nClauses <= 800000) p=nClauses/2300;

    int *CNoStack = (int*) malloc(sizeof(int)*200001);
    int CNoSum=0;
    for (i = 0; i < nClauses; ++i) clauseScore[i]=0;
    
    int alpha=40*p;
    if(alpha < 5000) alpha=5000;
    if(alpha>10000 && maxCsize >20) alpha=10000;
    int noneqSz = (maxCsize != minCsize);
  //  printf("c p=%d theta=%d \n",p, nClauses/p);
BCE:
   if(last != -1){
      if(bce==0 && nClauses <2000000) simple_bce(-1);
      else  simple_bce(cut);
   }
   last=-1;
   bce++;
   if (nClauses == nRemoved) {
           free(CNoStack);
           return;
   }
//DECOMPOSITION
    int decision = -1;

    for(i=0; i<p && i<CNoSum; i++){
      if (label[CNoStack[i]]) continue; 
      decision=CNoStack[i];
      goto REMOVE;
    }

    int cnt; 
    if(nClauses>700000){
            cnt=20000;
            if(nClauses>2000000 && maxCsize == minCsize) cnt=2000;
      }
    else{
         cnt=nClauses/2;
         if(cnt<10000) cnt=nClauses;  
    }
    int min_occ = 10000000;
    for (i = 0; i < CNoSum; ++i) clauseScore[CNoStack[i]]=0;
    CNoSum=0;
    for (i=0; i < nClauses; ++i) {
      if (label[ i ]) continue; 
      int *clause = clauses[i];
      while (*clause) {
          int lit=*clause;
          marks[ -lit ] = i;
          if (occurrences[ -lit ] < min_occ) min_occ = occurrences[ -lit ];
          clause++; 
       }
       cnt--;
       if(cnt==0) break;
     }
  
     cnt=0;
     for (i = 0; i < nClauses && (cnt<alpha || CNoSum < p); ++i) {
        if (label[i]) continue; // clause is already in one of the sets;
        int *clause = clauses[ i ];
        while (*clause) {
          int lit = *clause;   
          int m = occurrences[-lit];
          if (m == min_occ) {
             cnt++;
             int cond=noneqSz && ((m>20 && nRemoved > nClauses/2) || nClauses<10000);
             for (j = 0; j < m; ++j) {
                 int cls = lookup[ -lit ][ j ];
                 if(cond){
                      int count = 0;
                      int *check = clauses[ cls ];
	              while (*check)  if (marks[ *(check++) ] == i) count++;
	              if (count == 1) goto addscore;
                 }
                 else{ 
addscore:
                        if(clauseScore[cls]) clauseScore[cls]++;
                         else{
                             if(CNoSum<200000){
                               CNoStack[CNoSum++]=cls;
                               clauseScore[cls]=1;
                          }
                      }                           
                 }
              }
           }
           clause++;
        }
     }

       if(CNoSum==0) {
             re_touch();
             cut=-2;
             goto BCE;
       }
       find_k_largest(CNoStack,CNoSum, p);
       decision = CNoStack[0];
REMOVE:;
      if (decision >= 0) {
          label[ decision ] = 2;
          nRemoved++;  nMoved++;
          removeBlocked_addcandidate (decision,cut);
          goto BCE;
      }
}

void RsetGuidedDecompose(int *preRem, int cut)
{   int i,j,bce=0,rm=0;
    int decision = -1;
BCE:
    if(last != -1){
        if(bce<100) simple_bce(-1);
        else  simple_bce(cut);
    }
    last = -1;
    bce++;
    if (nClauses == nRemoved) return;
//DECOMPOSITION
    while(1){
         decision=preRem[rm];
         if(decision < 0) break;
         rm++;
         if (label[decision]==0) goto REMOVE;
    }
    for (i = 0; i < nClauses; ++i) clauseScore[ i ] = 0;
    int k=0;
    int min_occ=1000000;
    int max_score=-1,maxCls=-1;
    for (i = 0; i < nClauses && k<200; ++i) {
       if (label[ i ]) continue; 
       int *clause = clauses[ i ];
       int flag=0;
       while (*clause) {
          int lit=*clause;
          marks[-lit] = i;
          if (occurrences[-lit] < occurrences[lit]) {
                  if (occurrences[-lit] <= min_occ) {
                      min_occ=occurrences[-lit];
                      flag=1;
                  }
          }
          clause++; 
       }
       if(flag==0) continue;
       k++;
       clause = clauses[ i ];
       while (*clause) {
          int lit = *clause;   
          int m = occurrences[ -lit ];
          if (m == min_occ) {
             for (j = 0; j < m; ++j) {
                 int cls = lookup[-lit][j];
                 int count = 0;
                 int *check = clauses[ cls ];
	         while (*check)  if (marks[ *(check++) ] == i) count++;
	         if (count == 1) clauseScore[ cls ]++;
                 if(clauseScore[cls]>max_score){
                      max_score=clauseScore[cls];
                      maxCls=cls;
                 }
              }
           }
           clause++;
      }
    }
    if(maxCls < 0){
           for (i = 0; i < nClauses ; ++i) {
               if (label[ i ]==0) {maxCls=i; break;}
           }    
    }
    decision = maxCls;
REMOVE:;
      if (decision >= 0) {
          label[ decision ] = 2;
          nRemoved++;  nMoved++;
          removeBlocked_addcandidate (decision,cut);
          goto BCE;
      }
 }

void flipClause(int *clause)
{   
    int *first=clause;
    while (*clause) {
      int var=ABS(*clause);
      if (value[var] == (*clause > 0)) return;
      clause++;
    }
    clause--;
    while (clause >= first) {
      int lit=*clause--;
      if (value[ABS(lit) ] == 2){// any
              value[ABS(lit)] = (lit > 0);
              return;
      }
    }
    value[ ABS(*first) ] = (*first > 0);
}

void bcd_init()
{  int i;
  for (i = -nVars; i <= nVars; ++i) { 
        occurrences[ i ] = 0; 
        marks[i] = -1; 
  }

  for (i = 0; i < nClauses; ++i) {
    next    [ i ] = i + 1;
    label   [ i ] = 0;  // 1: blocked 2:moved 0:any 
    addClauseIdx(i);
    touched[ i ] = 1; 
  }
  last = nClauses - 1;
  next[last] = last;
  nMoved = nRemoved = nRank = start = nBlocked = 0;
}
 
void copyRightSet(int *Rset)
{  int i,k=0;
   for (i = 0; i < nClauses; ++i) {
        if(label[i]==2) Rset[k++]=i;
   }
   Rset[k]=-1;
}

void detectUnit()
{  int lit,i,ulit;
   int ucnt=1;

   unitsum=0;
   while(ucnt){
      ucnt=0;
      for(i=0; i<nClauses; i++){
         int *clause = clauses[i];
         int cnt=0;
         while ((lit=*clause)) {
           clause++;
           if(value[ABS(lit)]==2){
                 if(cnt>=1) goto nextCls;
                 cnt=1;
                 ulit=lit;
                 continue;
           }
           if(value[ABS(lit)]==(lit>0)) goto nextCls;
         }
         if(cnt==1){
             value[ABS(ulit)]=(ulit>0);
             ucnt++;
         }
     nextCls: ;
     }
     unitsum += ucnt;
  }
  printf("c # unit var: %d \n",unitsum);
  if(unitsum){
//remove
      int ncls=0;
      for(i=0; i<nClauses; i++){
         int *clause = clauses[i];
         while ((lit=*clause)) {
           clause++;
           if(value[ABS(lit)]==(lit>0)) goto nextc;
         }
         clauses[ncls++]=clauses[i];
       nextc:;
      }
      printf("c # clauses: %d, # removed clauses: %d \n",ncls,nClauses-ncls);
      nClauses=ncls;
  }
} 


void MixDecompose(int pure_mode) 
{  int i,cut=0;
   double percent;

  printf("c MixDecompose...\nc # var: %d,  #clause: %d \n", nVars, nClauses);
  printf("c max clause size: %d, min clause size=: %d \n",maxCsize,minCsize); 
  fflush(stdout);
  
  for (i = 0; i <= nVars; ++i) value[i] = 2;//any
  if(minCsize==1) detectUnit();

  stack       = (int* ) malloc (sizeof(int ) * ( nClauses ));
  touched     = (int* ) malloc (sizeof(int ) * ( nClauses ));
  next        = (int* ) malloc (sizeof(int ) * ( nClauses ));
  clauseScore = (int* ) malloc (sizeof(int ) * ( nClauses ));
  label       = (int* ) malloc (sizeof(int ) * ( nClauses ));
  marks       = (int* ) malloc (sizeof(int ) * (2*nVars+1)); 
  marks       += nVars;
  bcd_init();

  if (pure_mode) PureDecompose();
  else  {
       int  *Rset=(int* ) malloc (sizeof(int )*(nClauses));
       int pre_nBlocked=0;

       MaxPureDecompose();
       percent = (nBlocked * 100.0) / nClauses;
       printf("c MaxPureDecompose # blocked=%d %f\n",nBlocked,percent);
       fflush(stdout);
       pre_nBlocked=nBlocked;
       copyRightSet(Rset);

       bcd_init();
       PureDecompose();
       percent = (nBlocked * 100.0) / nClauses;
       printf("c PureDecompose # blocked=%d %f\n",nBlocked,percent);
       fflush(stdout);
       if(pre_nBlocked<nBlocked){
              pre_nBlocked=nBlocked;
              copyRightSet(Rset);
       }

       bcd_init();
       int isRand=0;
       if(maxCsize==minCsize) isRand=1; 
       MinPureDecompose(isRand); 
       percent = (nBlocked * 100.0) / nClauses;
       printf("c MinPureDecompose # blocked=%d %f\n",nBlocked,percent);
       fflush(stdout);
       if(pre_nBlocked<nBlocked){
               pre_nBlocked=nBlocked;
               copyRightSet(Rset);
       }

       if(nClauses<5000000 && nVars<1000000){ 
              bcd_init();
              if(maxCsize==minCsize){
                     if(nClauses<600000) cut=-1;
                      else cut=1;
               }
               else if(minCsize>=2) cut=1;
               LessInterfereDecompose(cut);
               percent = (nBlocked * 100.0) / nClauses;
               printf("c LessInterfereDecompose # blocked=%d %f\n",nBlocked,percent);
               if(pre_nBlocked<nBlocked)  copyRightSet(Rset);
        }
        if(nMoved>0){
            printf("c post-processing: RsetGuidedDecompose\n");
            bcd_init();
            RsetGuidedDecompose(Rset,cut);
        }
        free(Rset);
        nBlocked1=nBlocked;
   }

   int *Bstack = (int* ) malloc (sizeof(int ) * ( nClauses-nBlocked));
   int bcnt=0;

   if(nClauses<10000000 && nMoved>0){ 
      printf("c Move blocked and blockable....\n");
      moveBlockable(Bstack,&bcnt);
   }

   printf("c # first part of blocked =%d,  previous right set =%d, # blocked=%d, moved blocked=%d\n",
      nBlocked1,nMoved,nBlocked,bcnt);
   fflush(stdout);

   int **newclauses = (int**) malloc(sizeof(int*) * (nClauses + 1));
   nBlocked2=1;

//first part
  for (i = nBlocked - 1; i >= 0; --i) newclauses[nBlocked2++]=clauses[stack[i]];
//second part
   for (i = 0; i < bcnt; i++) {
          newclauses[nBlocked2++]=clauses[Bstack[i]];
          stack[nBlocked++]=Bstack[i];
   }
   free(Bstack);

   percent = (100.0*nBlocked) / nClauses;
   double percent2 = (100.0*nBlocked) / (nClauses+unitsum);
   printf("c MixDecompose: Blocked %i out of  %i clauses %f%%, %i remain %f%%, %f%% under unit+clauses\n",
          nBlocked, nClauses, percent, nClauses - nBlocked, 100.0-percent,percent2);
   double totalTime = elapsed_time();
   printf("c %-30s: %-8.3fsec\n", "total time", totalTime);
   printf("\nc check assignment # blocked =%d \n",nBlocked2);
   fflush(stdout);

   for (i = 1; i < nBlocked2; i++) flipClause(newclauses[i]);

   if(output != stdout){
        fprintf(output, "p cnf %i %i\n", nVars, nBlocked2-1);
        for (i = 1; i < nBlocked2; i++){
             int *clause = newclauses[i];
             while (*clause) fprintf(output, "%i ", *clause++);
             fprintf(output, "0\n");
         }
   }
    
   for (i = 1; i < nBlocked2; i++){
      int *clause = newclauses[i];
      int  blocking_literal = *clause;
      while (*clause) {
      if (value[ABS(*clause)] == (*clause >0) ) goto next_clause_error;
         clause++; 
      }
      int j=nBlocked2-i;
      printf("c Fail to forcing blocking literal %i=%d to true (stack  %i)\n", blocking_literal, 
        value[ABS(blocking_literal)], stack[j]);
      exit(1);
      next_clause_error : ;
  }

// Right blocked set -------------------------------------------------------------
  for (i = -nVars; i <= nVars; ++i) occurrences[i]=0; 
  for (i = 0; i < nClauses; ++i) 
      if(label[ i ] == 2)  addClauseIdx(i);

  remove_pure_lit();
 
  if(nBlocked < nClauses ){
      for (i = -nVars; i <= nVars; ++i) { 
          occurrences[ i ] = 0; 
          marks[i] = -1; 
      }
 
      last = -1;
      for (i = 0; i < nClauses; ++i) {
          if(label[ i ] == 2){
             if (last == -1) start = i;
             else            next[last]= i;
             last = i;
             label[i] = 0;
             addClauseIdx(i);
             touched[i] = 1;
          }
          else  touched[i]= 0; 
      }
      if(last == -1) {
           if( nBlocked < nClauses ){
               printf("c : # blocked=%d # clauses=%d \n",nBlocked,nClauses);
               exit(-1);
           }
           goto disp;
      }
      next[last] = last;
      nRemoved = nBlocked;
      nMoved = nRank = 0;
      LessInterfereDecompose(cut);
  }
disp:;  

  int k = nBlocked2; 
  for (i = nBlocked - 1; i >= nBlocked2-1; --i) newclauses[k++]=clauses[stack[i]];
  if(k <= nClauses){
         for (i = 0; i < nClauses; ++i) 
              if(label[ i ] == 2){
                      newclauses[k++]=clauses[i];
                      stack[nBlocked++]=i;
               }
  } 

   for (i = 0; i < nBlocked; i++) label[stack[i]]=-2;
   k=0;
   for (i = 0; i < nClauses; i++){
         if(label[i]!=-2) {
            printf("c error %d %d \n",i,k++);
            break;
         }
    }
          
   free(clauses);
   clauses = newclauses;

  free(stack);
  free(touched);
  free(next);
  free(clauseScore);
  free(label);

  checkData();

  marks -= nVars;
  free(marks);
  return;
}

int main(int argc, char *argv[]) 
{
       ticks_per_second = sysconf(_SC_CLK_TCK);

        if((argc !=2 && argc !=3)  || (argv[1][0] == '-' && argv[1][1] == 'h')){
           printf("usage: ./MixBcd CNF formula [<output>]\n");
           return 0;
        }
        printf("c MixBcd: Fast blocked clause decomposition by Chen, July 1, 2015\n");
    
        fileName = argv[1];
        if (argc == 3) output = fopen(argv[2], "w");
        else output = stdout;

	buildSignalHandler();

	readCNFfile();
	value = (int*) malloc(sizeof(int) * (nVars + 1));
        lookup_Mem();
        MixDecompose(0);

	double totalTime = elapsed_time();
	printf("c %-30s: %-8.3fsec\n", "final time", totalTime);
	return 0;
}

