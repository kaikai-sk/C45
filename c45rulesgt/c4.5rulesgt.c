/*************************************************************************/
/*									 */
/*		Definitions used in C4.5				 */
/*              ------------------------				 */
/*									 */
/*************************************************************************/


#include <stdio.h>
#include <math.h>

#define	 Eof			EOF             /*char read on end of file*/
#define	 Nil			0               /*null pointer*/
#define	 false			0 
#define	 true			1 
#define	 None			-1
#define	 Epsilon                1E-3

//long	 random();
#define	 Random			((rand()&2147483647) / 2147483648.0)

#define	 Max(a,b)               ((a)>(b) ? a : b) 
#define	 Min(a,b)               ((a)<(b) ? a : b) 
#define	 Round(x)		((int) (x+0.5))
#define	 Log2			0.69314718055994530942
#define	 Log(x)			((x) <= 0 ? 0.0 : log((float)x) / Log2)

#define	 Bit(b)			(1 << (b))
#define	 In(b,s)		((s[(b) >> 3]) & Bit((b) & 07))
#define	 ClearBits(n,s)		memset(s,0,n)
#define	 CopyBits(n,f,t)	memcpy(t,f,n)
#define	 SetBit(b,s)		(s[(b) >> 3] |= Bit((b) & 07))

#define	 ForEach(v,f,l)		for(v=f ; v<=l ; ++v) 

#define	 Verbosity(d)		if(VERBOSITY >= d)

#define	 Check(v,l,h)\
	     if ( v<l||v>h ) {printf("\t** illegal value **\n"); exit(1);}
/*************************************************************************/
/*									 */
/*		Type definitions for C4.5				 */
/*              -------------------------				 */
/*									 */
/*************************************************************************/


typedef  char	Boolean, *String, *Set;

typedef  int	ItemNo;		/* data item number */
typedef  float	ItemCount;	/* count of (partial) items */

typedef  short	ClassNo,	/* class number, 0..MaxClass */
		DiscrValue;	/* discrete attribute value (0 = ?) */
typedef  short	Attribute;	/* attribute number, 0..MaxAtt */

typedef  union  _attribute_value
	 {
	    DiscrValue	_discr_val;
	    float	_cont_val;
	 }
	 	AttValue, *Description;

#define  CVal(Case,Attribute)   Case[Attribute]._cont_val
#define  DVal(Case,Attribute)   Case[Attribute]._discr_val
#define  Class(Case)		Case[MaxAtt+1]._discr_val

#define  Unknown  -999		/* unknown value for continuous attribute */


#define  BrDiscr	1	/* node types:	branch */
#define  ThreshContin	2	/*		threshold cut */
#define  BrSubset	3	/*		subset test */

typedef  struct _tree_record *Tree;
typedef  struct _tree_record
	 {
	    short	NodeType;	/* 0=leaf 1=branch 2=cut 3=subset */
	    ClassNo	Leaf;		/* most frequent class at this node */
	    ItemCount	Items,		/* no of items at this node */
			*ClassDist,	/* class distribution of items */
	    		Errors;		/* no of errors at this node */
	    Attribute	Tested; 	/* attribute referenced in test */
	    short	Forks;		/* number of branches at this node */
	    float	Cut,		/* threshold for continuous attribute */
		  	Lower,		/* lower limit of soft threshold */
		  	Upper;		/* upper limit ditto */
	    Set         *Subset;	/* subsets of discrete values  */
	    Tree	*Branch;	/* Branch[x] = (sub)tree for outcome x */
	 }
		TreeRec;

#define  IGNORE		1	/* special attribute status: do not use */
#define  DISCRETE	2	/* ditto: collect values as data read */


typedef short	RuleNo;			/* rule number */


typedef struct TestRec *Test;

struct TestRec
       {
	   short	NodeType;	/* test type (see tree nodes) */
	   Attribute	Tested;		/* attribute tested */
	   short	Forks;		/* possible branches */
	   float	Cut;		/* threshold (if relevant) */
	   Set		*Subset;	/* subset (if relevant) */
       };


typedef struct CondRec *Condition;

struct CondRec
       {
	   Test		CondTest;	/* test part of condition */
	   short	TestValue;	/* specified outcome of test */
       };


typedef struct ProdRuleRec PR;

struct ProdRuleRec
       {
	   short	Size;		/* number of conditions */
	   Condition	*Lhs;		/* conditions themselves */
	   ClassNo	Rhs;		/* class given by rule */
	   float	Error,		/* estimated error rate */
			Bits;		/* bits to encode rule */
	   ItemNo	Used,		/* times rule used */
			Incorrect;	/* times rule incorrect */
       };


typedef struct RuleSetRec RuleSet;

struct RuleSetRec
       {
	   PR		*SRule;		/* rules */
	   RuleNo	SNRules,	/* number of rules */
			*SRuleIndex;	/* ranking of rules */
	   ClassNo	SDefaultClass;	/* default class for this ruleset */
    };
/*************************************************************************/
/*									 */
/*  Main routine for constructing sets of production rules from trees	 */
/*  -----------------------------------------------------------------	 */
/*									 */
/*************************************************************************/




	/*  External data.  Note: uncommented variables have the same meaning
	    as for decision trees  */

short		MaxAtt, MaxClass, MaxDiscrVal;

ItemNo		MaxItem;

Description	*Item;

DiscrValue	*MaxAttVal;

char		*SpecialStatus;

String		*ClassName,
		*AttName,
		**AttValName,
		FileName = "DF";

short		VERBOSITY = 0,
		TRIALS;

Boolean		UNSEENS	  = false,
		SIGTEST	  = false,	/* use significance test in rule pruning */
		SIMANNEAL = false;	/* use simulated annealing */

float		SIGTHRESH   = 0.05,
		CF	    = 0.25,
		REDUNDANCY  = 1.0;	/* factor that guesstimates the
					   amount of redundancy and
					   irrelevance in the attributes */

PR		*Rule;			/* current rules */

RuleNo		NRules = 0,		/* number of current rules */
		*RuleIndex;		/* rule index */

short		RuleSpace = 0;		/* space allocated for rules */

ClassNo		DefaultClass;		/* current default class */

RuleSet		*PRSet;			/* sets of rulesets */

float		AttTestBits,		/* bits to encode tested att */
		*BranchBits;		/* ditto attribute value */

int optind = 1;
char *optarg;


    getopt(Argc, Argv, Str)
/*  ------  */
    int Argc;
    char **Argv, *Str;
{
    int Optchar;
    char *Option;

    if ( optind >= Argc ) return EOF;

    Option = Argv[optind++];

    if ( *Option++ != '-' ) return '?';

    Optchar = *Option++;

    while ( *Str && *Str != Optchar ) Str++;
    if ( ! *Str ) return '?';

    if ( *++Str == ':' )
    {
	if ( *Option ) optarg = Option;
	else
	if ( optind < Argc ) optarg = Argv[optind++];
	else
	Optchar = '?';
    }

    return Optchar;
}

    main(Argc, Argv)
/*  ----  */
    int Argc;
    char *Argv[];
{
    int o;
    extern char *optarg;
    Boolean FirstTime=true;

    PrintHeader("rule generator");

    /*  Process options  */

    while ( (o = getopt(Argc, Argv, "f:uv:c:r:F:a")) != EOF )
    {
	if ( FirstTime )
	{
	    printf("\n    Options:\n");
	    FirstTime = false;
	}

	switch (o)
	{
	    case 'f':	FileName = optarg;
			printf("\tFile stem <%s>\n", FileName);
			break;
	    case 'u':	UNSEENS = true;
			printf("\tRulesets evaluated on unseen cases\n");
			break;
	    case 'v':	VERBOSITY = atoi(optarg);
			printf("\tVerbosity level %d\n", VERBOSITY);
			break;
	    case 'c':	CF = atof(optarg);
			printf("\tPruning confidence level %g%%\n", CF);
			Check(CF, 0, 100);
			CF /= 100;
			break;
	    case 'r':	REDUNDANCY = atof(optarg);
			printf("\tRedundancy factor %g\n", REDUNDANCY);
			Check(REDUNDANCY, 0, 10000);
			break;
	    case 'F':	SIGTHRESH = atof(optarg);
			printf("\tSignificance test in rule pruning, ");
			printf("threshold %g%%\n", SIGTHRESH);
			Check(SIGTHRESH, 0, 100);
		 	SIGTHRESH /= 100;
			SIGTEST = true;
			break;
	    case 'a':	SIMANNEAL = true;
			printf("\tSimulated annealing for selecting rules\n");
			break;
	    case '?':	printf("unrecognised option\n");
			exit(1);
	}
    }

    /*  Initialise  */

    GetNames();
    GetData(".data");
    printf("\nRead %d cases (%d attributes) from %s\n",
	   MaxItem+1, MaxAtt+1, FileName);

    GenerateLogs();

    /*  Construct rules  */

    GenerateRules();

    /*  Evaluations  */

    printf("\n\nEvaluation on training data (%d items):\n", MaxItem+1);
    EvaluateRulesets(true);

    /*  Save current ruleset  */

    SaveRules();

    if ( UNSEENS )
    {
	GetData(".test");
	printf("\nEvaluation on test data (%d items):\n", MaxItem+1);
	EvaluateRulesets(false);
    }

    exit(0);
}
/*************************************************************************/
/*								  	 */
/*	Miscellaneous routines for rule handling		  	 */
/*	----------------------------------------		  	 */
/*								  	 */
/*************************************************************************/



extern  FILE	*TRf;		/* rules file */


Test	*TestVec;
short	NTests = 0;

FILE	*fopen();
extern char	Fn[500];	/* file name */


/*************************************************************************/
/*								  	 */
/*  Save the current ruleset in rules file in order of the index  	 */
/*								  	 */
/*************************************************************************/


    SaveRules()
/*  ----------  */
{
    short ri, d, v, Bytes;
    RuleNo r;
    Test Tst;

    if ( TRf ) fclose(TRf);

    strcpy(Fn, FileName);
    strcat(Fn, ".rules");
    if ( ! ( TRf = fopen(Fn, "w") ) ) Error(0, Fn, " for writing");
    
    StreamOut((char *) &NRules, sizeof(RuleNo));
    StreamOut((char *) &DefaultClass, sizeof(ClassNo));

    ForEach(ri, 1, NRules)
    {
	r = RuleIndex[ri];
        StreamOut((char *) &Rule[r].Size, sizeof(short));
	ForEach(d, 1, Rule[r].Size)
	{
	    Tst = Rule[r].Lhs[d]->CondTest;

	    StreamOut((char *) &Tst->NodeType, sizeof(short));
	    StreamOut((char *) &Tst->Tested, sizeof(Attribute));
	    StreamOut((char *) &Tst->Forks, sizeof(short));
	    StreamOut((char *) &Tst->Cut, sizeof(float));
	    if ( Tst->NodeType == BrSubset )
	    {
		Bytes = (MaxAttVal[Tst->Tested]>>3) + 1;
		ForEach(v, 1, Tst->Forks)
		{
		    StreamOut((char *) Tst->Subset[v], Bytes);
		}
	    }
	    StreamOut((char *) &Rule[r].Lhs[d]->TestValue, sizeof(short));
	}
	StreamOut((char *) &Rule[r].Rhs, sizeof(ClassNo));
	StreamOut((char *) &Rule[r].Error, sizeof(float));
    }

    SaveDiscreteNames();
}



/*************************************************************************/
/*                                                                	 */
/*	Get a new ruleset from rules file			  	 */
/*                                                                	 */
/*************************************************************************/


    GetRules()
/*  ---------  */
{
    RuleNo nr, r;
    short n, d, v, Bytes;
    Condition *Cond;
    Test Tst, FindTest();
    ClassNo c;
    float e;
    Boolean NewRule();

    if ( TRf ) fclose(TRf);

    strcpy(Fn, FileName);
    strcat(Fn, ".rules");
    if ( ! ( TRf = fopen(Fn, "r") ) ) Error(0, Fn, "");
    
    StreamIn((char *) &nr, sizeof(RuleNo));
    StreamIn((char *) &DefaultClass, sizeof(ClassNo));

    ForEach(r, 1, nr)
    {
        StreamIn((char *) &n, sizeof(short));
	Cond = (Condition *) calloc(n+1, sizeof(Condition));
	ForEach(d, 1, n)
	{
	    Tst = (Test) malloc(sizeof(struct TestRec));

	    StreamIn((char *) &Tst->NodeType, sizeof(short));
	    StreamIn((char *) &Tst->Tested, sizeof(Attribute));
	    StreamIn((char *) &Tst->Forks, sizeof(short));
	    StreamIn((char *) &Tst->Cut, sizeof(float));
	    if ( Tst->NodeType == BrSubset )
	    {
		Tst->Subset = (Set *) calloc(Tst->Forks + 1, sizeof(Set));

		Bytes = (MaxAttVal[Tst->Tested]>>3) + 1;
		ForEach(v, 1, Tst->Forks)
		{
		    Tst->Subset[v] = (Set) malloc(Bytes);
		    StreamIn((char *) Tst->Subset[v], Bytes);
		}
	    }

	    Cond[d] = (Condition) malloc(sizeof(struct CondRec));
	    Cond[d]->CondTest = FindTest(Tst);
	    StreamIn((char *) &Cond[d]->TestValue, sizeof(short));
	}
	StreamIn((char *) &c, sizeof(ClassNo));
	StreamIn((char *) &e, sizeof(float));
	NewRule(Cond, n, c, e);
	free(Cond);
    }

    RecoverDiscreteNames();
}



/*************************************************************************/
/*								  	 */
/*  Find a test in the test vector; if it's not there already, add it	 */
/*								  	 */
/*************************************************************************/


Test FindTest(Newtest)
/*   ---------  */
    Test Newtest;
{
    static short TestSpace=0;
    short i;
    Boolean SameTest();

    ForEach(i, 1, NTests)
    {
	if ( SameTest(Newtest, TestVec[i]) )
	{
	    free(Newtest);
	    return TestVec[i];
	}
    }

    NTests++;
    if ( NTests >= TestSpace )
    {
	TestSpace += 1000;
	if ( TestSpace > 1000 )
	{
	    TestVec = (Test *) realloc(TestVec, TestSpace * sizeof(Test));
	}
	else
	{
	    TestVec = (Test *) malloc(TestSpace * sizeof(Test));
	}
    }

    TestVec[NTests] = Newtest;

    return TestVec[NTests];
}



/*************************************************************************/
/*								  	 */
/*	See if test t1 is the same test as test t2		  	 */
/*								  	 */
/*************************************************************************/


Boolean SameTest(t1, t2)
/*      ---------  */
    Test t1, t2;
{
    short i;

    if ( t1->NodeType != t2->NodeType ||
	t1->Tested != t2->Tested )
    {
	return false;
    }

    switch ( t1->NodeType )
    {
	case BrDiscr:       return true;
	case ThreshContin:  return  t1->Cut == t2->Cut;
	case BrSubset:      ForEach(i, 1, t1->Forks)
			    {
		 		if ( t1->Subset[i] != t2->Subset[i] )
				{
				    return false;
				}
			    }
    }
    return true;
}



/*************************************************************************/
/*								  	 */
/*		Clear for new set of rules			  	 */
/*								  	 */
/*************************************************************************/


    InitialiseRules()
/*  ----------------  */
{
    NRules = 0;
    Rule = 0;
    RuleSpace = 0;
}



/*************************************************************************/
/*								  	 */
/*  Add a new rule to the current ruleset, by updating Rule[],	  	 */
/*  NRules and, if necessary, RuleSpace				  	 */
/*								  	 */
/*************************************************************************/


Boolean NewRule(Cond, NConds, TargetClass, Err)
/*       -------  */
    Condition Cond[];
    short NConds;
    ClassNo TargetClass;
    float Err;
{
    short d, r;
    Boolean SameRule();

    /*  See if rule already exists  */

    ForEach(r, 1, NRules)
    {
	if ( SameRule(r, Cond, NConds, TargetClass) )
	{
	    Verbosity(1) printf("\tduplicates rule %d\n", r);

	    /*  Keep the most pessimistic error estimate  */

	    if ( Err > Rule[r].Error )
	    {
		Rule[r].Error = Err;
	    }

	    return false;
	}
    }

    /*  Make sure there is enough room for the new rule  */

    NRules++;
    if ( NRules >= RuleSpace )
    {
	RuleSpace += 100;
	if ( RuleSpace > 100 )
	{
	    Rule = (PR *) realloc(Rule, RuleSpace * sizeof(PR));
	}
	else
	{
	    Rule = (PR *) malloc(RuleSpace * sizeof(PR));
	}
    }

    /*  Form the new rule  */

    Rule[NRules].Size = NConds;
    Rule[NRules].Lhs = (Condition *) calloc(NConds+1, sizeof(Condition));
    ForEach(d, 1, NConds)
    {
	Rule[NRules].Lhs[d] = (Condition) malloc(sizeof(struct CondRec));

	Rule[NRules].Lhs[d]->CondTest = Cond[d]->CondTest;
	Rule[NRules].Lhs[d]->TestValue = Cond[d]->TestValue;
    }
    Rule[NRules].Rhs = TargetClass;
    Rule[NRules].Error = Err;

    Verbosity(1) PrintRule(NRules);

    return true;
}



/*************************************************************************/
/*								  	 */
/*  Decide whether the given rule duplicates rule r		  	 */
/*								  	 */
/*************************************************************************/


Boolean SameRule(r, Cond, NConds, TargetClass)
/*      --------  */
    RuleNo r;
    Condition Cond[];
    short NConds;
    ClassNo TargetClass;
{
    short d, i;
    Test SubTest1, SubTest2;

    if ( Rule[r].Size != NConds || Rule[r].Rhs != TargetClass )
    {
	return false;
    }

    ForEach(d, 1, NConds)
    {
	if ( Rule[r].Lhs[d]->CondTest->NodeType != Cond[d]->CondTest->NodeType ||
	     Rule[r].Lhs[d]->CondTest->Tested   != Cond[d]->CondTest->Tested )
	{
	    return false;
	}

	switch ( Cond[d]->CondTest->NodeType )
	{
	    case BrDiscr:
		if ( Rule[r].Lhs[d]->TestValue != Cond[d]->TestValue )
		{
		    return false;
		}
		break;

	    case ThreshContin:
		if ( Rule[r].Lhs[d]->CondTest->Cut != Cond[d]->CondTest->Cut )
		{
		    return false;
		}
		break;

	    case BrSubset:
		SubTest1 = Rule[r].Lhs[d]->CondTest;
		SubTest2 = Cond[d]->CondTest;
		ForEach(i, 1, SubTest1->Forks)
		{
		    if ( SubTest1->Subset[i] != SubTest2->Subset[i] )
		    {
			return false;
		    }
		}
	}
    }

    return true;
}



/*************************************************************************/
/*								  	 */
/*		Print the current indexed ruleset		  	 */
/*								  	 */
/*************************************************************************/


    PrintIndexedRules()
/*  -----------------  */
{
    short ri;

    ForEach(ri, 1, NRules )
    {
	PrintRule(RuleIndex[ri]);
    }
    printf("\nDefault class: %s\n", ClassName[DefaultClass]);
}



/*************************************************************************/
/*								  	 */
/*		Print the rule r				  	 */
/*								  	 */
/*************************************************************************/


    PrintRule(r)
/*  ---------  */
    RuleNo r;
{
    short d;

    printf("\nRule %d:\n", r);
    ForEach(d, 1, Rule[r].Size)
    {
        printf("    ");
        PrintCondition(Rule[r].Lhs[d]);
    }
    printf("\t->  class %s  [%.1f%%]\n",
	    ClassName[Rule[r].Rhs], 100 * (1 - Rule[r].Error));
}



/*************************************************************************/
/*								  	 */
/*	Print a condition c of a production rule		  	 */
/*								  	 */
/*************************************************************************/


    PrintCondition(c)
/*  --------------  */
    Condition c;
{
    Test tp;
    DiscrValue v, pv, Last, Values=0;
    Boolean First=true;
    Attribute Att;

    tp = c->CondTest;
    v = c->TestValue;
    Att = tp->Tested;

    printf("\t%s", AttName[Att]);

    if ( v < 0 )
    {
	printf(" is unknown\n");
	return;
    }

    switch ( tp->NodeType )
    {
	case BrDiscr:
	    printf(" = %s\n", AttValName[Att][v]);
	    break;

	case ThreshContin:
	    printf(" %s %g\n", ( v == 1 ? "<=" : ">" ), tp->Cut);
	    break;

	case BrSubset:
	    /*  Count values at this branch  */

	    for ( pv=1 ; Values <= 1 && pv <= MaxAttVal[Att] ; pv++ )
	    {
		if ( In(pv, tp->Subset[v]) )
		{
		    Last = pv;
		    Values++;
		}
	    }

	    if ( Values == 1 )
	    {
		printf(" = %s\n", AttValName[Att][Last]);
		break;
	    }

	    printf(" in ");
	    ForEach(pv, 1, MaxAttVal[Att])
	    {
		if ( In(pv, tp->Subset[v]) )
		{
		    if ( First )
		    {
			printf("{");
			First = false;
		    }
		    else
		    {
			printf(", ");
		    }
		    printf("%s", AttValName[Att][pv]);
		}
	    }
	    printf("}\n");
    }
}
/*************************************************************************/
/*									 */
/*	Tabluate logs and log factorials (to improve speed)		 */
/*	--------------------------------				 */
/*									 */
/*************************************************************************/




float	*LogItemNo;
double	*LogFact;


/*************************************************************************/
/*									 */
/*  Set up the array LogItemNo to contain the logs of integers and	 */
/*  the array LogFact to contain logs of factorials (all to base 2)	 */
/*									 */
/*************************************************************************/


    GenerateLogs()
/*  ------------  */
{
    ItemNo i;

    LogItemNo = (float *) malloc((MaxItem+100) * sizeof(float));
    LogFact = (double *) malloc((MaxItem+100) * sizeof(double));

    LogItemNo[0] = -1E38;
    LogItemNo[1] = 0;
    LogFact[0] = LogFact[1] = 0;

    ForEach(i, 2, MaxItem+99)
    {
	LogItemNo[i] = log((float) i) / Log2;
	LogFact[i] = LogFact[i-1] + LogItemNo[i];
    }
}
/*************************************************************************/
/*									 */
/*	Generate all rulesets from the decision trees		  	 */
/*	---------------------------------------------		  	 */
/*								  	 */
/*************************************************************************/




/*************************************************************************/
/*								  	 */
/*  For each tree, form a set of rules and process them, then form a	 */
/*  composite set of rules from all of these sets.		  	 */
/*  If there is only one tree, then no composite set is formed.	  	 */
/*								  	 */
/*  Rulesets are stored in  PRSet[0]  to  PRSet[TRIALS], where    	 */
/*  PRSet[TRIALS] contains the composite ruleset.		  	 */
/*								  	 */
/*  On completion, the current ruleset is the composite ruleset (if one	 */
/*  has been made), otherwise the ruleset from the single tree. 	 */
/*								  	 */
/*************************************************************************/


    GenerateRules()
/*  -------------  */
{
    Tree DecisionTree, GetTree();
    short t=0, RuleSetSpace=0, r;

    /*  Find bits to encode attributes and branches  */

    FindTestCodes();

    /*  Now process each decision tree  */

    while ( DecisionTree = GetTree(".unpruned") )
    {
	printf("\n------------------\n");
	printf("Processing tree %d\n", t);

	/*  Form a set of rules from the next tree  */

	FormRules(DecisionTree);

	/*  Process the set of rules for this trial  */

	ConstructRuleset();

	printf("\nFinal rules from tree %d:\n", t);
	PrintIndexedRules();
	    
	/*  Make sure there is enough room for the new ruleset  */

	if ( t + 1 >= RuleSetSpace )
	{
	    RuleSetSpace += 10;

	    if ( RuleSetSpace > 10 )
	    {
		PRSet = (RuleSet *) realloc(PRSet, RuleSetSpace * sizeof(RuleSet));
	    }
	    else
	    {
		PRSet = (RuleSet *) malloc(RuleSetSpace * sizeof(RuleSet));
	    }

	}

	PRSet[t].SNRules = NRules;
	PRSet[t].SRule = Rule;
	PRSet[t].SRuleIndex = RuleIndex;
	PRSet[t].SDefaultClass = DefaultClass;

	++t;
    }

    if ( ! t )
    {
	printf("\nERROR:  can't find any decision trees\n");
	exit(1);
    }

    TRIALS = t;

    /*  If there is more than one tree in the trees file,
	make a composite ruleset of the rules from all trees  */

    if ( TRIALS > 1 )
    {
	CompositeRuleset();
    }
}



/*************************************************************************/
/*								  	 */
/*	Determine code lengths for attributes and branches		 */
/*								  	 */
/*************************************************************************/


    FindTestCodes()
/*  -------------  */
{
    Attribute Att;
    DiscrValue v, V;
    ItemNo i, *ValFreq;
    int PossibleCuts;
    float Sum, SumBranches=0, p;
    void SwapUnweighted();

    BranchBits  = (float *) malloc((MaxAtt+1) * sizeof(float));

    ForEach(Att, 0, MaxAtt)
    {
	if ( (V = MaxAttVal[Att]) )
	{
	    ValFreq = (ItemNo *) calloc(V+1, sizeof(ItemNo));

	    ForEach(i, 0, MaxItem)
	    {
		ValFreq[DVal(Item[i],Att)]++;
	    }

	    Sum = 0;
	    ForEach(v, 1, V)
	    {
		if ( ValFreq[v] )
		{
		    Sum += (ValFreq[v] / (MaxItem+1.0)) *
			   (LogItemNo[MaxItem+1] - LogItemNo[ValFreq[v]]);
		}
	    }
	    free(ValFreq);

	    BranchBits[Att] = Sum;
	}
	else
	{
	    Quicksort(0, MaxItem, Att, SwapUnweighted);

	    PossibleCuts = 1;
	    ForEach(i, 1, MaxItem)
	    {
		if ( CVal(Item[i],Att) > CVal(Item[i-1],Att) )
		{
		    PossibleCuts++;
		}
	    }

	    BranchBits[Att] = PossibleCuts > 1 ?
			      1 + LogItemNo[PossibleCuts] / 2 : 0 ;
	}

	SumBranches += BranchBits[Att];
    }

    AttTestBits = 0;
    ForEach(Att, 0, MaxAtt)
    {
	if ( (p = BranchBits[Att] / SumBranches) > 0 )
	{
	    AttTestBits -= p * log(p) / log(2.0);
	}
    }
}



/*************************************************************************/
/*                                                                	 */
/*  Exchange items at a and b.  Note:  unlike the similar routine in	 */
/*  buildtree, this does not assume that items have a Weight to be	 */
/*  swapped as well!							 */
/*                                                                	 */
/*************************************************************************/


void SwapUnweighted(a, b)
/*   --------------  */
    ItemNo a, b;
{
    Description Hold;

    Hold = Item[a];
    Item[a] = Item[b];
    Item[b] = Hold;
}



/*************************************************************************/
/*								  	 */
/*	Form composite ruleset for all trials			  	 */
/*								  	 */
/*************************************************************************/


    CompositeRuleset()
/*  ----------------  */
{
    RuleNo r;
    short t, ri;
    Boolean NewRule();
    
    InitialiseRules();

    /*  Lump together all the rules from each ruleset  */

    ForEach(t, 0, TRIALS-1)
    {
	ForEach(ri, 1, PRSet[t].SNRules)
	{
	    r = PRSet[t].SRuleIndex[ri];
	    NewRule(PRSet[t].SRule[r].Lhs, PRSet[t].SRule[r].Size,
		     PRSet[t].SRule[r].Rhs, PRSet[t].SRule[r].Error);
	}
    }

    /*  ... and select a subset in the usual way  */

    ConstructRuleset();

    printf("\nComposite ruleset:\n");
    PrintIndexedRules();

    PRSet[TRIALS].SNRules    = NRules;
    PRSet[TRIALS].SRule      = Rule;
    PRSet[TRIALS].SRuleIndex = RuleIndex;
    PRSet[TRIALS].SDefaultClass = DefaultClass;
}
/*************************************************************************/
/*								  	 */
/*	Form a set of rules from a decision tree			 */
/*	----------------------------------------			 */
/*								  	 */
/*************************************************************************/




ItemNo	*TargetClassFreq,	/* [Boolean] */
	*Errors,		/* [Condition] */
	*Total;			/* [Condition] */

float	*Pessimistic,		/* [Condition] */
	*Actual,		/* [Condition] */
	*CondSigLevel;		/* [Condition] */

Boolean	**CondSatisfiedBy,	/* [Condition][ItemNo] */
	*Deleted;		/* [Condition] */

DiscrValue *SingleValue;	/* [Attribute] */

Condition *Stack;

short	MaxDisjuncts,
	MaxDepth;



/*************************************************************************/
/*								  	 */
/*	Form a ruleset from decision tree t			  	 */
/*								  	 */
/*************************************************************************/


    FormRules(t)
/*  ----------  */
    Tree t;
{
    short i;

    /*  Find essential parameters and allocate storage  */

    MaxDepth = 0;
    MaxDisjuncts = 0;

    TreeParameters(t, 0);

    Actual = (float *) calloc(MaxDepth+2, sizeof(float));
    Total = (ItemNo *) calloc(MaxDepth+2, sizeof(ItemNo));
    Errors = (ItemNo *) calloc(MaxDepth+2, sizeof(ItemNo));
    Pessimistic = (float *) calloc(MaxDepth+2, sizeof(float));

    CondSigLevel = (float *) calloc(MaxDepth+2, sizeof(float));

    TargetClassFreq = (ItemNo *) calloc(2, sizeof(ItemNo));

    Deleted = (Boolean *) calloc(MaxDepth+2, sizeof(Boolean));
    CondSatisfiedBy = (char **) calloc(MaxDepth+2, sizeof(char *));
    Stack = (Condition *) calloc(MaxDepth+2, sizeof(Condition));

    ForEach(i, 0, MaxDepth+1)
    {
	CondSatisfiedBy[i] = (char *) calloc(MaxItem+1, sizeof(char));
	Stack[i] = (Condition) malloc(sizeof(struct CondRec));
    }

    SingleValue = (DiscrValue *) calloc(MaxAtt+1, sizeof(DiscrValue));

    InitialiseRules();

    /*  Extract and prune disjuncts  */

    Scan(t, 0);

    /*  Deallocate storage  */

    ForEach(i, 0, MaxDepth+1)
    {
	free(CondSatisfiedBy[i]);
	free(Stack[i]);
    }
    free(Deleted);
    free(CondSatisfiedBy);
    free(Stack);

    free(Actual);
    free(Total);
    free(Errors);
    free(Pessimistic);

    free(CondSigLevel);

    free(TargetClassFreq);
}



/*************************************************************************/
/*                                                                	 */
/*  Find the maximum depth and the number of leaves in tree t	  	 */
/*  with initial depth d					  	 */
/*                                                                	 */
/*************************************************************************/


    TreeParameters(t, d)
/*  ---------------  */
    Tree t;
    short d;
{
    DiscrValue v;

    if ( t->NodeType )
    {
	ForEach(v, 1, t->Forks)
	{
	    TreeParameters(t->Branch[v], d+1);
	}
    }
    else
    {
	/*  This is a leaf  */

	if ( d > MaxDepth ) MaxDepth = d;
	MaxDisjuncts++;
    }
}



/*************************************************************************/
/*								  	 */
/*  Extract disjuncts from tree t at depth d, and process them	  	 */
/*								  	 */
/*************************************************************************/


    Scan(t, d)
/*  ----  */
    Tree t;
    short d;
{
    DiscrValue v;
    short i;
    Condition *Term;
    Test x, FindTest();

    if ( t->NodeType )
    {
	d++;

	x = (Test) malloc(sizeof(struct TestRec));
	x->NodeType = t->NodeType;
	x->Tested = t->Tested;
	x->Forks = t->Forks;
	x->Cut = ( t->NodeType == ThreshContin ? t->Cut : 0 );
	if ( t->NodeType == BrSubset )
	{
	    x->Subset = (Set *) calloc(t->Forks + 1, sizeof(Set));
	    ForEach(v, 1, t->Forks)
	    {
		x->Subset[v] = t->Subset[v];
	    }
	}

	Stack[d]->CondTest = FindTest(x);

	ForEach(v, 1, t->Forks)
	{
	    Stack[d]->TestValue = v;
	    Scan(t->Branch[v], d);
	}
    }
    else
    if ( t->Items >= 1 )
    {
	/*  Leaf of decision tree - construct the set of
 	    conditions associated with this leaf and prune  */

	Term = (Condition *) calloc(d+1, sizeof(Condition));
	ForEach(i, 1, d)
	{
	    Term[i] = (Condition) malloc(sizeof(struct CondRec));
	    Term[i]->CondTest = Stack[i]->CondTest;
	    Term[i]->TestValue = Stack[i]->TestValue;
	}

	PruneRule(Term, d, t->Leaf);

	free(Term);
    }
}
/*************************************************************************/
/*								   	 */
/*	Pruning single rules					   	 */
/*	--------------------				   	      	 */
/*								   	 */
/*************************************************************************/




/*  External data structures used in building rules  */

extern ItemNo	*TargetClassFreq,	/* [Boolean] */
		*Errors,		/* [Condition] */
		*Total;			/* [Condition] */

extern float	*Pessimistic,		/* [Condition] */
		*Actual,		/* [Condition] */
		*CondSigLevel;		/* [Condition] */

extern Boolean	**CondSatisfiedBy,	/* [Condition][ItemNo] */
		*Deleted;

#define Before(n1,n2)  (n1->Tested < n2->Tested ||\
			n1->NodeType < n2->NodeType ||\
		        n1->Tested == n2->Tested && n1->Cut < n2->Cut)

#define IsTarget(case)  (Class(case) == TargetClass ? 1 : 0)



/*************************************************************************/
/*									 */
/*  Prune the rule given by the conditions Cond, and the number of	 */
/*  conditions NCond, and add the resulting rule to the current		 */
/*  ruleset if it is sufficiently accurate				 */
/*									 */
/*************************************************************************/


    PruneRule(Cond, NCond, TargetClass)
/*  ---------  */
    Condition Cond[];
    short NCond;
    ClassNo TargetClass;
{
    short d, dd, id, Bestd, Bestid, Remaining=NCond;
    float DefaultError, Extra, AddErrs(), TableProb();
    Boolean Alter, Satisfies(), NewRule(), Redundant();
    Condition Hold;
    ItemNo i;

    ForEach(d, 0, NCond)
    {
	Deleted[d] = false;
    }

    /*  Evaluate the satisfaction matrix  */

    TargetClassFreq[0] = TargetClassFreq[1] = 0;

    ForEach(i, 0, MaxItem)
    {
	ForEach(d, 1, NCond)
	{
	    CondSatisfiedBy[d][i] = Satisfies(Item[i], Cond[d]);
	}
	TargetClassFreq[IsTarget(Item[i])]++;
    }

    DefaultError = 1.0 - (TargetClassFreq[true] + 1.0) / (MaxItem + 3.0);

    /*  Find conditions to delete  */

    Verbosity(1) printf("\n  pruning rule for %s", ClassName[TargetClass]);

    do
    {
	Alter = false;

	FindTables(NCond, TargetClass);

	/*  Find the condition, deleting which would most improve
	    the accuracy of the rule.
	    Notes: The pessimistic error rate, and not the actual
		   error rate, is currently used.
	    	   When d is 0, we are dealing with all conditions.  */

	Bestd = id = 0;

	Verbosity(1)
	    printf("\n     Err Used   Pess\tAbsent condition\n");

	ForEach(d, 0, NCond)
	{
	    if ( Deleted[d] ) continue;

	    if ( Total[d] )
	    {
		Actual[d] = Errors[d] / (float) Total[d];
		Extra = AddErrs((float) Total[d], (float) Errors[d]);
		Pessimistic[d] = (Errors[d] + Extra) / Total[d];
	    }
	    else
	    {
		Actual[d] = 0;
		Pessimistic[d] = DefaultError;
	    }

	    Verbosity(1)
		printf("   %5d%5d  %4.1f%%",
		       Errors[d], Total[d], 100 * Pessimistic[d]);

	    if ( ! d )
	    {
		Verbosity(1) printf("\t<base rule>\n");
	    }
	    else
	    {
		id++;

		/*  If significance testing option used, invoke Fisher's
		    exact test here to assess probability that division
		    by d arises from chance.  */

		if ( SIGTEST )
		{
		    CondSigLevel[d] =
			TableProb(Errors[0],
				   Errors[d]-Errors[0],
				   Total[0]-Errors[0],
			           Total[d]-Total[0]-Errors[d]+Errors[0]);

		    Verbosity(1) printf("  Sig=%.3f", CondSigLevel[d]);
		}

		Verbosity(1) PrintCondition(Cond[d]);

		/*  Bestd identifies the condition with lowest pessimistic
		    error  estimate  */

		if ( ! Bestd || Pessimistic[d] <= Pessimistic[Bestd] )
		{
		    Bestd = d;
		    Bestid = id;
		}

		/*  Alter is set true if we are going to drop a condition
		    (either because we get lower pessimistic est, or
		    because one of the conditions fails a significance test)  */

		if ( Pessimistic[d] <= Pessimistic[0] ||
		     Actual[d] <= Actual[0]  ||
		     SIGTEST && CondSigLevel[d] > SIGTHRESH )
		{
		    Alter = true;
		}
	    }
	}

	if ( Alter )
	{
	    Verbosity(1) printf("\teliminate test %d\n", Bestid);

	    Deleted[Bestd] = true;
	    Remaining--;
	}

    } while ( Alter && Remaining );

    if ( ! Remaining || ! Total[0] )
    {
	return;
    }

    if ( Pessimistic[0] >= DefaultError )
    {
	Verbosity(1) printf("\ttoo inaccurate\n");
	return;
    }

    /*  Sort the conditions  */

    ForEach(d, 1, Remaining)
    {
	dd =  0;
	ForEach(id, d, NCond)
	{
	    if ( ! Deleted[id] &&
		 ( ! dd ||
		   Before(Cond[id]->CondTest, Cond[dd]->CondTest) ) )
	    {
		dd = id;
	    }
	}
	if ( dd != d )
	{
	    Hold    = Cond[d];
	    Cond[d] = Cond[dd];
	    Cond[dd] = Hold;
	    Deleted[dd] = Deleted[d];
	}
	Deleted[d] = true;
    }

    NewRule(Cond, Remaining, TargetClass, Pessimistic[0]);
}



/*************************************************************************/
/*									 */
/*  See whether condition R is redundant                           	 */
/*									 */
/*************************************************************************/


Boolean Redundant(R, Cond, NCond)
/*      ---------  */
    Condition Cond[];
    short R, NCond;
{
    short d, v, vv;
    Test t, Rt;
    Boolean IsSubset();

    Rt = Cond[R]->CondTest;
    v =  Cond[R]->TestValue;

    ForEach(d, 1, NCond)
    {
	if ( Deleted[d] || d == R ) continue;

	t = Cond[d]->CondTest;
	vv = Cond[d]->TestValue;

	if ( t->Tested != Rt->Tested ) continue;

	switch ( t->NodeType )
	{
	    case BrDiscr:  /* test of discrete attribute */

		return false;

	    case ThreshContin:  /* test of continuous attribute */

		if ( vv == v &&
		     ( v == 1 ? t->Cut < Rt->Cut : t->Cut > Rt->Cut ) )
		{
		    return true;
		}

		break;

	    case BrSubset:  /* subset test on discrete attribute  */

		if ( IsSubset(t->Subset[vv], Rt->Subset[v], Rt->Tested) )
		{
		    return true;
		}
	}
    }

    return false;
}



/*************************************************************************/
/*									 */
/*  Decide whether subset S1 of values is contained in subset S2	 */
/*									 */
/*************************************************************************/


Boolean IsSubset(S1, S2, Att)
/*      --------  */
    Set S1, S2;
    Attribute Att;
{
    DiscrValue v;

    ForEach(v, 1, MaxAttVal[Att])
    {
	if ( In(v, S1) && ! In(v, S2) ) return false;
    }

    return true;
}



/*************************************************************************/
/*									 */
/*  Find the frequency distribution tables for the current conditions: 	 */
/*									 */
/*	Total[0] = items matching all conditions		   	 */
/*	Total[d] = items matching all except condition d	   	 */
/*									 */
/*	Errors[0] = wrong-class items matching all conditions	   	 */
/*	Errors[d] = wrong-class items matching all but cond d	   	 */
/*									 */
/*  This routine is critical to the efficiency of rule pruning. It	 */
/*  computes the information above in one pass through the data,	 */
/*  looking at cases that fail to satisfy at most one of the		 */
/*  non-deleted conditions						 */
/*									 */
/*************************************************************************/


    FindTables(NCond, TargetClass)
/*  -----------  */
    short NCond;
    ClassNo TargetClass;
{
    ItemNo i;
    short Misses, Missed[2], d;
    Boolean CorrectClass;

    /*  Clear distributions  */

    ForEach(d, 0, NCond)
    {
	Total[d] = Errors[d] = 0;
    }

    /*  Set distributions  */

    ForEach(i, 0, MaxItem)
    {
	Misses = 0;
	CorrectClass = IsTarget(Item[i]);

	for ( d = 1 ; d <= NCond && Misses <= 1 ; d++ )
	{
	    if ( ! Deleted[d] && ! CondSatisfiedBy[d][i] )
	    {
		Missed[Misses++] = d;
	    }
	}

	if ( ! Misses )
	{
	    UpdateCount(Total, Errors, 0, CorrectClass);
	}
	else
	if ( Misses == 1 )
	{
	    UpdateCount(Total, Errors, Missed[0], CorrectClass);
	}
    }

    /*  Adjust counts to reflect cases that met all conditions  */

    ForEach(d, 1, NCond)
    {
	if ( ! Deleted[d] )
	{
	    Total[d] += Total[0];
	    Errors[d] += Errors[0];
	}
    }
}



/*************************************************************************/
/*									 */
/*  Increment the counts Total[d] and Errors[d]				 */
/*									 */
/*************************************************************************/


    UpdateCount(T, E, d, OK)
/*  -----------  */
    ItemNo T[], E[];
    short d;
    Boolean OK;
{
    T[d]++;
    if ( ! OK ) E[d]++;
}



/*************************************************************************/
/*									 */
/*  Determine whether the given case description satisfies the given	 */
/*  condition.								 */
/*									 */
/*************************************************************************/


Boolean Satisfies(CaseDesc, OneCond)
/*      ---------  */
    Description CaseDesc; 
    Condition OneCond;
{
    DiscrValue v;
    float cv;
    Test t;
    short s;
    Boolean Outcome;

    t = OneCond->CondTest;

    /*  Determine the outcome of this test on this item  */

    switch ( t->NodeType )
    {
	case BrDiscr:  /* test of discrete attribute */

	    v = DVal(CaseDesc, t->Tested);
	    Outcome = ( v == 0 ? -1 : v );
	    break;

	case ThreshContin:  /* test of continuous attribute */

	    cv = CVal(CaseDesc, t->Tested);
	    Outcome = ( cv == Unknown ? -1 : cv <= t->Cut ? 1 : 2 );
	    break;

	case BrSubset:  /* subset test on discrete attribute  */

	    v = DVal(CaseDesc, t->Tested);
	    Outcome = -1;
	    ForEach(s, 1, t->Forks)
	    {
		if ( In(v, t->Subset[s]) )
		{
		    Outcome = s;
		    break;
		}
	    }
    }

    return ( Outcome == OneCond->TestValue );
}



/*************************************************************************/
/*									 */
/*  Hypergeometric distribution	(uses tabulated log factorials)		 */
/*									 */
/*************************************************************************/


double Hypergeom(a, r, A, B)
/*               ---------  */
    int a, r, A, B;
{
    return exp( LogFact[A] + LogFact[B] + LogFact[r] + LogFact[A+B-r] -
	        ( LogFact[a] + LogFact[r-a] + LogFact[A-a]
		  + LogFact[B-(r-a)] + LogFact[A+B]) );
}



/*************************************************************************/
/*									 */
/*  TableProb examines the 2x2 contingency table t and computes the      */
/*  probability that a random division could have produced a split at	 */
/*  least as extreme as this.  Also known as "Fisher's Exact Test",	 */
/*  after its inventor, R.A. Fisher.					 */
/*									 */
/*************************************************************************/


float TableProb(t11, t12, t21, t22)
/*    ---------  */
    int t11, t12, t21, t22;
{
    double Sum=0.0;
    int A, B, r, a, k, a0;

    /*  First, rearrange the rows and columns of the table to get it into
	canonical form  */

    if ( t11 + t12 > t21 + t22 )
    {
	A = t11 + t12;
	B = t21 + t22;

	if ( t11 * (t21 + t22) > t21 * (t11 + t12) )
	{
	    a0 = t11;
	    r  = t11 + t21;
	}
	else
	{
	    a0 = t12;
	    r  = t12 + t22;
	}
    }
    else
    {
	A = t21 + t22;
	B = t11 + t12;
	if ( t21 * (t11 + t12) > t11 * (t21 + t22) )
	{
	    a0 = t21;
	    r  = t21 + t11;
	}
	else
	{
	    a0 = t22;
	    r  = t22 + t12;
	}
    }

    /*  Now compute the probability  */

    k = Min(r, A);
    ForEach(a, a0, k)
    {
	Sum += Hypergeom(a, r, A, B);
    }

    return Sum;
}
/*************************************************************************/
/*									 */
/*	Process sets of rules						 */
/*	---------------------					         */
/*								         */
/*************************************************************************/




ItemNo	*ClassFreq,	/* ClassFreq[c]	= no. items of class c  */
	*Covered,	/* Covered[i]	= no. included rules that cover item i */
	*FalsePos,	/* FalsePos[c]	= no. false positives from rules
					  selected for class c */
	*NoRule,	/* NoRule[c]	= no. items covered by no selected rule */

	*Right,		/* Right[r]	= no. correct rule firings */
	*Wrong;		/* Wrong[r]	= no. incorrect rule firings */

float	*Value,		/* Value[r]	= advantage attributable to rule r or
					  realisable if rule r included */
	SubsetValue,	/* value of best class subset so far */
	CodeWeight;	/* multiplying factor for rule encodings */

Boolean	*RuleIn,	/* RuleIn[r]	= true if rule r included */
	*Subset,	/* best class subset so far */
	**Match;	/* Match[r][i]	= true if rule r fires on item i */

RuleNo	*ClassRules;	/* list of all rules for current target class */

ClassNo	FocusClass;



/*************************************************************************/
/*									 */
/*  Construct an ordered subset (indexed by RuleIndex) of the current	 */
/*  set of rules							 */
/*									 */
/*************************************************************************/


    ConstructRuleset()
/*  ----------------  */
{
    RuleNo r, OldNRules = NRules;

    /*  Allocate tables  */

    Right = (ItemNo *) calloc(NRules+1, sizeof(ItemNo));
    Wrong = (ItemNo *) calloc(NRules+1, sizeof(ItemNo));

    Value = (float *) calloc(NRules+1, sizeof(float));

    RuleIn = (Boolean *) calloc(NRules+1, sizeof(Boolean));
    Subset = (Boolean *) malloc((NRules+1) * sizeof(Boolean));

    ClassRules = (RuleNo *) malloc((NRules+1) * sizeof(RuleNo));

    ClassFreq = (ItemNo *) calloc(MaxClass+1, sizeof(ItemNo));

    Covered = (ItemNo *) calloc(MaxItem+1, sizeof(ItemNo));

    Match = (Boolean **) calloc(NRules+1, sizeof(Boolean *));

    FalsePos = (ItemNo *) calloc(MaxClass+1, sizeof(ItemNo));

    NoRule = (ItemNo *) calloc(MaxClass+1, sizeof(ItemNo));

    ForEach(r, 1, NRules)
    {
	Match[r] = (Boolean *) calloc(MaxItem+1, sizeof(Boolean));
    }

    /*  Cover each class, then order the classes to give an index of rules  */

    InitialiseTables();

    FindRuleCodes();
    CodeWeight = 0.5;

    ForEach(FocusClass, 0, MaxClass)
    {
	CoverClass();
    }

    MakeIndex();
    FindDefault();

    /*  Clear  */

    free(Value);
    free(RuleIn);
    free(ClassRules);
    free(Subset);
    free(Covered);
    free(FalsePos);
    free(NoRule);
    ForEach(r, 1, OldNRules)
    {
	free(Match[r]);
    }
    free(Match);
}



/*************************************************************************/
/*									 */
/*		Initialise all tables used in sifting			 */
/*									 */
/*************************************************************************/


    InitialiseTables()
/*  ----------------  */
{
    ItemNo i;
    RuleNo r;
    ClassNo c;
    float Strength();

    ForEach(r, 1, NRules)
    {
	RuleIn[r] = false;
	Rule[r].Used = Rule[r].Incorrect = 0;
    }

    ForEach(c, 0, MaxClass)
    {
	ClassFreq[c] = 0;
    }

    ForEach(i, 0, MaxItem)
    {
	ClassFreq[Class(Item[i])]++;

	ForEach(r, 1, NRules)
	{
	    Match[r][i] = Strength(Rule[r], Item[i]) > 0.1;

	    if ( Match[r][i] )
	    {
		Rule[r].Used++;
		if ( Class(Item[i]) != Rule[r].Rhs ) Rule[r].Incorrect++;
	    }
	}
    }
}



/*************************************************************************/
/*								         */
/*	Select a subset of the rules for class FocusClass	         */
/*								         */
/*************************************************************************/


    CoverClass()
/*  ----------  */
{
    RuleNo r, RuleCount=0;
    ItemNo i;

    Verbosity(1)
	printf("\nClass %s\n-----\nAction  Change  Value",
		ClassName[FocusClass]);

    ForEach(i, 0, MaxItem)
    {
	Covered[i] = 0;
    }

    ForEach(r, 1, NRules)
    {
	if ( Rule[r].Rhs == FocusClass )
	{
	    RuleCount++;
	    ClassRules[RuleCount] = r;
	}
    }

    if ( ! RuleCount )
    {
	return;
    }

    SubsetValue = 1E10;

    if ( RuleCount <= 10 )
    {
	AllCombinations(RuleCount);
    }
    else
    if ( SIMANNEAL )
    {
	SimAnneal(RuleCount);
    }
    else
    {
	SpotSearch(RuleCount);
    }

    memcpy(RuleIn, Subset, NRules+1);
    Verbosity(1) printf("\n\tBest value %.1f\n", SubsetValue);
}


 
/*************************************************************************/
/*									 */
/*    Try all combinations of rules to find best value			 */
/*									 */
/*************************************************************************/


    AllCombinations(NR)
/*  ---------------  */
    RuleNo NR;
{
    RuleNo r;

    if ( ! NR )
    {
	CalculateValue();
    }
    else
    {
	r = ClassRules[NR];

	AllCombinations(NR-1);

	AddRule(r);
	AllCombinations(NR-1);

	DeleteRule(r);
	Verbosity(1) printf("\n");
    }
}



/*************************************************************************/
/*									 */
/*  Find a good subset by simulated annealing				 */
/*									 */
/*************************************************************************/


    SimAnneal(RuleCount)
/*  ---------  */
    RuleNo RuleCount;
{
    RuleNo r, OutCount;
    short ri, Tries;
    float Temp, Delta;
    Boolean Changed;

    /*  Keep dropping and adding rules until can't improve  */

    for ( Temp = 1000 ; Temp > 0.001 ; Temp *= 0.95 )
    {
	CalculateValue();

	Verbosity(2)
	{
	    OutCount = 0;

	    ForEach(ri, 1, RuleCount)
	    {
		r = ClassRules[ri];

		if ( ! RuleIn[r] )
		{
		    if ( ! (OutCount++ % 3) ) printf("\n\t\t");
		    printf("%d<%d|%d=%.1f> ", r, Right[r], Wrong[r], Value[r]);
		}
	    }

	    printf("\n\n");
	}

	Changed = false;

	for ( Tries = 100 ; ! Changed && Tries > 0 ; Tries-- )
	{
	    /*  Choose a rule to add or delete  */

	    ri = RuleCount * Random + 1;

	    r = ClassRules[ri];

	    Delta = ( RuleIn[r] ? -Value[r] : Value[r] );

	    if ( Delta > 0 || Random < exp(Delta / Temp) )
	    {
		if ( RuleIn[r] )
		{
		    DeleteRule(r);
		}
		else
		{
		    AddRule(r);
		}
		
		Changed = true;
	    }
	}

	if ( ! Changed ) break;
    }

    /*  Try to improve best subset so far by hill-climbing  */

    Verbosity(1) printf("Polish: ");
    memcpy(RuleIn, Subset, NRules+1);
    HillClimb(RuleCount);
}



/*************************************************************************/
/*									 */
/*  Find a good subset by repeated greedy search			 */
/*									 */
/*************************************************************************/


    SpotSearch(RuleCount)
/*  ----------  */
    RuleNo RuleCount;
{
    RuleNo r;
    short ri, Trial;
    float ProbIn;

    ForEach(Trial, 0, 10)
    {
	Verbosity(1) printf("\n    Trial %d:", Trial);

	/*  Add rules randomly to the initial subset  */

	ProbIn = Trial / 10.0;
	ForEach(ri, 1, RuleCount)
	{
	    r = ClassRules[ri];
	    RuleIn[r] = Random < ProbIn;
	}

	HillClimb(RuleCount);
    }
}



/*************************************************************************/
/*									 */
/*  Improve a subset of rules by adding and deleting rules		 */
/*									 */
/*************************************************************************/


    HillClimb(RuleCount)
/*  ---------  */
    RuleNo RuleCount;
{
    RuleNo r, Bestr;
    short ri, OutCount;
    ItemNo i;
    float Delta, BestDelta;

    ForEach(i, 0, MaxItem)
    {
	Covered[i] = 0;
    }

    ForEach(ri, 1, RuleCount)
    {
	r = ClassRules[ri];
	if ( RuleIn[r] )
	{
	    ForEach(i, 0, MaxItem)
	    {
		if ( Match[r][i] )
		{
		    Covered[i]++;
		}
	    }
	}
    }
    
    /*  Add or drop rule with greatest reduction in coding cost  */

    while ( true )
    {
	CalculateValue();

	Verbosity(2)
	{
	    OutCount = 0;

	    ForEach(ri, 1, RuleCount)
	    {
		r = ClassRules[ri];

		if ( ! RuleIn[r] )
		{
		    if ( ! (OutCount++ % 3) ) printf("\n\t\t");
		    printf("%d<%d|%d=%.1f> ", r, Right[r], Wrong[r], Value[r]);
		}
	    }

	    printf("\n\n");
	}

	Bestr = BestDelta = 0;
	ForEach(ri, 1, RuleCount)
	{
	    r = ClassRules[ri];
	    Delta = ( RuleIn[r] ? -Value[r] : Value[r] );
	    if ( Delta > BestDelta )
	    {
		Bestr = r;
		BestDelta = Delta;
	    }
	}
	if ( ! Bestr ) break;

	if ( RuleIn[Bestr] )
	{
	    DeleteRule(Bestr);
	}
	else
	{
	    AddRule(Bestr);
	}
    }
}



/*************************************************************************/
/*								         */
/*  Find the number of correct and incorrect rule firings for rules      */
/*  for class FocusClass and hence determine the Value of the rules.     */
/*  If best so far, remember.						 */
/*								         */
/*************************************************************************/


    CalculateValue()
/*  --------------  */
{
    RuleNo r, Selected=0, InCount;
    ItemNo i, Times, FPos=0, FNeg=0, SumCover=0;
    float BaseBits, RuleBits=0, NewBits, ExceptionBits();
    ClassNo ThisClass;
    Boolean *RuleMatch;

    ForEach(i, 0, MaxItem)
    {
	ThisClass = Class(Item[i]);

	if ( Covered[i] )
	{
	    SumCover++;
	    if( ThisClass != FocusClass ) FPos++;
	}
	else
	if ( ThisClass == FocusClass )
	{
	    FNeg++;
	}
    }

    ForEach(r, 1, NRules)
    {
	if ( Rule[r].Rhs == FocusClass )
	{
	    Right[r] = Wrong[r] = 0;

	    if ( RuleIn[r] )
	    {
		RuleBits += Rule[r].Bits;
		Selected++;
	    }

	    RuleMatch = Match[r];

	    ForEach(i, 0, MaxItem)
	    {
		if ( RuleMatch[i] &&
		   ( ! (Times = Covered[i]) || Times == 1 && RuleIn[r] ) )
		{
		    if ( Class(Item[i]) == FocusClass )
		    {
			Right[r]++;
		    }
		    else
		    {
			Wrong[r]++;
		    }
		}
	    }
	}
    }

    RuleBits -= LogFact[Selected];	/* allow for reordering of rules */

    BaseBits = CodeWeight * RuleBits + ExceptionBits(SumCover, FPos, FNeg);

    /*  From the Right and Wrong of each rule, calculate its value  */

    Verbosity(1)
    {
        printf("\t");
    	InCount = -1;
    }

    ForEach(r, 1, NRules)
    {
	if ( Rule[r].Rhs == FocusClass )
	{
	    if ( RuleIn[r] )
	    {
		NewBits = ExceptionBits(SumCover-Right[r]-Wrong[r],
					FPos-Wrong[r], FNeg+Right[r]) +
			  CodeWeight *
			      (RuleBits - Rule[r].Bits + LogItemNo[Selected]);
		Value[r] = NewBits - BaseBits;
	    }
	    else
	    {
		NewBits = ExceptionBits(SumCover+Right[r]+Wrong[r],
					FPos+Wrong[r], FNeg-Right[r]) +
			  CodeWeight *
			      (RuleBits + Rule[r].Bits - LogItemNo[Selected+1]);
		Value[r] = BaseBits - NewBits;
	    }

	    Verbosity(1)
	    {
	        if ( RuleIn[r] )
	        {
		    if ( ++InCount && ! (InCount % 3) ) printf("\n\t\t");
		    printf("%d[%d|%d=%.1f]  ", r, Right[r], Wrong[r], Value[r]);
	        }
	    }
	}
    }

    Verbosity(1)
    {
	printf("\n\t\t%d rules, %d firings: F+=%d, F-=%d, %.1f bits (rules=%.1f)\n",
		Selected, SumCover, FPos, FNeg, BaseBits, RuleBits);
    }

    if ( BaseBits < SubsetValue )
    {
	SubsetValue = BaseBits;
	memcpy(Subset, RuleIn, NRules+1);
    }
}



/*************************************************************************/
/*								         */
/*  Add rule r to the set of included rules and increase the number of	 */
/*  rules covering each of the items that fire the rule		         */
/*								         */
/*************************************************************************/


    AddRule(r)
/*  -------  */
    RuleNo r;
{
    ItemNo i;

    RuleIn[r] = true;

    ForEach(i, 0, MaxItem)
    {
	if ( Match[r][i] )
	{
	    Covered[i]++;
	}
    }

    Verbosity(1) printf("%5d+  %6.1f", r, Value[r]);
}



/*************************************************************************/
/*								         */
/*  Delete rule r from the included rules and decrease the number of	 */
/*  rules covering each of the items covered by the rule	         */
/*								         */
/*************************************************************************/


    DeleteRule(r)
/*  ----------  */
    RuleNo r;
{
    ItemNo i;

    RuleIn[r] = false;

    ForEach(i, 0, MaxItem)
    {
	if ( Match[r][i] )
	{
	    Covered[i]--;
	}
    }

    Verbosity(1) printf("%5d-  %6.1f", r, -Value[r]);
}



/*************************************************************************/
/*								         */
/*  Make an index of included rules in RuleIndex.  Select first those    */
/*  classes whose rules have the fewest false positives.  Within a	 */
/*  class, put rules with higher accuracy ahead.			 */
/*								         */
/*************************************************************************/


    MakeIndex()
/*  ---------  */
{
    ClassNo c, BestC, Pass;
    RuleNo r, BestR, NewNRules = 0;
    ItemNo i;
    Boolean *Included;

    Included = (Boolean *) calloc(MaxClass+1, sizeof(Boolean));
    RuleIndex = (RuleNo *) calloc(NRules+1, sizeof(RuleNo));

    Verbosity(1) printf("\nFalsePos  Class\n");

    ForEach(i, 0, MaxItem)
    {
	Covered[i] = 0;
    }

    /*  Select the best class to put next  */

    ForEach(Pass, 0, MaxClass)
    {
	ForEach(c, 0, MaxClass)
	{
	    if ( Included[c] ) continue;

	    FalsePos[c] = 0;

	    ForEach(i, 0, MaxItem)
	    {
		if ( Covered[i] || Class(Item[i]) == c ) continue;

		ForEach(r, 1, NRules)
		{
		    if ( Rule[r].Rhs == c && RuleIn[r] && Match[r][i] )
		    {
			FalsePos[c]++;
			break;
		    }
		}
	    }
	}

	BestC = -1;
	ForEach(c, 0, MaxClass)
	{
	    if ( ! Included[c] &&
	         ( BestC < 0 || FalsePos[c] < FalsePos[BestC] ) )
	    {
		BestC = c;
	    }
	}
	Included[BestC] = true;

	Verbosity(1)
	    printf("%5d     %s\n", FalsePos[BestC], ClassName[BestC]);

	/*  Now grab the rules for this class  */

	do
	{
	    BestR = 0;

	    /*  Find the best rule to put next  */

	    ForEach(r, 1, NRules)
	    {
		if ( RuleIn[r] && Rule[r].Rhs == BestC &&
		     ( ! BestR || Rule[r].Error < Rule[BestR].Error ) )
		{
		    BestR = r;
		}
	    }

	    if ( BestR )
	    {
		RuleIndex[++NewNRules] = BestR;
		RuleIn[BestR] = false;

		ForEach(i, 0, MaxItem)
		{
		    Covered[i] |= Match[BestR][i];
		}
	    }
	} while ( BestR );
    }

    NRules = NewNRules;
    free(Included);
}



/*************************************************************************/
/*								         */
/*  Find the default class as the one with most items not covered by	 */
/*  any rule.  Resolve ties in favour of more frequent classes.		 */
/*  (Note: Covered has been set by MakeIndex.)				 */
/*								         */
/*************************************************************************/


    FindDefault()
/*  -----------  */
{
    ClassNo c;
    ItemNo i;

    /*  Determine uncovered items  */

    ForEach(c, 0, MaxClass)
    {
	NoRule[c] = 0;
    }

    ForEach(i, 0, MaxItem)
    {
	if ( ! Covered[i] )
	{
	    NoRule[Class(Item[i])]++;
	}
    }

    Verbosity(1)
    {
	printf("\nItems: Uncovered   Class\n");
	ForEach(c, 0, MaxClass)
	{
	    printf("%5d %7d      %s\n", ClassFreq[c], NoRule[c], ClassName[c]);
	}
	printf("\n");
    }

    DefaultClass = 0;
    ForEach(c, 1, MaxClass)
    {
	if ( NoRule[c] > NoRule[DefaultClass] ||
	     NoRule[c] == NoRule[DefaultClass] &&
	     ClassFreq[c] > ClassFreq[DefaultClass] )
	{
	    DefaultClass = c;
	}
    }
}



/*************************************************************************/
/*								         */
/*  Given a rule and a case, determine the strength with which we can    */
/*  conclude that the case belongs to the class specified by the rule's  */
/*  right-hand side.						         */
/*								         */
/*  If the case doesn't satisfy all the conditions of the rule,		 */
/*  then this is 0.						         */
/*								         */
/*************************************************************************/


float Strength(ThisRule, Case)
/*    --------  */
    PR ThisRule;
    Description Case;
{
    short d;
    Boolean Satisfies();

    if ( ThisRule.Error > 0.7 ) return 0.0;

    ForEach(d, 1, ThisRule.Size)
    {
	if ( ! Satisfies(Case, ThisRule.Lhs[d]) )
	{
	    return 0.0;
	}
    }

    return ( 1 - ThisRule.Error );
}



/*************************************************************************/
/*									 */
/*  Determine the number of bits to encode exceptions.  Unlike the	 */
/*  version in the book, this uses an approximate encoding that 	 */
/*  penalizes unbalanced numbers of false positives and false negatives  */
/*  as described in my paper at 1995 International Machine Learning      */
/*  Conference (published by Morgan Kaufmann).				 */
/*									 */
/*************************************************************************/


float Biased(N, E, ExpE)
/*    ------  */
    int N, E;
    float ExpE;
{
    float Rate;

    if ( ExpE <= 1E-6 )
    {
	return ( E == 0 ? 0.0 : 1E6 );
    }
    else
    if ( ExpE >= N-1E-6 )
    {
	return ( E == N ? 0.0 : 1E6 );
    }

    Rate = ExpE / N;
    return -E * Log(Rate) - (N-E) * Log(1-Rate);
}



float ExceptionBits(Fires, FP, FN)
/*    -------------  */
    int Fires, FP, FN;
{
    if ( Fires > 0.5 * (MaxItem+1) )
    {
	return Log(MaxItem+1)
		+ Biased(Fires, FP, 0.5 * (FP+FN))
		+ Biased(MaxItem+1-Fires, FN, (float) FN);
    }
    else
    {
	return Log(MaxItem+1)
		+ Biased(Fires, FP, (float) FP)
		+ Biased(MaxItem+1-Fires, FN, 0.5 * (FP+FN));
    }
}



/*************************************************************************/
/*									 */
/*  Find encoding lengths for all rules					 */
/*									 */
/*************************************************************************/


    FindRuleCodes()
/*  -------------  */
{
    RuleNo r;
    short d, NCond;
    float Bits, CondBits();

    ForEach(r, 1, NRules)
    {
	NCond = Rule[r].Size;
	Bits = 0;

	ForEach(d, 1, NCond)
	{
	    Bits += CondBits(Rule[r].Lhs[d]);
	}

	/*  Must encode the number of conditions, but credit the total
	    encoding by the ways conditions can be reordered  */

	Rule[r].Bits = Bits + LogItemNo[NCond] - LogFact[NCond];
    }
}



/*************************************************************************/
/*									 */
/*  Determine the number of bits required to encode a condition		 */
/*									 */
/*************************************************************************/


float CondBits(C)
/*    --------  */
    Condition C;
{
    Test t;
    Attribute a;

    t = C->CondTest;
    a = t->Tested;

    switch ( t->NodeType )
    {
	case BrDiscr:		/* test of discrete attribute */
	case ThreshContin:	/* test of continuous attribute */

	    return AttTestBits/REDUNDANCY + BranchBits[a];

	case BrSubset:		/* subset test on discrete attribute  */

	    return AttTestBits/REDUNDANCY + MaxAttVal[a];
    } 
}
/*************************************************************************/
/*									 */
/*	Evaluatation of rulesets					 */
/*	------------------------					 */
/*									 */
/*************************************************************************/





/*************************************************************************/
/*									 */
/*	Evaluate all rulesets						 */
/*									 */
/*************************************************************************/


    EvaluateRulesets(DeleteRules)
/*  ----------------  */
    Boolean DeleteRules;
{
    short t;
    ItemNo *Errors, Interpret();
    float AvSize=0, AvErrs=0;
    Boolean Final;

    if ( TRIALS == 1 )
    {
	/*  Evaluate current ruleset as there is no composite ruleset  */

	Interpret(0, MaxItem, DeleteRules, true, true);
	return;
    }

    Errors = (ItemNo *) malloc((TRIALS+1) * sizeof(ItemNo));

    ForEach(t, 0, TRIALS)
    {
	NRules    = PRSet[t].SNRules;
	Rule      = PRSet[t].SRule;
	RuleIndex = PRSet[t].SRuleIndex;
	DefaultClass = PRSet[t].SDefaultClass;

	if ( t < TRIALS )
	{
	    printf("\nRuleset %d:\n", t);
	}
	else
	{
	    printf("\nComposite ruleset:\n");
	}

	Final = (t == TRIALS);
	Errors[t] = Interpret(0, MaxItem, DeleteRules, Final, Final);

	AvSize += NRules;
	AvErrs += Errors[t];

	if ( DeleteRules )
	{
	    PRSet[t].SNRules = NRules;
	}
    }

    /*  Print report  */

    printf("\n");
    printf("Trial   Size      Errors\n");
    printf("-----   ----      ------\n");

    ForEach(t, 0, TRIALS)
    {
	if ( t < TRIALS )
	{
	    printf("%4d", t);
	}
	else
	{
	    printf("  **");
	}
	printf("    %4d  %3d(%4.1f%%)\n",
	      PRSet[t].SNRules, Errors[t], 100 * Errors[t] / (MaxItem+1.0));
    }

    AvSize /= TRIALS + 1;
    AvErrs /= TRIALS + 1;
    printf("\t\t\t\tAv size = %.1f,  av errors = %.1f (%.1f%%)\n",
	   AvSize, AvErrs, 100 * AvErrs / (MaxItem+1.0));
}



/*************************************************************************/
/*									 */
/*	Evaluate current ruleset					 */
/*									 */
/*************************************************************************/


float	Confidence;		/* certainty factor of fired rule */
				/* (set by BestRuleIndex) */


ItemNo Interpret(Fp, Lp, DeleteRules, CMInfo, Arrow)
/*     ---------  */
    ItemNo Fp, Lp;
    Boolean DeleteRules, CMInfo, Arrow;
{
    ItemNo i, Tested=0, Errors=0, *Better, *Worse, *ConfusionMat;
    Boolean FoundRule;
    ClassNo AssignedClass, AltClass;
    Attribute Att;
    RuleNo p, Bestr, ri, ri2, riDrop=0, BestRuleIndex();
    float ErrorRate, BestRuleConfidence;

    if ( CMInfo )
    {
	ConfusionMat = (ItemNo *) calloc((MaxClass+1)*(MaxClass+1), sizeof(ItemNo));
    }

    ForEach(ri, 1, NRules)
    {
	p = RuleIndex[ri];
	Rule[p].Used = Rule[p].Incorrect = 0;
    }

    Better = (ItemNo *) calloc(NRules+1, sizeof(ItemNo));
    Worse  = (ItemNo *) calloc(NRules+1, sizeof(ItemNo));

    ForEach(i, Fp, Lp)
    {
	/*  Find first choice for rule for this item  */

	ri = BestRuleIndex(Item[i], 1);
	Bestr = ( ri ? RuleIndex[ri] : 0 );
	FoundRule = Bestr > 0;

	if ( FoundRule )
	{
	    Rule[Bestr].Used++;
	    AssignedClass =  Rule[Bestr].Rhs;
	    BestRuleConfidence = Confidence;

	    /*  Now find second choice  */

	    ri2 = BestRuleIndex(Item[i], ri+1);
	    AltClass = ( ri2 ? Rule[RuleIndex[ri2]].Rhs : DefaultClass );
	    if ( AltClass != AssignedClass )
	    {
		if ( AssignedClass == Class(Item[i]) )
		{
		    Better[ri]++;
		}
		else
		if ( AltClass == Class(Item[i]) )
		{
		    Worse[ri]++;
		}
	    }
	}
	else
	{
	    AssignedClass = DefaultClass;
	}
	
	if ( CMInfo )
	{
	    ConfusionMat[Class(Item[i])*(MaxClass+1)+AssignedClass]++;
	}
	Tested++;

	if ( AssignedClass != Class(Item[i]) )
	{
	    Errors++;
	    if ( FoundRule ) Rule[Bestr].Incorrect++;

	    Verbosity(3)
	    {
	    	printf("\n");
	    	ForEach(Att, 0, MaxAtt)
	    	{
	    	    printf("\t%s: ", AttName[Att]);
	    	    if ( MaxAttVal[Att] )
	    	    {
	    		if ( DVal(Item[i],Att) )
			{
	    		    printf("%s\n", AttValName[Att][DVal(Item[i],Att)]);
			}
	    		else
			{
	    		    printf("?\n");
			}
	    	    }
	    	    else
	    	    {
	    		if ( CVal(Item[i],Att) != Unknown )
			{
	    		    printf("%g\n", CVal(Item[i],Att));
			}
	    		else
			{
	    		    printf("?\n");
			}
	    	    }
	    	}
	    	printf("\t%4d:\tGiven class %s,", i, ClassName[Class(Item[i])]);
	    	if ( FoundRule )
	    	{
	    	    printf(" rule %d [%.1f%%] gives class ",
	    		    Bestr, 100 * BestRuleConfidence);
	    	}
	    	else
		{
	    	    printf(" default class ");
		}
	    	printf("%s\n", ClassName[AssignedClass]);
	    }
	}
    }

    printf("\nRule  Size  Error  Used  Wrong\t          Advantage\n");
    printf(  "----  ----  -----  ----  -----\t          ---------\n");
    ForEach(ri, 1, NRules)
    {
	p = RuleIndex[ri];
	if ( Rule[p].Used > 0 )
	{
	    ErrorRate = Rule[p].Incorrect / (float) Rule[p].Used;

	    printf("%4d%6d%6.1f%%%6d%7d (%.1f%%)\t%6d (%d|%d) \t%s\n",
		    p, Rule[p].Size,
		    100 * Rule[p].Error, Rule[p].Used, Rule[p].Incorrect,
		    100 * ErrorRate,
		    Better[ri]-Worse[ri], Better[ri], Worse[ri],
		    ClassName[Rule[p].Rhs]);

	    /*  See whether this rule should be dropped.  Note: can only drop
		one rule at a time, because Better and Worse are affected  */

	    if ( DeleteRules && ! riDrop && Worse[ri] > Better[ri] )
	    {
		riDrop = ri;
	    }
	}
    }

    free(Better);
    free(Worse);

    if ( riDrop )
    {
	printf("\nDrop rule %d\n", RuleIndex[riDrop]);

	ForEach(ri, riDrop+1, NRules)
	{
	    RuleIndex[ri-1] = RuleIndex[ri];
	}
	NRules--;
    
	if ( CMInfo ) free(ConfusionMat);
	return Interpret(Fp, Lp, DeleteRules, true, Arrow);
    }
    else
    {
	printf("\nTested %d, errors %d (%.1f%%)%s\n",
	    Tested, Errors, 100 * Errors / (float) Tested,
	    ( Arrow ? "   <<" : "" ));
    }

    if ( CMInfo )
    {
	PrintConfusionMatrix(ConfusionMat);
	free(ConfusionMat);
    }

    return Errors;
}



/*************************************************************************/
/*									 */
/*	Find the best rule for the given case, leaving probability       */
/*      in Confidence							 */
/*									 */
/*************************************************************************/


RuleNo BestRuleIndex(CaseDesc, Start)
/*     ---------------  */
    Description CaseDesc;
    RuleNo Start;
{
    RuleNo r, ri;
    float Strength();

    ForEach(ri, Start, NRules)
    {
	r = RuleIndex[ri];
	Confidence = Strength(Rule[r], CaseDesc);

	if ( Confidence > 0.1 )
	{
	    return ri;
	}
    }

    Confidence = 0.0;
    return 0;
}
/*************************************************************************/
/*									 */
/*  Statistical routines for C4.5					 */
/*  -----------------------------					 */
/*									 */
/*************************************************************************/



									
/*************************************************************************/
/*									 */
/*  Compute the additional errors if the error rate increases to the	 */
/*  upper limit of the confidence level.  The coefficient is the	 */
/*  square of the number of standard deviations corresponding to the	 */
/*  selected confidence level.  (Taken from Documenta Geigy Scientific	 */
/*  Tables (Sixth Edition), p185 (with modifications).)			 */
/*									 */
/*************************************************************************/


float Val[] = {  0,  0.001, 0.005, 0.01, 0.05, 0.10, 0.20, 0.40, 1.00},
      Dev[] = {4.0,  3.09,  2.58,  2.33, 1.65, 1.28, 0.84, 0.25, 0.00};


float AddErrs(N, e)
/*    -------  */
    ItemCount N, e;
{
    static float Coeff=0;
    float Val0, Pr;

    if ( ! Coeff )
    {
	/*  Compute and retain the coefficient value, interpolating from
	    the values in Val and Dev  */

	int i;

	i = 0;
	while ( CF > Val[i] ) i++;

	Coeff = Dev[i-1] +
		  (Dev[i] - Dev[i-1]) * (CF - Val[i-1]) /(Val[i] - Val[i-1]);
	Coeff = Coeff * Coeff;
    }

    if ( e < 1E-6 )
    {
	return N * (1 - exp(log(CF) / N));
    }
    else
    if ( e < 0.9999 )
    {
	Val0 = N * (1 - exp(log(CF) / N));
	return Val0 + e * (AddErrs(N, 1.0) - Val0);
    }
    else
    if ( e + 0.5 >= N )
    {
	return 0.67 * (N - e);
    }
    else
    {
	Pr = (e + 0.5 + Coeff/2
	        + sqrt(Coeff * ((e + 0.5) * (1 - (e + 0.5)/N) + Coeff/4)) )
             / (N + Coeff);
	return (N * Pr - e);
    }
}
/*************************************************************************/
/*								  	 */
/*	Routine for printing confusion matrices				 */
/*	---------------------------------------				 */
/*								  	 */
/*************************************************************************/



    PrintConfusionMatrix(ConfusionMat)
/*  --------------------  */
    ItemNo *ConfusionMat;
{
    short Row, Col;

    if ( MaxClass > 20 ) return;  /* Don't print nonsensical matrices */

    /*  Print the heading, then each row  */

    printf("\n\n\t");
    ForEach(Col, 0, MaxClass)
    {
	printf("  (%c)", 'a' + Col);
    }

    printf("\t<-classified as\n\t");
    ForEach(Col, 0, MaxClass)
    {
	printf(" ----");
    }
    printf("\n");

    ForEach(Row, 0, MaxClass)
    {
	printf("\t");
	ForEach(Col, 0, MaxClass)
	{
	    if ( ConfusionMat[Row*(MaxClass+1) + Col] )
	    {
		printf("%5d", ConfusionMat[Row*(MaxClass+1) + Col]);
	    }
	    else
	    {
		printf("     ");
	    }
	}
	printf("\t(%c): class %s\n", 'a' + Row, ClassName[Row]);
    }
    printf("\n");
}
/*************************************************************************/
/*									 */
/*	Sorting utilities						 */
/*	-----------------						 */
/*									 */
/*************************************************************************/





/*************************************************************************/
/*									 */
/*	Sort items from Fp to Lp on attribute a				 */
/*									 */
/*************************************************************************/


    Quicksort(Fp, Lp, Att, Exchange)
/*  ---------  */
    ItemNo Fp, Lp;
    Attribute Att;
    void (*Exchange)();
{
    register ItemNo Lower, Middle;
    register float Thresh;
    register ItemNo i;

    if ( Fp < Lp )
    {
	Thresh = CVal(Item[Lp], Att);

	/*  Isolate all items with values <= threshold  */

	Middle = Fp;

	for ( i = Fp ; i < Lp ; i++ )
	{ 
	    if ( CVal(Item[i], Att) <= Thresh )
	    { 
		if ( i != Middle ) (*Exchange)(Middle, i);
		Middle++; 
	    } 
	} 

	/*  Extract all values equal to the threshold  */

	Lower = Middle - 1;

	for ( i = Lower ; i >= Fp ; i-- )
	{
	    if ( CVal(Item[i], Att) == Thresh )
	    { 
		if ( i != Lower ) (*Exchange)(Lower, i);
		Lower--;
	    } 
	} 

	/*  Sort the lower values  */

	Quicksort(Fp, Lower, Att, Exchange);

	/*  Position the middle element  */

	(*Exchange)(Middle, Lp);

	/*  Sort the higher values  */

	Quicksort(Middle+1, Lp, Att, Exchange);
    }
}
/*************************************************************************/
/*									 */
/*	Get names of classes, attributes and attribute values		 */
/*	-----------------------------------------------------		 */
/*									 */
/*************************************************************************/



#include <sys/types.h>
#include <sys/stat.h>


#define  Space(s)	(s == ' ' || s == '\n' || s == '\t')
#define  SkipComment	while ( ( c = getc(f) ) != '\n' )

char	Delimiter;
String	CopyString();



/*************************************************************************/
/*									 */
/*  Read a name from file f into string s, setting Delimiter.		 */
/*									 */
/*  - Embedded periods are permitted, but periods followed by space	 */
/*    characters act as delimiters.					 */
/*  - Embedded spaces are permitted, but multiple spaces are replaced	 */
/*    by a single space.						 */
/*  - Any character can be escaped by '\'.				 */
/*  - The remainder of a line following '|' is ignored.			 */
/*									 */
/*************************************************************************/


Boolean ReadName(f, s)
/*      ---------  */
    FILE *f;
    String s;
{
    register char *Sp=s;
    register int c;

    /*  Skip to first non-space character  */

    while ( ( c = getc(f) ) == '|' || Space(c) )
    {
	if ( c == '|' ) SkipComment;
    }

    /*  Return false if no names to read  */

    if ( c == EOF )
    {
	Delimiter = EOF;
	return false;
    }

    /*  Read in characters up to the next delimiter  */

    while ( c != ':' && c != ',' && c != '\n' && c != '|' && c != EOF )
    {
	if ( c == '.' )
	{
	    if ( ( c = getc(f) ) == '|' || Space(c) ) break;
	    *Sp++ = '.';
	}

	if ( c == '\\' )
	{
	    c = getc(f);
	}

	*Sp++ = c;

	if ( c == ' ' )
	{
	    while ( ( c = getc(f) ) == ' ' )
		;
	}
	else
	{
	    c = getc(f);
	}
    }

    if ( c == '|' ) SkipComment;
    Delimiter = c;

    /*  Strip trailing spaces  */

    while ( Space(*(Sp-1)) ) Sp--;

    *Sp++ = '\0';
    return true;
}



/*************************************************************************/
/*									 */
/*  Read the names of classes, attributes and legal attribute values.	 */
/*  On completion, these names are stored in:				 */
/*	ClassName	-  class names					 */
/*	AttName		-  attribute names				 */
/*	AttValName	-  attribute value names			 */
/*  with:								 */
/*	MaxAttVal	-  number of values for each attribute		 */
/*									 */
/*  Other global variables set are:					 */
/*	MaxAtt		-  maximum attribute number			 */
/*	MaxClass	-  maximum class number				 */
/*	MaxDiscrVal	-  maximum discrete values for any attribute	 */
/*									 */
/*  Note:  until the number of attributes is known, the name		 */
/*	   information is assembled in local arrays			 */
/*									 */
/*************************************************************************/


    GetNames()
/*  ---------  */
{
    FILE *Nf, *fopen();
    char Fn[100], Buffer[1000];
    DiscrValue v;
    int AttCeiling=100, ClassCeiling=100, ValCeiling;

    /*  Open names file  */

    strcpy(Fn, FileName);
    strcat(Fn, ".names");
    if ( ! ( Nf = fopen(Fn, "r") ) ) Error(0, Fn, "");

    /*  Get class names from names file  */

    ClassName = (String *) calloc(ClassCeiling, sizeof(String));
    MaxClass = -1;
    do
    {
	ReadName(Nf, Buffer);

	if ( ++MaxClass >= ClassCeiling)
	{
	    ClassCeiling += 100;
	    ClassName = (String *) realloc(ClassName, ClassCeiling*sizeof(String));
	}
	ClassName[MaxClass] = CopyString(Buffer);
    }
    while ( Delimiter == ',' );

    /*  Get attribute and attribute value names from names file  */

    AttName = (String *) calloc(AttCeiling, sizeof(String));
    MaxAttVal = (DiscrValue *) calloc(AttCeiling, sizeof(DiscrValue));
    AttValName = (String **) calloc(AttCeiling, sizeof(String *));
    SpecialStatus = (char *) malloc(AttCeiling);

    MaxAtt = -1;
    while ( ReadName(Nf, Buffer) )
    {
	if ( Delimiter != ':' ) Error(1, Buffer, "");

	if ( ++MaxAtt >= AttCeiling )
	{
	    AttCeiling += 100;
	    AttName = (String *) realloc(AttName, AttCeiling*sizeof(String));
	    MaxAttVal = (DiscrValue *) realloc(MaxAttVal, AttCeiling*sizeof(DiscrValue));
	    AttValName = (String **) realloc(AttValName, AttCeiling*sizeof(String *));
	    SpecialStatus = (char *) realloc(SpecialStatus, AttCeiling);
	}

	AttName[MaxAtt] = CopyString(Buffer);
	SpecialStatus[MaxAtt] = Nil;
	MaxAttVal[MaxAtt] = 0;
	ValCeiling = 100;
	AttValName[MaxAtt] = (String *) calloc(ValCeiling, sizeof(String));

	do
	{
	    if ( ! ( ReadName(Nf, Buffer) ) ) Error(2, AttName[MaxAtt], "");

	    if ( ++MaxAttVal[MaxAtt] >= ValCeiling )
	    {
		ValCeiling += 100;
		AttValName[MaxAtt] =
		    (String *) realloc(AttValName[MaxAtt], ValCeiling*sizeof(String));
	    }

	    AttValName[MaxAtt][MaxAttVal[MaxAtt]] = CopyString(Buffer);
	}
	while ( Delimiter == ',' );

	if ( MaxAttVal[MaxAtt] == 1 )
	{
	    /*  Check for special treatment  */

	    if ( ! strcmp(Buffer, "continuous") )
	    {}
	    else
	    if ( ! memcmp(Buffer, "discrete", 8) )
	    {
		SpecialStatus[MaxAtt] = DISCRETE;

		/*  Read max values, reserve space and check MaxDiscrVal  */

		v = atoi(&Buffer[8]);
		if ( v < 2 )
		{
		    printf("** %s: illegal number of discrete values\n",
			   AttName[MaxAtt]);
		    exit(1);
		}

		AttValName[MaxAtt] =
		    (String *) realloc(AttValName[MaxAtt], (v+2)*sizeof(String));
		AttValName[MaxAtt][0] = (char *) v;
		if ( v > MaxDiscrVal ) MaxDiscrVal = v;
	    }
	    else
	    if ( ! strcmp(Buffer, "ignore") )
	    {
		SpecialStatus[MaxAtt] = IGNORE;
	    }
	    else
	    {
		/*  Cannot have only one discrete value for an attribute  */

		Error(3, AttName[MaxAtt], "");
	    }

	    MaxAttVal[MaxAtt] = 0;
	}
	else
	if ( MaxAttVal[MaxAtt] > MaxDiscrVal ) MaxDiscrVal = MaxAttVal[MaxAtt];
    }

    fclose(Nf);
}



/*************************************************************************/
/*									 */
/*	Locate value Val in List[First] to List[Last]			 */
/*									 */
/*************************************************************************/


int Which(Val, List, First, Last)
/*  -----  */
    String Val, List[];
    short First, Last;
{
    short n=First;

    while ( n <= Last && strcmp(Val, List[n]) ) n++;

    return ( n <= Last ? n : First-1 );
}



/*************************************************************************/
/*									 */
/*	Allocate space then copy string into it				 */
/*									 */
/*************************************************************************/

String CopyString(x)
/*     -----------  */
    String x;
{
    char *s;

    s = (char *) calloc(strlen(x)+1, sizeof(char));
    strcpy(s, x);
    return s;
}



/*************************************************************************/
/*									 */
/*			Error messages					 */
/*									 */
/*************************************************************************/

    Error(n, s1, s2)
/*  -----  */
    short n;
    String s1, s2;
{
    static char Messages=0;

    printf("\nERROR:  ");
    switch(n)
    {
	case 0: printf("cannot open file %s%s\n", s1, s2);
		exit(1);

	case 1:	printf("colon expected after attribute name %s\n", s1);
		break;

	case 2:	printf("unexpected eof while reading attribute %s\n", s1);
		break;

	case 3: printf("attribute %s has only one value\n", s1);
		break;

	case 4: printf("case %d's value of '%s' for attribute %s is illegal\n",
		    MaxItem+1, s2, s1);
		break;

	case 5: printf("case %d's class of '%s' is illegal\n", MaxItem+1, s2);
    }

    if ( ++Messages > 10 )
    {
	printf("Error limit exceeded\n");
	exit(1);
    }
}
/*************************************************************************/
/*									 */
/*	Get case descriptions from data file				 */
/*	--------------------------------------				 */
/*									 */
/*************************************************************************/



#define Inc 2048



/*************************************************************************/
/*									 */
/*  Read raw case descriptions from file with given extension.		 */
/*									 */
/*  On completion, cases are stored in array Item in the form		 */
/*  of Descriptions (i.e. arrays of attribute values), and		 */
/*  MaxItem is set to the number of data items.				 */
/*									 */
/*************************************************************************/

    GetData(Extension)
/*  --------  */
    String Extension;
{
    FILE *Df, *fopen();
    char Fn[100];
    ItemNo i=0, j, ItemSpace=0;
    Description GetDescription();

    /*  Open data file  */

    strcpy(Fn, FileName);
    strcat(Fn, Extension);
    if ( ! ( Df = fopen(Fn, "r") ) ) Error(0, Fn, "");

    do
    {
	MaxItem = i;

	/*  Make sure there is room for another item  */

	if ( i >= ItemSpace )
	{
	    if ( ItemSpace )
	    {
		ItemSpace += Inc;
		Item = (Description *)
			realloc(Item, ItemSpace*sizeof(Description));
	    }
	    else
	    {
		Item = (Description *)
			malloc((ItemSpace=Inc)*sizeof(Description));
	    }
	}

	Item[i] = GetDescription(Df);

    } while ( Item[i] != Nil && ++i );

    fclose(Df);
    MaxItem = i - 1;
}



/*************************************************************************/
/*									 */
/*  Read a raw case description from file Df.				 */
/*									 */
/*  For each attribute, read the attribute value from the file.		 */
/*  If it is a discrete valued attribute, find the associated no.	 */
/*  of this attribute value (if the value is unknown this is 0).	 */
/*									 */
/*  Returns the Description of the case (i.e. the array of		 */
/*  attribute values).							 */
/*									 */
/*************************************************************************/


Description GetDescription(Df)
/*          ---------------  */
    FILE *Df;
{
    Attribute Att;
    char name[500], *endname, *CopyString();
    Boolean ReadName();
    int Dv;
    float Cv;
    Description Dvec;
    double strtod();

    if ( ReadName(Df, name) )
    {
	Dvec = (Description) calloc(MaxAtt+2, sizeof(AttValue));

        ForEach(Att, 0, MaxAtt)
        {
	    if ( SpecialStatus[Att] == IGNORE )
	    {
		/*  Skip this value  */

		DVal(Dvec, Att) = 0;
	    }
	    else
	    if ( MaxAttVal[Att] || SpecialStatus[Att] == DISCRETE )
	    {
		/*  Discrete value  */ 

	        if ( ! ( strcmp(name, "?") ) )
		{
		    Dv = 0;
		}
	        else
	        {
		    Dv = Which(name, AttValName[Att], 1, MaxAttVal[Att]);
		    if ( ! Dv )
		    {
			if ( SpecialStatus[Att] == DISCRETE )
			{
			    /*  Add value to list  */

			    Dv = ++MaxAttVal[Att];
			    if ( Dv > (int) AttValName[Att][0] )
			    {
				printf("\nToo many values for %s (max %d)\n",
					AttName[Att], (int) AttValName[Att][0]);
				exit(1);
			    }

			    AttValName[Att][Dv] = CopyString(name);
			}
			else
			{
			    Error(4, AttName[Att], name);
			}
		    }
	        }
	        DVal(Dvec, Att) = Dv;
	    }
	    else
	    {
		/*  Continuous value  */

	        if ( ! ( strcmp(name, "?") ) )
		{
		    Cv = Unknown;
		}
	        else
		{
		    Cv = strtod(name, &endname);
		    if ( endname == name || *endname != '\0' )
			Error(4, AttName[Att], name);
		}
		CVal(Dvec, Att) = Cv;
	    }

	    ReadName(Df, name);
        }

        if ( (Dv = Which(name, ClassName, 0, MaxClass)) < 0 )
        {
	    Error(5, "", name);
	    Dv = 0;
        }
	Class(Dvec) = Dv;

	return Dvec;
    }
    else
    {
	return Nil;
    }
}
/*************************************************************************/
/*                                                              	 */
/*  Determine the class of a case description from a decision tree	 */
/*  --------------------------------------------------------------	 */
/*                                                              	 */
/*************************************************************************/



float	*ClassSum=Nil;		/* ClassSum[c] = total weight of class c */



/*************************************************************************/
/*                                                              	 */
/*  Categorize a case description using the given decision tree		 */
/*                                                              	 */
/*************************************************************************/


ClassNo Category(CaseDesc, DecisionTree) 
/*       --------  */
    Description CaseDesc; 
    Tree DecisionTree; 
{ 
    ClassNo c, BestClass;

    if ( ! ClassSum )
    {
	ClassSum = (float *) malloc((MaxClass+1) * sizeof(float));
    }

    ForEach(c, 0, MaxClass)
    {
	ClassSum[c] = 0;
    }

    Classify(CaseDesc, DecisionTree, 1.0);

    BestClass = 0;
    ForEach(c, 0, MaxClass)
    {
	Verbosity(5) printf("class %s weight %.2f\n", ClassName[c], ClassSum[c]);

	if ( ClassSum[c] > ClassSum[BestClass] ) BestClass = c;
    }

    return BestClass;
}



/*************************************************************************/
/*                                                              	 */
/*  Classify a case description using the given subtree by adjusting	 */
/*  the value ClassSum for each class					 */
/*                                                              	 */
/*************************************************************************/


    Classify(CaseDesc, T, Weight)
/*  --------  */
    Description CaseDesc; 
    Tree T;
    float Weight;
{
    DiscrValue v, dv;
    float Cv;
    Attribute a;
    ClassNo c;

    switch ( T->NodeType )
    {
        case 0:  /* leaf */

	    if ( T->Items > 0 )
	    {
		/*  Update from ALL classes  */

		ForEach(c, 0, MaxClass)
		{
		    if ( T->ClassDist[c] )
		    {
			ClassSum[c] += Weight * T->ClassDist[c] / T->Items;
		    }
		}
	    }
	    else
	    {
		ClassSum[T->Leaf] += Weight;
	    }

	    return;

	case BrDiscr:  /* test of discrete attribute */

	    a = T->Tested;
	    v = DVal(CaseDesc, a);

	    if ( v && v <= T->Forks )	/*  Make sure not new discrete value  */
	    {
		Classify(CaseDesc, T->Branch[v], Weight);
	    }
	    else
	    {
		ForEach(v, 1, T->Forks)
		{
		    Classify(CaseDesc, T->Branch[v], 
			     (Weight * T->Branch[v]->Items) / T->Items);
		}
	    }

	    return;

	case ThreshContin:  /* test of continuous attribute */

	    a = T->Tested;
	    Cv = CVal(CaseDesc, a);

	    if ( Cv == Unknown )
	    {
		ForEach(v, 1, 2)
		{
		    Classify(CaseDesc, T->Branch[v], 
			     (Weight * T->Branch[v]->Items) / T->Items);
		}
	    }
	    else
	    {
		v = ( Cv <= T->Cut ? 1 : 2 );
		Classify(CaseDesc, T->Branch[v], Weight);
	    }

	    return;

	case BrSubset:  /* subset test on discrete attribute  */

	    a = T->Tested;
	    dv = DVal(CaseDesc, a);

	    if ( dv )
	    {
		ForEach(v, 1, T->Forks)
		{
		    if ( In(dv, T->Subset[v]) )
		    {
			Classify(CaseDesc, T->Branch[v], Weight);

			return;
		    }
		}
	    }

	    /*  Value unknown or not found in any of the subsets  */

	    ForEach(v, 1, T->Forks)
	    {
		Classify(CaseDesc, T->Branch[v], 
		         (Weight * T->Branch[v]->Items) / T->Items);
	    }

	    return;
    } 
}
/*************************************************************************/
/*									 */
/*	Routines for displaying, building, saving and restoring trees	 */
/*	-------------------------------------------------------------	 */
/*									 */
/*************************************************************************/




#define	Tab		"|   "
#define	TabSize		4
#define	Width		80	/* approx max width of printed trees */

	/*  If lines look like getting too long while a tree is being
	    printed, subtrees are broken off and printed separately after
	    the main tree is finished	 */

short	Subtree;		/* highest subtree to be printed */
Tree	Subdef[100];		/* pointers to subtrees */

FILE	*TRf = 0, *fopen();	/* file pointer for tree i/o */
char	Fn[500];		/* file name */



/*************************************************************************/
/*									 */
/*	Display entire decision tree T					 */
/*									 */
/*************************************************************************/


    PrintTree(T)
/*  ----------  */
    Tree T;
{
    short s;

    Subtree=0;
    printf("Decision Tree:\n");
    Show(T, 0);
    printf("\n");

    ForEach(s, 1, Subtree)
    {
	printf("\n\nSubtree [S%d]\n", s);
	Show(Subdef[s], 0);
	printf("\n");
    }
    printf("\n");
}



/*************************************************************************/
/*									 */
/*	Display the tree T with offset Sh				 */
/*									 */
/*************************************************************************/


    Show(T, Sh)
/*  ---- */
    Tree T;
    short Sh;
{
    DiscrValue v, MaxV;
    short MaxLine();

    if ( T->NodeType )
    {
	/*  See whether separate subtree needed  */

	if ( T != Nil && Sh && Sh * TabSize + MaxLine(T) > Width )
	{
	    if ( Subtree < 99 )
	    {
		Subdef[++Subtree] = T;
		printf("[S%d]", Subtree);
	    }
	    else
	    {
		printf("[S??]");
	    }
	}
	else
	{
	    MaxV = T->Forks;

	    /*  Print simple cases first */

	    ForEach(v, 1, MaxV)
	    {
		if ( ! T->Branch[v]->NodeType )
		{
		    ShowBranch(Sh, T, v);
		}
	    }

	    /*  Print subtrees  */

	    ForEach(v, 1, MaxV)
	    {
		if ( T->Branch[v]->NodeType )
		{
		    ShowBranch(Sh, T, v);
		}
	    }
	}
    }
    else
    {
	printf(" %s (%.1f", ClassName[T->Leaf], T->Items);
	if ( T->Errors > 0 ) printf("/%.1f", T->Errors);
	printf(")");
    }
}



/*************************************************************************/
/*									 */
/*	Print a node T with offset Sh, branch value v, and continue	 */
/*									 */
/*************************************************************************/


    ShowBranch(Sh, T, v)
/*  -----------  */
    short Sh;
    Tree T;
    DiscrValue v;
{
    DiscrValue Pv, Last;
    Attribute Att;
    Boolean FirstValue;
    short TextWidth, Skip, Values=0, i;
    
    Att = T->Tested;

    switch ( T->NodeType )
    {
	case BrDiscr:

	    Indent(Sh, Tab);

	    printf("%s = %s:", AttName[Att], AttValName[Att][v]);
	    break;

	case ThreshContin:

	    Indent(Sh, Tab);

	    printf("%s %s %g ",
		    AttName[Att], ( v == 1 ? "<=" : ">" ), T->Cut);

	    if ( T->Lower != T->Upper )
	    {
		printf("[%g,%g]", T->Lower, T->Upper);
	    }

	    printf(":");
	    break;

	case BrSubset:

	    /*  Count values at this branch  */

	    ForEach(Pv, 1, MaxAttVal[Att])
	    {
		if ( In(Pv, T->Subset[v]) )
		{
		    Last = Pv;
		    Values++;
		}
	    }
	    if ( ! Values ) return;

	    Indent(Sh, Tab);

	    if ( Values == 1 )
	    {
		printf("%s = %s:", AttName[Att], AttValName[Att][Last]);
		break;
	    }

	    printf("%s in {", AttName[Att]);
	    FirstValue = true;
	    Skip = TextWidth = strlen(AttName[Att]) + 5;

	    ForEach(Pv, 1, MaxAttVal[Att])
	    {
		if ( In(Pv, T->Subset[v]) )
		{
		    if ( ! FirstValue &&
			 TextWidth + strlen(AttValName[Att][Pv]) + 11 > Width )
		    {
		  	Indent(Sh, Tab);
			ForEach(i, 1, Skip) putchar(' ');

			TextWidth = Skip;
			FirstValue = true;
		    }

		    printf("%s%c", AttValName[Att][Pv], Pv == Last ? '}' : ',');
		    TextWidth += strlen(AttValName[Att][Pv]) + 1;
		    FirstValue = false;
		}
	    }
	    putchar(':');
    }

    Show(T->Branch[v], Sh+1);
}



/*************************************************************************/
/*									 */
/*	Find the maximum single line size for non-leaf subtree St.	 */
/*	The line format is						 */
/*			<attribute> <> X.xx:[ <class (<Items>)], or	 */
/*			<attribute> = <DVal>:[ <class> (<Items>)]	 */
/*									 */
/*************************************************************************/


short MaxLine(St)
/*    --------  */
    Tree St;
{
    Attribute a;
    DiscrValue v, MaxV, Next;
    short Ll, MaxLl=0;

    a = St->Tested;

    MaxV = St->Forks;
    ForEach(v, 1, MaxV)
    {
	Ll = ( St->NodeType == 2 ? 4 : strlen(AttValName[a][v]) ) + 1;

	/*  Find the appropriate branch  */

        Next = v;

	if ( ! St->Branch[Next]->NodeType )
	{
	    Ll += strlen(ClassName[St->Branch[Next]->Leaf]) + 6;
	}
	MaxLl = Max(MaxLl, Ll);
    }

    return strlen(AttName[a]) + 4 + MaxLl;
}



/*************************************************************************/
/*								   	 */
/*	Indent Sh columns					  	 */
/*								  	 */
/*************************************************************************/

    Indent(Sh, Mark)
/*  ------  */
    short Sh;
    char *Mark;
{
    printf("\n");
    while ( Sh-- ) printf("%s", Mark);
}



/*************************************************************************/
/*									 */
/*	Save entire decision tree T in file with extension Extension	 */
/*									 */
/*************************************************************************/


    SaveTree(T, Extension)
/*  ---------  */
    Tree T;
    String Extension;
{
    static char *LastExt="";

    if ( strcmp(LastExt, Extension) )
    {
	LastExt = Extension;

	if ( TRf ) fclose(TRf);

	strcpy(Fn, FileName);
	strcat(Fn, Extension);
	if ( ! ( TRf = fopen(Fn, "w") ) )
	    Error(0, Fn, " for writing");
    }

    putc('\n', TRf);
    OutTree(T);

    SaveDiscreteNames();
}



/*************************************************************************/
/*									 */
/*	Save tree T as characters					 */
/*									 */
/*************************************************************************/


    OutTree(T)
/*  --------  */
    Tree T;
{
    DiscrValue v;
    int Bytes;

    StreamOut((char *) &T->NodeType, sizeof(short));
    StreamOut((char *) &T->Leaf, sizeof(ClassNo));
    StreamOut((char *) &T->Items, sizeof(ItemCount));
    StreamOut((char *) &T->Errors, sizeof(ItemCount));
    StreamOut((char *) T->ClassDist, (MaxClass + 1) * sizeof(ItemCount));

    if ( T->NodeType )
    {
	StreamOut((char *) &T->Tested, sizeof(Attribute));
	StreamOut((char *) &T->Forks, sizeof(short));

	switch ( T->NodeType )
	{
	    case BrDiscr:
		break;

	    case ThreshContin:
		StreamOut((char *) &T->Cut, sizeof(float));
		StreamOut((char *) &T->Lower, sizeof(float));
		StreamOut((char *) &T->Upper, sizeof(float));
		break;

	    case BrSubset:
		Bytes = (MaxAttVal[T->Tested]>>3) + 1;
		ForEach(v, 1, T->Forks)
		{
		    StreamOut((char *) T->Subset[v], Bytes);
		}
		break;
	}

	ForEach(v, 1, T->Forks)
	{
	    OutTree(T->Branch[v]);
	}
    }
}



/*************************************************************************/
/*									 */
/*	Retrieve entire decision tree with extension Extension		 */
/*									 */
/*************************************************************************/


Tree GetTree(Extension)
/*   --------  */
    String Extension;
{
    Tree Hold, InTree();
    static char *LastExt="";

    if ( strcmp(LastExt, Extension) )
    {
	LastExt = Extension;

	if ( TRf ) fclose(TRf);

	strcpy(Fn, FileName);
	strcat(Fn, Extension);
	if ( ! ( TRf = fopen(Fn, "r") ) ) Error(0, Fn, "");
    }

    if ( ! TRf || getc(TRf) == EOF ) return Nil;

    Hold = InTree();

    RecoverDiscreteNames();

    return Hold;
}



/*************************************************************************/
/*									 */
/*	Retrieve tree from saved characters				 */
/*									 */
/*************************************************************************/


Tree InTree()
/*   -------  */
{
    Tree T;
    DiscrValue v;
    int Bytes;

    T = (Tree) malloc(sizeof(TreeRec));

    StreamIn((char *) &T->NodeType, sizeof(short));
    StreamIn((char *) &T->Leaf, sizeof(ClassNo));
    StreamIn((char *) &T->Items, sizeof(ItemCount));
    StreamIn((char *) &T->Errors, sizeof(ItemCount));

    T->ClassDist = (ItemCount *) calloc(MaxClass+1, sizeof(ItemCount));
    StreamIn((char *) T->ClassDist, (MaxClass + 1) * sizeof(ItemCount));

    if ( T->NodeType )
    {
	StreamIn((char *) &T->Tested, sizeof(Attribute));
	StreamIn((char *) &T->Forks, sizeof(short));

	switch ( T->NodeType )
	{
	    case BrDiscr:
		break;

	    case ThreshContin:
		StreamIn((char *) &T->Cut, sizeof(float));
		StreamIn((char *) &T->Lower, sizeof(float));
		StreamIn((char *) &T->Upper, sizeof(float));
		break;

	    case BrSubset:
		T->Subset = (Set *) calloc(T->Forks + 1, sizeof(Set));

		Bytes = (MaxAttVal[T->Tested]>>3) + 1;
		ForEach(v, 1, T->Forks)
		{
		    T->Subset[v] = (Set) malloc(Bytes);
		    StreamIn((char *) T->Subset[v], Bytes);
		}
	}

	T->Branch = (Tree *) calloc(T->Forks + 1, sizeof(Tree));
	ForEach(v, 1, T->Forks)
	{
	    T->Branch[v] = InTree();
	}
    }

    return T;
}



/*************************************************************************/
/*									 */
/*	Stream characters to/from file TRf from/to an address		 */
/*									 */
/*************************************************************************/


    StreamOut(s, n)
/*  ---------  */
    String s;
    int n;
{
    while ( n-- ) putc(*s++, TRf);
}



    StreamIn(s, n)
/*  ---------  */
    String s;
    int n;
{
    while ( n-- ) *s++ = getc(TRf);
}



/*************************************************************************/
/*									 */
/*	Free up space taken up by tree Node				 */
/*									 */
/*************************************************************************/


    ReleaseTree(Node)
/*  -------  */
    Tree Node;
{
    DiscrValue v;

    if ( Node->NodeType )
    {
	ForEach(v, 1, Node->Forks)
	{
	    ReleaseTree(Node->Branch[v]);
	}

	free(Node->Branch);

	if ( Node->NodeType == BrSubset )
	{
	    free(Node->Subset);
	}

    }

    free(Node->ClassDist);
    free(Node);
}



/*************************************************************************/
/*									 */
/*	Construct a leaf in a given node				 */
/*									 */
/*************************************************************************/


Tree Leaf(ClassFreq, NodeClass, Cases, Errors)
/*   ----  */
    ItemCount *ClassFreq;
    ClassNo NodeClass;
    ItemCount Cases, Errors;
{
    Tree Node;

    Node = (Tree) calloc(1, sizeof(TreeRec));

    Node->ClassDist = (ItemCount *) calloc(MaxClass+1, sizeof(ItemCount));
    memcpy(Node->ClassDist, ClassFreq, (MaxClass+1) * sizeof(ItemCount));
    
    Node->NodeType	= 0; 
    Node->Leaf		= NodeClass;
    Node->Items		= Cases;
    Node->Errors	= Errors;

    return Node; 
}



/*************************************************************************/
/*									 */
/*	Insert branches in a node 	                 		 */
/*									 */
/*************************************************************************/


    Sprout(Node, Branches)
/*  ------  */
    Tree Node;
    DiscrValue Branches;
{
    Node->Forks = Branches;
    
    Node->Branch = (Tree *) calloc(Branches+1, sizeof(Tree));
}



/*************************************************************************/
/*									 */
/*	Count the nodes in a tree					 */
/*									 */
/*************************************************************************/

	
    TreeSize(Node)
/*  --------  */
    Tree Node;
{
    int Sum=0;
    DiscrValue v;

    if ( Node->NodeType )
    {
	ForEach(v, 1, Node->Forks)
	{
	    Sum += TreeSize(Node->Branch[v]);
	}
    }

    return Sum + 1;
}



/*************************************************************************/
/*									 */
/*	Return a copy of tree T						 */
/*									 */
/*************************************************************************/


Tree CopyTree(T)
/*   ---------  */
    Tree T;
{
    DiscrValue v;
    Tree New;

    New = (Tree) malloc(sizeof(TreeRec));
    memcpy(New, T, sizeof(TreeRec));

    New->ClassDist = (ItemCount *) calloc(MaxClass+1, sizeof(ItemCount));
    memcpy(New->ClassDist, T->ClassDist, (MaxClass + 1) * sizeof(ItemCount));

    if ( T->NodeType )
    {
	New->Branch = (Tree *) calloc(T->Forks + 1, sizeof(Tree));
	ForEach(v, 1, T->Forks)
	{
	    New->Branch[v] = CopyTree(T->Branch[v]);
	}
    }

    return New;
}



/*************************************************************************/
/*									 */
/*	Save attribute values read with "discrete N"			 */
/*									 */
/*************************************************************************/


    SaveDiscreteNames()
/*  -----------------  */
{
    Attribute Att;
    DiscrValue v;
    int Length;

    ForEach(Att, 0, MaxAtt)
    {
	if ( SpecialStatus[Att] != DISCRETE ) continue;

	StreamOut((char *) &MaxAttVal[Att], sizeof(int));

	ForEach(v, 1, MaxAttVal[Att])
	{
	    Length = strlen(AttValName[Att][v]) + 1;

	    StreamOut((char *) &Length, sizeof(int));
	    StreamOut((char *) AttValName[Att][v], Length);
	}
    }
}



/*************************************************************************/
/*									 */
/*	Recover attribute values read with "discrete N"			 */
/*									 */
/*************************************************************************/


    RecoverDiscreteNames()
/*  --------------------  */
{
    Attribute Att;
    DiscrValue v;
    int Length;

    ForEach(Att, 0, MaxAtt)
    {
	if ( SpecialStatus[Att] != DISCRETE ) continue;

	StreamIn(&MaxAttVal[Att], sizeof(int));

	ForEach(v, 1, MaxAttVal[Att])
	{
	    StreamIn(&Length, sizeof(int));

	    AttValName[Att][v] = (char *) malloc(Length);
	    StreamIn(AttValName[Att][v], Length);
	}
    }
}
/*************************************************************************/
/*									 */
/*	Print header for all C4.5 programs				 */
/*	----------------------------------				 */
/*									 */
/*************************************************************************/


#define  RELEASE "8"


    PrintHeader(Title)
/*  -----------  */
    char *Title;
{
    char *ctime(), TitleLine[80];
    long clock, time();
    short Underline;

    clock = time(0);
    sprintf(TitleLine, "C4.5 [release %s] %s", RELEASE, Title);
    printf("\n%s\t%s", TitleLine, ctime(&clock));

    Underline = strlen(TitleLine);
    while ( Underline-- ) putchar('-');
    putchar('\n');
}
