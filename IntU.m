(* ::Package:: *)

BeginPackage["IntU`"];
Unprotect@@Names["IntU`*"]
Clear@@Names["IntU`*"]

(*Variable[text_?StringQ]:= "\!\(\*StyleBox[\""<>text<>"\", \"TI\"]\)"
Variable[a_,b__]:=Variable[a]<>","<>Variable[b]
 
Func[text_?StringQ]:= "\!\(\*StyleBox[\""<>text<>"\", \"Input\"]\)"
Func[a_,b__]:=Func[a]<>","<>Func[b]
*)



IntUDOIToString[text_,doi_]:="\!\(\*ButtonBox[StyleBox[\""<>text<>"\", \"SR\"],Active->True,BaseStyle->\"Link\",ButtonData->\"http://dx.doi.org/"<>doi<>"\"]\)";
IntUciteCollins06 = IntUDOIToString["[Collins&\:015aniady 2006]","10.1007/s00220-006-1554-3"];
IntUciteBernstein04 = IntUDOIToString["[Bernstein 2004]","10.1016/j.jsc.2003.11.001"];
IntUDocumentationReaplcements = {"<v>" -> "\!\(\*StyleBox[\"" , "</v>" -> "\", \"TI\"]\)", "<f>"->"\!\(\*StyleBox[\"", "</f>" -> "\", \"Input\"]\)"} 



(* ::Section:: *)
(*Help messages*)


IntegrateUnitaryHaar::usage = StringReplace[
"<f>IntegrateUnitaryHaar</f>[<v>integrand</v>,{<v>var</v>,<v>dim</v>}] \
gives the definite integral on unitary group with respect to the Haar measure, accepting the following arguments: 
-<v>integrand</v> - the polynomial type expression of variable <v>var</v> with indices placed as subscripts, \
can contain any other symbolic expression of other variables,
-<v>var</v> - the symbol of variable for integration,   
-<v>dim</v> - the dimension of a unitary group, must be a positive integer.
<f>IntegrateUnitaryHaar</f>[<v>f</v>,{<v>u</v>,<v>d1</v>},{<v>v</v>,<v>d2</v>} ...] \
gives multiple integral."
,IntUDocumentationReaplcements]

IntegrateUnitaryHaarIndices::usage = StringReplace[
"<f>IntegrateUnitaryHaarIndices</f>{<v>I1</v>,<v>J1</v>,<v>I2</v>,<v>J2</v>},<v>dim</v>] \
gives a definite integral on unitary group with respect to the Haar measure for given indices. see "<>IntUciteCollins06<>"."
,IntUDocumentationReaplcements]

Weingarten::usage = StringReplace[
"<f>Weingarten</f>[<v>type</v>,<v>dim</v>] - returns the value of <v>Weingarten</v> function defined in \
"<>IntUciteCollins06<>" and accepts the following arguments:
-<v>type</v> - an integer partition which corresponds to the cycle type of permutation,
-<v>dim</v> - the dimension of a unitary group, must be a positive integer."
,IntUDocumentationReaplcements]

CharacterSymmetricGroup::usage =  StringReplace[
"<f>CharacterSymmetricGroup</f>[<v>part</v>,<v>type</v>] - \
gives the character of the symmetric group \!\(\*SuperscriptBox[\(\[Chi]\), \(<v>part</v>\)]\)(<v>type</v>)
Parameter <v>type</v> is optional. The default value is set to a trivial \
partition and in this case the function returns the dimension of the irreducible \
representation of symmetric group indexed by <v>part</v>,
If <v>type</v> is specified the value of the character is calculated by Murnaghan-Nakayama rule using \
<v>MNInner</v> algorithm provided in "<>IntUciteBernstein04<>"." 
,IntUDocumentationReaplcements]

SchurPolynomialAt1::usage = StringReplace[ 
"<f>SchurPolynomialAt1</f>[<v>part</v>,<v>dim</v>] - returns the value of the Schur polynomial \!\(\*SubscriptBox[\(s\), \(<v>part</v>\)]\) \
at <v>d</v>-dimensional point (1,1,...,1), i.e. the dimension of irreducible representation of <v>U</v>(<v>dim</v>) corresponding to <v>part</v>."
,IntUDocumentationReaplcements]

PermutationTypePartition::usage = StringReplace[
"<f>PermutationTypePartition</f>[<v>perm</v>] - gives the partition which represents the cycle type of the permutation \
<v>perm</v>."
,IntUDocumentationReaplcements]

MultinomialBeta::usage = StringReplace[
"<f>MultinomialBeta</f>[<v>p</v>] - gives for <v>d</v>-dimensional vector of non negative numbers <v>\!\(\*SubscriptBox[\(p\), \(1\)]\), \!\(\*SubscriptBox[\(p\), \(2\)]\), ... , \!\(\*SubscriptBox[\(p\), \(d\)]\)</v> \
the value of multinomial Beta function defined as \
\!\(\*FractionBox[\(\(\[Product]\[CapitalGamma] \((\*SubscriptBox[\(p\), \(i\)])\)\)\(\\\\n\)\), \(\[CapitalGamma] \((\[Sum]\*SubscriptBox[\(p\), \(i\)])\)\)]\)."
,IntUDocumentationReaplcements]
   
CardinalityConjugacyClassPartition::usage = StringReplace[
"<f>CardinalityConjugacyClassPartition</f>[<v>part</v>] - gives a cardinality of conjugacy class for \
permutation with the cycle type given by a partition <v>part</v>." 
,IntUDocumentationReaplcements]


BinaryPartition::usage = StringReplace[
"<f>BinaryPartition</f>[<v>part</v>] - gives a binary representation of a partition <v>part</v>. \
This function is needed for the implementation of <v>MNInner</v> algorithm in function <f>CharacterSymmetricGroup</f>."
,IntUDocumentationReaplcements]


ConjugatePartition::usage=StringReplace[
"<f>ConjugatePartition</f>[<v>part</v>] -  gives a conjugate of a partition <v>part</v>."
,IntUDocumentationReaplcements]



(* ::Section:: *)
(*Private definitions*)


Begin["`Private`"];

DEBUG = False;
OPT = True;



intuAuthors = "Zbigniew Puchala <z.puchala[at]iitis[dot]pl>, Jaroslaw Miszczak <miszczak[at]iitis[dot]pl>";
intuLicense = "GPLv3 <http://www.gnu.org/licenses/gpl.html>";
intuHistory = {
	{"0.1.0", "28/06/2011", "Zbyszek & Jarek", "Initial version"},
    {"0.1.1", "30/06/2011", "Zbyszek", "Some changes"},
    {"0.1.2", "11/07/2011", "Zbyszek", "Some changes"},
    {"0.1.21", "01/08/2011", "Zbyszek", "Function for Integer partitions deleted - now build in function in use"},
    {"0.1.22", "12/08/2011", "Zbyszek", "Weingarten changed and other stuff"},
    {"0.1.23", "24/08/2011", "Zbyszek", "New optimization and some clean up"},
    {"0.1.24", "26/08/2011", "Zbyszek", "Main function changed - now multiple integrals can be calculated"},
    {"0.1.25", "14/09/2011", "Zbyszek", "Documentation improved"},
    {"0.2.0", "19/09/2011", "Zbyszek & Jarek", "Documentation corrected"},
    {"0.2.1", "03/10/2011", "Zbyszek", "Small error concerning conjugate simplification corrected"},
    {"0.2.2", "04/10/2011", "Zbyszek", "Small error concerning paterns matching"},
    {"0.2.3", "15/01/2012", "Zbyszek", "Some code changes"},
    {"0.3.0", "26/02/2014", "Zbyszek", "Some bugs fixed"}
};
intuVersion = Last[intuHistory][[1]];
intuLastModification = Last[intuHistory][[2]];
intuAbout = " ... ";



(* ::Subsection:: *)
(*Helper functions*)


(*
 Returns the size of conjugancy class for permutation with cycle type given by partition in a group Subscript[S, n],
 see \cite[Eqn.(1.2)]{sagan2001symmetric} 
*)
CardinalityConjugacyClassPartition[partition_]:=Block[{t},
  t = Tally[partition];
  (*return*)
  Total[partition]! / (Product[ (t[[i]][[1]])^(t[[i]][[2]])(t[[i]][[2]])! ,{i,1,Length[t]} ])
]

(*
 Returns a conjugate partition  
*)
ConjugatePartition[part_] := Block[{CountPositive, conj, f},
	CountPositive[x_] := Length[Select[x, # > 0 &]];
    conj = {};
    f = (AppendTo[conj, CountPositive[#]]; # - 1) & ;
    Nest[f, part, part[[1]]];
    (*return*)
    conj
];

(*
 Returns a partition which is a cycle type of a given permutation(in a list form)
*)
PermutationTypePartition[perm_?PermutationListQ]:=Block[{s},  
    s = Sort[Length[#]&/@(PermutationCycles[perm][[1]]),Greater];
    (*return*)
    Join[s,ConstantArray[1,Length[perm]-Total[s]]]
];

(*
 Binary representation of a given partition 
*)
BinaryPartition[partition_]:=Block[{l={}},
    Flatten[Map[Append[l,Flatten[{ConstantArray[1,#],0}]]&,Differences[Prepend[Reverse[partition],0]]]]
];

(* 
 From \cite[Proposition 4.62]{etingof2009introduction}
*)
SchurPolynomialAt1[partt_,dim_]:=Block[{part,zeros},
    zeros = ConstantArray[0, dim-Length[partt]];
    part = Join[partt,zeros];
    (*return*)
    Product[(part[[i]] - part[[j]] + j - i)/(j - i),{j, 1, dim},{i, 1, j-1}]
];

MultinomialBeta[a_]:=(Times@@(Gamma/@a))/(Gamma[Total[a]]);

PositiveIntegerQ[x_]:=And[IntegerQ[x], x> 0]
NotPositiveIntegerQ[x_]:=Not[PositiveIntegerQ[x]]



(* ::Subsection:: *)
(*Weingarten function and function related to*)


(*
 Character of symmetric group at identity permutation, see  \cite[page 57]{james1981representation} 
 Implementation of hook-length formula  
*)
CharacterAtId[partition_]:=Block[{conjPart},
    conjPart = ConjugatePartition[partition];
    (*return*)
    Total[partition]!/ Product[ partition[[i]] - j + conjPart[[j]] - i + 1 , {i, 1,Length[partition]}, {j, 1, partition[[i]]}]
];
(* Implementation of determinant version:
(Total[partition])!Det[Table[1/(partition[[i]] + j - i)!,{i,1,Length[partition]},{j,1,Length[partition]}]]
*)

(*
 Murnaghan-Nakayama algorithm for computing a character of symmetric group Subscript[S, n], algorithm MNInner from \cite{bernstein2004computational}
*)
MurnaghanNakayama[Rr_,mm_,tt_:1]:= 
 MurnaghanNakayama[Rr,mm,tt]=Block[{BP,i,j,R=Rr,m=mm,t=tt,c=0,s=1,temp},
 	If[t> Length[m], 
 		c=1,
 	(*else*)
	    c=0; s=1;
	    For[j=1, j < Min[m[[t]],Length[R]], j++, If[R[[j]] == 0, s=-s]; ];
	    For[i=1, i < Length[R] - m[[t]] + 1, i++,
	        If[R[[i]] != R[[ i + m[[t]]-1]], s=-s];
	        If[i + m[[t]] <= Length[R],
	            If[R[[i]] == 1 && R[[ i + m[[t]] ]] == 0,
	                temp = R[[i]];
	                R[[i]] = R[[ i + m[[t]] ]] ;
	                R[[ i + m[[t]] ]]=temp;
	                c = c + s*MurnaghanNakayama[R,m,t+1];
	                temp = R[[i]];
	                R[[i]] = R[[ i + m[[t]] ]];
	                R[[ i + m[[t]] ]] = temp;
	            ]; 
	        ];
	    ];
    ];
  (*return*)
  c
];

CharacterSymmetricGroup[partition_, type_:"id"]:= If[type==="id", CharacterAtId[partition] ,(*else*) MurnaghanNakayama[BinaryPartition[partition], type]];

(*
 Function from \cite{collins06integration}
*)
Weingarten[permutationType_,d__?PositiveIntegerQ]:=(
 Unprotect[Weingarten];
 Weingarten[permutationType,d]=Block[{func,n},    
    func = (CharacterSymmetricGroup[#])^2 CharacterSymmetricGroup[#,permutationType]/SchurPolynomialAt1[#,d]& ;
    n=Total[permutationType];
    1/(n!)^2 Fold[#1 + func[#2] &, 0, IntegerPartitions[n,d]]    
    ]; 
 Protect[Weingarten];
 (*return*) 
 Weingarten[permutationType,d] 
)



(* ::Subsection:: *)
(*Permutations*)


(*
 Finds all permutations which permutes list Idx1 to list Idx2
*)
GetPermutations[Idx1_, Idx2_]:=(*GetPermutations[Idx1, Idx2]=*)Block[{sIdx1, sIdx2,permI1,permI2inv, tally, idx,list,pI,pp},
    If[Length[Idx1]==Length[Idx2],
        sIdx1=Sort[Idx1]; sIdx2=Sort[Idx2];
        If[Total[Abs[sIdx1-sIdx2]]== 0,
            permI1 = FindPermutation[Idx1,sIdx1];
            permI2inv = FindPermutation[sIdx2,Idx2];
            tally = Tally[sIdx1];
            idx = 1;
            list = Table[
                If[i>= 2, idx += tally[[i-1]][[2]]];
                Permutations[Range[idx, idx - 1 + tally[[i]][[2]]]]
                ,{i,1,Length[tally]}];
            If[Length[list]>= 2,
                pI = Flatten[Apply[Outer[Join,##,1]&,list],Length[list]-1];
                ,(*else*)
                pI =Flatten[list,1];
            ];
            pp=Table[PermutationProduct[permI1,PermutationProduct[pI[[i]],permI2inv]],{i,1,Length[pI]}];
            pp
        ,(*else*)
        {}]
    ,(*else*)
    {}]
];



(* ::Subsection:: *)
(*Integral*)


(*
 Inegral for given indices - see \cite[Eqn. 11]{collins06integration}
*)
IntegrateUnitaryHaarIndices[{I1_,J1_,I2_,J2_}, dim_?PositiveIntegerQ]:=(
If[Sort[I1] == Sort[I2] && Sort[J1] == Sort[J2] && Length[I1]==Length[J1] && Length[I1]>0, 
 Unprotect[IntegrateUnitaryHaarIndices];
 IntegrateUnitaryHaarIndices[{I1,J1,I2,J2}, dim]=
 Block[{pIinv,pJ,s, int, perm, type},
	int = Null;
	
	(* 	OPTIMALIZATION FOR KNOWN VALUES OF INTEGRAL *)        
    If[OPT,
          (*
            Optimalization in the case of indices of size 2 - see appendix to "shadow 3" for detailed formula
          *)
        If[Length[I1]==2 && Length[I2]==2 && Length[J1]==2 && Length[J1]==2,
If[DEBUG, Print["OPT 1"];];   
            int =  1/(dim^2 -1)(KroneckerDelta[I1[[1]],I2[[1]]]*KroneckerDelta[I1[[2]],I2[[2]]]*KroneckerDelta[J1[[1]],J2[[1]]]*KroneckerDelta[J1[[2]],J2[[2]]]+
            KroneckerDelta[I1[[1]],I2[[2]]]*KroneckerDelta[I1[[2]],I2[[1]]]*KroneckerDelta[J1[[1]],J2[[2]]]*KroneckerDelta[J1[[2]],J2[[1]]]) -
            1/(dim*(dim^2-1)) (KroneckerDelta[I1[[1]],I2[[1]]]*KroneckerDelta[I1[[2]],I2[[2]]]*KroneckerDelta[J1[[1]],J2[[2]]]*KroneckerDelta[J1[[2]],J2[[1]]]+ 
            KroneckerDelta[I1[[1]],I2[[2]]]*KroneckerDelta[I1[[2]],I2[[1]]]*KroneckerDelta[J1[[1]],J2[[1]]]*KroneckerDelta[J1[[2]],J2[[2]]]);
        ];
  
        (* 
          Optimalization using fact that column of Haar distributed matrix has Uniform distribution on a simplex, see \cite[Chapter 4]{hiai2006semicircle}     
        *)
        If[int === Null,
        Block[{tallyI1, tallyI2, tallyJ1, tallyJ2,ks},
            tallyI1 = Tally[I1]; tallyI2 = Tally[I2]; tallyJ1 = Tally[J1]; tallyJ2 = Tally[J2];        
            If[Length[tallyI1]==1 && Length[tallyI2]==1,    
                If[I1[[1]] == I2[[1]],
                    ks=Join[tallyJ1\[Transpose][[2]],ConstantArray[0,dim - Length[tallyJ1]]];
If[DEBUG, Print["OPT 2"];];
                    int = (dim-1)! MultinomialBeta[ks + 1];     
                , (*else*)
                    int = 0;
                ];
            ];
            (*similarly for exchanging indices*) 
            If[int===Null && Length[tallyJ1]==1 && Length[tallyJ2]==1,
                If[J1[[1]] == J2[[1]],
                    ks=Join[tallyI1\[Transpose][[2]],ConstantArray[0,dim - Length[tallyI1]]];   
If[DEBUG, Print["OPT 2"];];    
                    int = (dim-1)! MultinomialBeta[ks + 1];
                , (*else*)
                    int = 0;
                ];
            ];
        ];  (*end Block*)
        ];  (*end if int === Null*)
        (*new optimization *)   
        If[int === Null && I1==I2 && J1==J2 && Length[I1]>1,
           Block[{test,tI},
                test = True;
                Do[test = test&& (If[I1[[k]]==I1[[l]],J1[[k]]==J1[[l]],True]);If[Not[test],Break[]],{k,1,Length[I1]},{l,1,Length[I1]}];
                If[test,
If[DEBUG, Print["OPT 3"];];
                    Block[{JoinAndMultiply,PartitionsWithConjSize,partitions,sumsOfPartitions,sum},
                        (*temp functions*)
                        JoinAndMultiply[x_,y_]:={Sort[Join[x[[1]],y[[1]]],Greater], x[[2]]*y[[2]]};
	                    JoinAndMultiply[x_,y_,z__]:=JoinAndMultiply[JoinAndMultiply[x,y],z];
	                    PartitionsWithConjSize[n_]:=Block[{ip}, ip=IntegerPartitions[n]; Map[{#,CardinalityConjugacyClassPartition[#]}&,ip]];
	                    (*end temp functions*)
	                    tI=Tally[I1];
	                    partitions=Map[PartitionsWithConjSize,(tI\[Transpose][[2]])];
	                    sumsOfPartitions= Map[Sort[#,Greater]&,Flatten[Apply[Outer[JoinAndMultiply, ##,1]&,partitions],Length[partitions]-1]];
	                    sum =Sum[sumsOfPartitions[[i]][[2]]*Weingarten[sumsOfPartitions[[i]][[1]],dim],{i,1,Length[sumsOfPartitions]}];
	                    int = Fold[#1*#2!&,1,tI\[Transpose][[2]]]*sum;         
                    ];
                ];
            ];
        ];
        If[int === Null && (I1 == I2 == J1) && (And @@ (Unequal @@@ (Transpose[{I1, J2}]))),
            Block[{t, z, test, tJ2, sigma, k, m},
                t = Tally[I1];               
                z = Transpose[t][[2]];
                If[(And @@ Map[Equal[#, z[[1]]] &, z]),
                    test = True;
                    Do[test = test && (If[I1[[k]] == I1[[l]], J2[[k]] == J2[[l]], True]); If[Not[test], Break[]], {k, 1, Length[I1]}, {l, 1, Length[I1]}];
                    If[test,
                    	tJ2 = Tally[J2];
                    	sigma = tJ2\[Transpose][[1]];
                    	If[Length[PermutationTypePartition[sigma]] == 1,
                    		k = z[[1]];
                    		m = Length[z];
If[DEBUG, Print["OPT 4"];];                    		
                    		int = (k!)^(2 m - 1) Total[(CardinalityConjugacyClassPartition[#]*Weingarten[m*#, dim] & /@ IntegerPartitions[k])];
                        ];
                    ];
                ];
            ];
        ]; 
        (*
        ... 
        *)
    ]; (*end if OPT *)

 If[int === Null, 
 If[Length[I1]>0,  
    pIinv = GetPermutations[I2,I1];
    pJ    = GetPermutations[J1,J2];     
    int = Sum[ 
            perm = PermutationList[PermutationProduct[pJ[[j]],pIinv[[i]]],Length[I1]];
            type = PermutationTypePartition[perm];
            Weingarten[type,dim]
            ,{i,1,Length[pIinv]},{j,1,Length[pJ]}
          ];
     (*
    Block[{n,A,rules,ss},
    n = Length[I1];    
    A=SparseArray[{},ConstantArray[1+n,n]];
      Do[
        perm = PermutationList[PermutationProduct[pJ[[j]],pIinv[[i]]],n];
        type = PermutationTypePartition[perm];
        type = Join[type+1, ConstantArray[1,n-Length[type]]];
        (A[[##]]++&@@ type) ;
        ,{i,1,Length[pIinv]},{j,1,Length[pJ]}];
    rules = ArrayRules[A];
    ss = Sum[
        type = Select[rules[[i]][[1]]-1, #>0&];    
        Weingarten[type,dim] * rules[[i]][[2]]
        ,{i,1,Length[rules]-1}];
    int=ss;
    ]; (*end block*)
    *)
    , int = 0;];];
 (*return*)
 int
 ];
 Protect[IntegrateUnitaryHaarIndices];
 (*return*) 
 IntegrateUnitaryHaarIndices[{I1,J1,I2,J2}, dim] 
 ,
 0
 ]
 
);

(*
 Extracts indices from expresion w and puts them into 4 lists I1,J1,I2,J2 see \cite[Eqn. 11]{collins06integration}.
*)
IndexExtractor[w_]:=Block[{fw,con,ccon, rest, I1, I2, J1,J2}, 

    fw=(Flatten[{w}//.{a_*b_-> {a,b},Conjugate[a_*b_]->{Conjugate[a],Conjugate[b]},Conjugate[a_^k_]:> ConstantArray[Conjugate[a],k],a_^k_ :>  ConstantArray[a,k]}]); 
    con = Select[fw,Head[#]===Conjugate &];  
    ccon=Conjugate[con]; 
    rest=Select[fw,Head[#]=!=Conjugate &];

(*    fw=(Flatten[{w}//.{a_*b_-> {a,b},CON[a_*b_]->{CON[a],CON[b]},CON[a_^k_]:> ConstantArray[CON[a],k],a_^k_ :>  ConstantArray[a,k]}]); 
    con = Select[fw,Head[#]===CON &];  
    ccon=CON[con]; 
    rest=Select[fw,Head[#]=!=CON &];
*)
    I1={};I2={};J1={};J2={};
    If[Length[rest]==Length[con],
        (AppendTo[I1,#[[2]]];AppendTo[J1,#[[3]]];)& /@ rest;
        (AppendTo[I2,#[[2]]];AppendTo[J2,#[[3]]];)& /@ ccon;                
        {I1,J1,I2,J2} = NormIdx[I1,J1,I2,J2];
    ]; 
    (*return*) 
    {I1,J1,I2,J2}
]

(*
Function normalizes indices, so that only first positive numbers are used
*)
NormIdx[i1_, j1_, i2_, j2_] := 
  Block[{Is1, Js1, Is2, Js2, symbI1, restSymbI, symbJ1, restSymbJ, k, 
    symbolChange, symbolChangeJ, IIs1, IIs2, JJs1, JJs2}, {Is1, Js1} =
     Sort[{i1, j1}\[Transpose]]\[Transpose];
   {Is2, Js2} = Sort[{i2, j2}\[Transpose]]\[Transpose];
   symbI1 = Union[Is1];
   restSymbI = Complement[Is2, symbI1];
   symbJ1 = DeleteDuplicates[Js1];
   restSymbJ = Complement[Js2, symbJ1];
   k = 0; 
   symbolChange = 
    Join[Table[k++; symbI1[[i]] -> k, {i, 1, Length[symbI1]}], 
     Table[k++; restSymbI[[i]] -> k, {i, 1, Length[restSymbI]}]];
   k = 0;
   symbolChangeJ = 
    Join[Table[k++; symbJ1[[i]] -> k, {i, 1, Length[symbJ1]}], 
     Table[k++; restSymbJ[[i]] -> k, {i, 1, Length[restSymbJ]}]];
   IIs1 = Is1 /. symbolChange;
   IIs2 = Is2 /. symbolChange;
   JJs1 = Js1 /. symbolChangeJ;
   JJs2 = Js2 /. symbolChangeJ;
   (*return*){IIs1, JJs1, IIs2, JJs2}
];
(*
NormIdx[i1_,j1_,i2_,j2_]:=Block[{Is1,Js1,Is2,Js2, symbI1, restSymb,k,symbolChange},
    {Is1,Js1}=Sort[{i1,j1}\[Transpose]]\[Transpose];
    {Is2,Js2}=Sort[{i2,j2}\[Transpose]]\[Transpose];
    symbI1=Union[Is1];
    restSymb=Complement[Union[Join[Js1,Is2,Js2]],symbI1];
    k=0; symbolChange=Join[Table[k++;symbI1[[i]]->k ,{i,1,Length[symbI1]}],Table[k++;restSymb[[i]]->k ,{i,1,Length[restSymb]}]];
    (*return*)  
    {Is1,Js1,Is2,Js2}/.symbolChange
];
*)

(*
Integrating function - this function calls multiple times IntU 
*)
IntegrateUnitaryHaar[integrand_, list__] := Fold[ IntU[#1,#2[[1]],#2[[2]]]& , integrand, {list}] 

(*
 Main function which performs integration
*)

IntU[integrand_, variable_, dim_?PositiveIntegerQ ] := Block[{freeFromVariable,integrandExpanded,f,g,expList,tempVar,NPI,isPoly,currVar,restVar,CON},	
    (*Print[StringJoin["Optimalization = ", ToString[OPT]] ];*)
    freeFromVariable[a_, b_] := If[FreeQ[a, variable] || FreeQ[b, variable], a + b, {a, b}];
    (*freeFromVariable[a_, b_] := If[False (*FreeQ[a, variable] || FreeQ[b, variable]*), a + b, {a, b}];*)

   	If[Not[FreeQ[integrand,variable]],
        integrandExpanded = ExpandAll[integrand];
        
	(*
	integrandExpanded = integrandExpanded //. Abs[x_]^(p_?EvenQ) :> ExpandAll[ExpandAll[x^(p/2)]*Conjugate[(ExpandAll[x^(p/2)])]];
        integrandExpanded = integrandExpanded //. Conjugate[x_]^(p_) :> Conjugate[ExpandAll[x^p]];
        integrandExpanded = ExpandAll[integrandExpanded //. { Conjugate[x_ + y_] :> Conjugate[x] + Conjugate[y], Conjugate[x_*y_] :> Conjugate[x]*Conjugate[y]}];
        *)
        
	(*
	integrandExpanded = ExpandAll[integrandExpanded //. {Abs[x_]^(p_?EvenQ) :> ExpandAll[ExpandAll[x^(p/2)]*Conjugate[ExpandAll[x^(p/2)]]],
			      Conjugate[x_]^(p_) :> Conjugate[ExpandAll[x^p]],
			      Conjugate[x_ + y_] :> Conjugate[x] + Conjugate[y], Conjugate[x_*y_] :> Conjugate[x]*Conjugate[y]}];
	*)
		
	integrandExpanded = ExpandAll[integrandExpanded //. {Abs[x_]^(p_?EvenQ) :> ExpandAll[ExpandAll[x^(p/2)]*CON[ExpandAll[x^(p/2)]]],
			      Conjugate[x_]^(p_) :> CON[ExpandAll[x^p]],
			      Conjugate[x_ + y_] :> CON[x] + CON[y], CON[x_*y_] :> CON[x]*CON[y],
			      Conjugate[x_]:>CON[x]}];
	integrandExpanded = ExpandAll[integrandExpanded //. {CON[x_]^(p_) :> CON[ExpandAll[x^p]],
			      CON[x_ + y_] :> CON[x] + CON[y], CON[x_*y_] :> CON[x]*CON[y]}];
	
	integrandExpanded = integrandExpanded/.CON[x_]->Conjugate[x];
		
	
	If[Head[integrandExpanded] === Plus,
	  expList= List@@integrandExpanded;,
	  expList= {integrandExpanded};
	];
	expList = expList/.Conjugate[x_*y_]-> Conjugate[x]*Conjugate[y];
        
        
        (*
        expList =(Flatten[{integrandExpanded}//.a_+b_:>freeFromVariable[a,b]]);
        expList = expList/.Abs[x_]^k_?EvenQ-> x^(k/2)*Conjugate[(x^(k/2))];
        expList = expList/.Conjugate[x_*y_]-> Conjugate[x]*Conjugate[y];
        *)
                
	(*
        f=Function[{x,var},Block[{const},( const= x/.{Subscript[var, p_,q_]-> 1};{
	    const*IntegrateUnitaryHaarIndices[IndexExtractor[x/.const-> 1],dim]
	    })]];
	*)
        
        f=Function[{x,var},Block[{const,y},( const= x/.{Subscript[var, p_,q_]-> 1};{
	      y=x/const;
	      If[const===0,0, const*IntegrateUnitaryHaarIndices[IndexExtractor[y],dim]]
	  })]];
        
        g=Function[{x,var}, Block[{},
	    If[FreeQ[x,variable], 
	      x,
	      (*else*)
	      If[x =!= 0,       
		isPoly = True;
		isPoly = ((x/.Subscript[var, __]^k_?NotPositiveIntegerQ-> NPI)/.NPI->0)=!=0;      
		isPoly = And[isPoly,PolynomialQ[x /.{Subscript[var, __]-> tempVar, Conjugate[Subscript[var, __]]-> tempVar },tempVar]];
		
		(* Miejsce do optymalizacji*)  
		l=  {};
		x/.Subscript[var, i_,j_]:> (AppendTo[l,{i,j}];) ;
		ul=Union[l];
		If[isPoly, Do[isPoly = isPoly && PolynomialQ[x/.{Subscript[var, ul[[i]][[1]],ul[[i]][[2]]]->currVar,Subscript[var, __]-> restVar},{currVar,Conjugate[currVar]}]; If[!test,Break[]],{i,1,Length[ul]}]];     
		If[isPoly,           
		    f[x,var]
		, (*else*)       
		  HoldForm[IntegrateUnitaryHaar[x,{var,dim}]]
		]
	      ,(*else*)
	      0
	      ]
	    ]
	    ]
        ];
        Total[Flatten[ g[#,variable]&/@expList]]
    ,(*else*)
        integrand	          
    ]
];
SetAttributes[IntU,Listable];


(* ::Section::Closed:: *)
(*Package footer*)


Print["Package IntU version ", IntU`Private`intuVersion, " (last modification: ", IntU`Private`intuLastModification, ")."];

End[];

Protect@@Names["IntU`*"]

EndPackage[];
