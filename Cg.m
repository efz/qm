(* ::Package:: *)

BeginPackage["Cg`"]


Cg::usage ="Use as CgCoeff,CgExpandVec";


CgCoeff[j1_,j2_,J_,m1_,m2_] := Subscript[Cg, j1,j2][J,m1,m2]


CgExpandVec[j1_,j2_,J_,M_] :=Subscript[\[CapitalPsi], j1,j2][J,M]


Subscript[Cg, j1_,j2_][J_,m1_,m2_]:=Subscript[\[Psi], j1,j2][m1,m2]  Subscript[\[CapitalPsi], j1,j2][J,m1+m2] //Simplify


Begin["`Private`"]


(* ::Input::Initialization:: *)
Subscript[\[Psi], j1_,j2_][m1_,m2_]  Subscript[\[Psi], j3_,j4_][m3_,m4_]   ^:= 0 /; j1 != j3 || j2 != j4 || m1 != m3 || m2 != m4


(* ::Input::Initialization:: *)
Subscript[\[Psi], j1_,j2_][m1_,m2_]  Subscript[\[Psi], j3_,j4_][m3_,m4_] ^:= 1/; j1 == j3 || j2 == j4 || m1 == m3 || m2 == m4


(* ::Input::Initialization:: *)
Power[Subscript[\[Psi], j1_,j2_][m1_,m2_],p_]   ^:= 1 /;p==2


(* ::Input::Initialization:: *)
Subscript[\[CapitalPsi], j1_,j2_][J_,M_] := Subscript[\[Psi], j1,j2][j1,j2] /; J== j1+j2 && M == J


(* ::Input::Initialization:: *)
Subscript[\[CapitalPsi], j1_,j2_][J_,M_]:= Subscript[\[Psi], j1,j2][-j1,-j2] /; J== j1+j2 && -M == J


(* ::Input::Initialization:: *)
Subscript[\[CapitalPsi], j1_,j2_][J_,M_]:=LowerM[Subscript[dummy\[CapitalPsi], j1,j2][J, M+1]] /; M+1 <=J && J<= j1+j2
Subscript[\[CapitalPsi], j1_,j2_][J_,M_]:= LowerJ[Subscript[dummy\[CapitalPsi], j1,j2][J+1, M]] /; M ==J && J+1<= j1+j2


(* ::Input::Initialization:: *)
LowerM[Subscript[dummy\[CapitalPsi], j1_,j2_][J_,M_]]/; Abs[M-1] <= J:= 1/Sqrt[J(J+1) -M^2 +M] Lowerm1m2[Subscript[\[CapitalPsi], j1,j2][J,M]]  //Simplify//Expand


(* ::Input::Initialization:: *)
Lowerm1m2[Subscript[\[Psi], j1_,j2_][m1_,m2_]] := Lowerm1[Subscript[\[Psi], j1,j2][m1,m2]] + Lowerm2[Subscript[\[Psi], j1,j2][m1,m2]] /;m1+m2> -j2-j2


(* ::Input::Initialization:: *)
Lowerm1m2[coef_ Subscript[\[Psi], j1_,j2_][arg__]]:=coef Lowerm1m2[Subscript[\[Psi], j1,j2][arg]]


(* ::Input::Initialization:: *)
Lowerm1m2[expr1_+expr2_]:= Lowerm1m2[expr1] +Lowerm1m2[expr2]


(* ::Input::Initialization:: *)
Lowerm1[coef_ Subscript[\[Psi], j1_,j2_][arg__]]:=coef Lowerm1[Subscript[\[Psi], j1,j2][arg]]


(* ::Input::Initialization:: *)
Lowerm2[coef_ Subscript[\[Psi], j1_,j2_][arg__]]:=coef Lowerm2[Subscript[\[Psi], j1,j2][arg]]


(* ::Input::Initialization:: *)
Lowerm1[expr1_+expr2_]:= Lowerm1[expr1] +Lowerm1[expr2]


(* ::Input::Initialization:: *)
Lowerm2[expr1_+expr2_]:= Lowerm2[expr1] +Lowerm2[expr2]


(* ::Input::Initialization:: *)
Lowerm1[Subscript[\[Psi], j1_,j2_][ m1_, m2_]] :=Sqrt[ j1(j1+1)-m1^2+m1] Subscript[\[Psi], j1,j2][m1-1, m2] /; Abs[m1-1] <=j1


(* ::Input::Initialization:: *)
Lowerm2[Subscript[\[Psi], j1_,j2_][m1_, m2_]] := Sqrt[j2(j2+1)-m2^2+m2]  Subscript[\[Psi], j1,j2][ m1, m2-1] /; Abs[m2-1] <=j2


(* ::Input::Initialization:: *)
Lowerm1[Subscript[\[Psi], j1_,j2_][ m1_, m2_]] := 0/; Abs[m1-1] > j1


(* ::Input::Initialization:: *)
Lowerm2[Subscript[\[Psi], j1_,j2_][ m1_, m2_]] := 0/; Abs[m2-1] > j2


(* ::Input::Initialization:: *)
CgExpand[Subscript[dummy\[CapitalPsi], j1_,j2_][J_,M_]] := Sum[Subscript[dummyCg, j1,j2][J,m1,M-m1] Subscript[\[Psi], j1,j2][m1,M-m1], {m1, Max[-j1, M-j2],Min[j1, M+j2]}] /; Abs[M] <=J


(* ::Input::Initialization:: *)
Cgs[Subscript[dummy\[CapitalPsi], j1_,j2_][J_,M_]] := Table[Subscript[dummyCg, j1,j2][J,m1,M-m1] , {m1, Max[-j1, M-j2],Min[j1, M+j2]}] /; Abs[M] <=J


(* ::Input::Initialization:: *)
CgEq[Subscript[dummyCg, j1_,j2_][J_,m1_,m2_]] := Subscript[dummyCg, j1,j2][J,m1,m2]^2 + Sum[Subscript[Cg, j1,j2][j,m1,m2]^2,{j,J+1, j1+j2}]==1


(* ::Input::Initialization:: *)
SetAttributes[CgEq, Listable]


(* ::Input::Initialization:: *)
OrthEqs[Subscript[dummy\[CapitalPsi], j1_,j2_][J_,M_]] := Table[((CgExpand[Subscript[dummy\[CapitalPsi], j1,j2][J,M]]  Subscript[\[CapitalPsi], j1,j2][j,M] //Simplify)/.Subscript[\[Psi], _,_][args__]^2->1)==0,{j,J+1, j1+j2}]


(* ::Input::Initialization:: *)
SetAttributes[OrthEqs, Listable]


(* ::Input::Initialization:: *)
CalcCgs[Subscript[dummy\[CapitalPsi], j1_,j2_][J_,M_]] := {Solve[Join[CgEq[Cgs[Subscript[dummy\[CapitalPsi], j1,j2][J,M]]], OrthEqs[Subscript[dummy\[CapitalPsi], j1,j2][J,M]]]//Flatten, Cgs[Subscript[dummy\[CapitalPsi], j1,j2][J,M]]][[1]]}//Flatten


(* ::Input::Initialization:: *)
LowerJ[Subscript[dummy\[CapitalPsi], j1__,j2_][J_,M_]] /;J > Abs[j1-j2] && Abs[M]==J-1:= CgExpand[Subscript[dummy\[CapitalPsi], j1,j2][J-1,M]]/.CalcCgs[Subscript[dummy\[CapitalPsi], j1,j2][J-1,M]] //Simplify//Expand


Protect[Cg]
Protect[CgExpandVec]
Protect[\[CapitalPsi]]


End[]
EndPackage[]
