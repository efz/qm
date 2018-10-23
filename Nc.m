(* ::Package:: *)

(* ::Input::Initialization:: *)
BeginPackage["Nc`"]


Nc::usage ="Use as Nc[a,b] , Nc[a**b] , nc[a,b,c]";


Cmi[\[HBar]]= 0


Cmi[a_]:= 0 /; NumberQ[a]


Cmi[a_,b_]:= 0 /; Cm[a] == 0 && Cm[b] == 0


Cmi[Power[a_,n_]]:= 0 /; Cm[a] == 0 && Cm[n] == 0


Cmi[Power[a_,n_Integer], b_]:= 0 /; Cm[a,b] == 0 || Cm[b,a] == 0


Cmi[a, Power[b_,n_Integer]]:= 0 /; Cm[a,b] == 0 || Cm[b,a] == 0


Cm[a__]:= If[ValueQ[Cmu[a]], Cmu[a], Cmi[a]] /; ValueQ[Cmu[a]] || ValueQ[Cmi[a]]


SetAttributes[Cmi, Protected]


SetAttributes[Cm, Protected]


Nc2Star[a_]:= a //.Nc[b_,c_]-> b**c


SetAttributes[Nc2Star,Protected]


Begin["`Private`"]


Nc[a_,b_,c_] := Nc[a, Nc[b,c]] 


Nc[a_+b_]:= Nc[a] + Nc[b]


Nc[a_ - b_]:=Nc[a] - Nc[b]


Nc[a_ ** b_]:= Nc[a, b]


Nc[-a_] := -Nc[a]


Nc[a_/b_]:= Nc[a, 1/b]


Nc[a_ b_]:= Nc[a, b]


Nc[a_/b_]:= a/b /; Cm[a] == 0 && Cm[b]==0


(* ::Input::Initialization:: *)
Nc[a_,b_ + c_] := Nc[a,b]+ Nc[a,c]
Nc[a_,b_ - c_] := Nc[a,b]-Nc[a,c]


(* ::Input::Initialization:: *)
Nc[b_ + c_,a_] := Nc[b,a]+Nc[c,a]


(* ::Input::Initialization:: *)
Nc[b_ - c_,a_] := Nc[b,a]-Nc[c,a]


Nc[a_, b_ ** c_] := Nc[a, Nc[b ,c]]


Nc[ a_ ** b_, c_] := Nc[Nc[a ,b], c]


(* ::Input::Initialization:: *)
Nc[a_,b_]:= a b/;Cm[a,b]==0||Cm[b,a]==0


Nc[a_,b_]:= Nc[a] b/;Cm[b]== 0


Nc[a_,b_]:= Nc[b] a/;Cm[a]== 0


(* ::Input::Initialization:: *)
Nc[-a_,b_]:= -Nc[a,b]


(* ::Input::Initialization:: *)
Nc[a_,-b_]:= -Nc[a,b]


(* ::Input::Initialization:: *)
Nc[a_*b_, c_]:= a Nc[b,c]/;Cm[a] == 0


(* ::Input::Initialization:: *)
Nc[a_*b_, c_]:= b Nc[a,c]/;Cm[b] == 0


(* ::Input::Initialization:: *)
Nc[a_,b_*c_]:= b Nc[a,c]/;Cm[b] == 0


(* ::Input::Initialization:: *)
Nc[a_,b_*c_]:= c Nc[a,b]/;Cm[c] == 0


(* ::Input::Initialization:: *)
Nc[l_List,b_]:= l*b/;Cm[b] == 0


(* ::Input::Initialization:: *)
Nc[l_List,b_]:= Table[Nc[l[[i]] ,b],{i,1,Length[l]}]


Nc[a_,l_List]:= a*l/;Cm[a] == 0


Nc[a_,l_List]:= Table[Nc[a,l[[i]]],{i,1,Length[l]}]


Nc[a_]:= a /;Head[a] === Symbol || Cm[a] ==0


Nc[a_/b_, c_]:= Nc[a, c]/b /;Cm[b] == 0


Nc[a_, b_/c_]:= Nc[a, b]/c /;Cm[c] == 0


Nc[Nc[a__]]:=Nc[a]


Nc[l_List]:=l


Nc[Power[a_,n_Integer], b_]:= Nc[b, Power[a,n]]/;(ValueQ[Cm[a,b]] || ValueQ[Cm[b,a]])&& BooleanQ[Cm[a,b] == 0]|| BooleanQ[Cm[b,a] == 0]


Nc[Power[a_,n_Integer], b_]:= Nc[Power[a,n - 1], Nc[b, a] + Cm[a,b]]/; ValueQ[Cm[a,b]] && n>1 && !BooleanQ[Cm[a,b] ==0]


Nc[a_, Power[b_,n_Integer]]:= Nc[Nc[b, a] + Cm[a,b], Power[b,n-1]]/; ValueQ[Cm[a,b]] && n>1 && !BooleanQ[Cm[a,b] ==0]


Nc[Power[a_,n_Integer],b_]:=Hold[Nc[Power[a,n],b]] /;ValueQ[Cm[a,b]] && ValueQ[Cm[b,a]]


Nc[a_,Power[b_,n_Integer]]:=Hold[Nc[a, Power[b,n]]] /;ValueQ[Cm[a,b]] && ValueQ[Cm[b,a]]


Nc[Power[a_,n1_Integer],Power[b_,n2_Integer]]:=Hold[Nc[Power[a, n1], Power[b,n2]]] /;ValueQ[Cm[a,b]] && ValueQ[Cm[b,a]]


Nc[a_,b_]:=Hold[Nc[a,b]] /;ValueQ[Cm[a,b]] && ValueQ[Cm[b,a]]


Nc[a_,b_] := Nc[b, a] + Cm[a,b] /; ValueQ[Cm[a,b]] && !BooleanQ[Cm[a,b] ==0]


Nc[Nc[a_,b_],c_]:= Nc[a, Nc[b,c]]


Nc[a_,Nc[a_,b_]]:=Nc[a a, b]


(* ::Text::Initialization:: *)
(*(*************************************************)*)


SetAttributes[Nc,Protected]


SetAttributes[Nc2Star,Protected]


End[]


(* ::Input::Initialization:: *)
EndPackage[]
