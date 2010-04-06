(* ::Package:: *)

NumericQ[Global`\[HBar]] := True;

(* Basic fields *)
\[CapitalPhi]f = Field[Global`\[CapitalPhi], {}, {a}];
Sf = Field[Global`S, {a}, {}];

Grading[Field[Global`\[CapitalPhi], ___]] := 0;
Grading[Field[Global`S, ___]] := 1;

(*Components*)
DefineComponents[Global`S,Global`b,Global`\[Beta]];
DefineComponents[Global`\[CapitalPhi],Global`\[Gamma],Global`c];

\[Beta]f= Field[Global`\[Beta],{a},{}];
\[Gamma]f= Field[Global`\[Gamma],{},{a}];
bf= Field[Global`b,{a},{}];
cf= Field[Global`c,{},{a}];


LambdaBracket[ Field[Global`S, ___], Field[Global`S, ___]] := 0; 

CoordinateFunctionQ[Global`\[CapitalPhi]]:=True;
Field[Global`\[CapitalPhi],{},{a_},{b_}]:= Field[Global`\[Delta], {b}, {a}];



(* Basic component brackets *)
LambdaBracket[ Field[\[Beta],___],Field[\[Beta],___]] := 0 ; 
LambdaBracket[ Field[\[Gamma],___],Field[\[Gamma],___]] := 0 ; 
LambdaBracket[ Field[\[Beta],{a_},{},{}],Field[\[Gamma],{},{b_},{}]] :=\[HBar]*Field[\[Delta],{a},{b},{}] ; 
LambdaBracket[ Field[\[Gamma],{},{a_},{}],Field[\[Beta],{b_},{},{}]] :=LambdaBracketChangeOrder[ Field[\[Gamma],{},{a},{}],Field[\[Beta],{b},{},{}]] ; 

LambdaBracket[ Field[b,___],Field[b,___]] := 0 ; 
LambdaBracket[ Field[c,___],Field[c,___]] := 0 ; 
LambdaBracket[ Field[b,{i_},{},{}],Field[c,{},{j_},{}]] :=\[HBar]*Field[\[Delta],{i},{j},{}] ; 
LambdaBracket[ Field[c,{},{i_},{}],Field[b,{j_},{},{}]] :=LambdaBracketChangeOrder[ Field[c,{},{i},{}],Field[b,{j},{},{}]]; 

LambdaBracket[ Field[\[Beta],___],Field[b,___]] := 0 ; 
LambdaBracket[ Field[\[Beta],___],Field[c,___]] := 0 ; 
LambdaBracket[ Field[b,___],Field[\[Beta],___]] := 0 ; 
LambdaBracket[ Field[c,___],Field[\[Beta],___]] := 0 ; 

LambdaBracket[ Field[\[Gamma],___],Field[b,___]] := 0 ; 
LambdaBracket[ Field[\[Gamma],___],Field[c,___]] := 0 ; 
LambdaBracket[ Field[b,___],Field[\[Gamma],___]] := 0 ; 
LambdaBracket[ Field[c,___],Field[\[Gamma],___]] := 0 ; 

LambdaBracket[ Field[\[Gamma],___],Field[f_,___]] := 0 ; /;CoordinateFunctionQ[f]; 
LambdaBracket[ Field[f_,___],Field[\[Gamma],___]] := 0 ; /;CoordinateFunctionQ[f]; 

LambdaBracket[ Field[c,___],Field[f_,___]] := 0 ; /;CoordinateFunctionQ[f]; 
LambdaBracket[ Field[f_,___],Field[c,___]] := 0 ; /;CoordinateFunctionQ[f]; 

LambdaBracket[ Field[b,___],Field[f_,___]] := 0 ; /;CoordinateFunctionQ[f]; 
LambdaBracket[ Field[f_,___],Field[b,___]] := 0 ; /;CoordinateFunctionQ[f]; 

LambdaBracket[ Field[f_,{down___},{up___},{deriv___}],Field[Global`\[Beta],{a_},{},{}]] :=Global`\[HBar]*Field[f,{down},{up},{a,deriv}] /;CoordinateFunctionQ[f];
LambdaBracket[ Field[Global`\[Beta],{a_},{},{}],Field[f_,{down___},{up___},{deriv___}]] :=Global`\[HBar]*Field[f,{down},{up},{a,deriv}] /;CoordinateFunctionQ[f];




(*Rules for functions that only depend on \[CapitalPhi]*)
CoordinateFunctionQ[_]:=False;
LambdaBracket[ Field[f_,{down___},{up___},{deriv___}],Field[Global`S,{a_},{},{}]] :=Global`\[HBar]*Field[f,{down},{up},{a,deriv}] /;CoordinateFunctionQ[f];
LambdaBracket[ Field[Global`S,{a_},{},{}],Field[f_,{down___},{up___},{deriv___}]] :=Global`\[HBar]*Field[f,{down},{up},{a,deriv}] /;CoordinateFunctionQ[f];
LambdaBracket[ Field[f_,___],Field[h_,___]] := 0 /;CoordinateFunctionQ[f]&&CoordinateFunctionQ[h]; 
LambdaBracket[ Field[f_,___],Field[Global`\[CapitalPhi],___]] := 0 /;CoordinateFunctionQ[f]; 
LambdaBracket[ Field[Global`\[CapitalPhi],___],Field[f_,___]] := 0 /;CoordinateFunctionQ[f]; 

NormalOrder[SD[Field[Global`\[CapitalPhi],{},{a_},{}]], Field[f_,{down___},{up___},deriv_]]:=SD[Field[f,{down},{up},Delete[deriv,Position[deriv,a]]]]/;MemberQ[deriv,a]&&CoordinateFunctionQ[f];
NormalOrder[TD[Field[Global`\[CapitalPhi],{},{a_},{}]], Field[f_,{down___},{up___},deriv_]]:=TD[Field[f,{down},{up},Delete[deriv,Position[deriv,a]]]]/;MemberQ[deriv,a]&&CoordinateFunctionQ[f];

NormalOrder[Field[f_,{down___},{up___},deriv_],SD[Field[Global`\[CapitalPhi],{},{a_},{}]]]:=SD[Field[f,{down},{up},Delete[deriv,Position[deriv,a]]]]/;MemberQ[deriv,a]&&CoordinateFunctionQ[f];
NormalOrder[Field[f_,{down___},{up___},deriv_],TD[Field[Global`\[CapitalPhi],{},{a_},{}]]]:=TD[Field[f,{down},{up},Delete[deriv,Position[deriv,a]]]]/;MemberQ[deriv,a]&&CoordinateFunctionQ[f];

(*When actong with the odd derivative on f, we get two derivatives on f, contracted with antisymmetric*)
NormalOrder[SD[Field[Global`\[CapitalPhi],{},{a_},{}]], SD[Field[f_,_List,_List,deriv_]]]:=0/;CoordinateFunctionQ[f]&&MemberQ[deriv,a];
NormalOrder[SD[Field[f_,_List,_List,deriv_]],SD[Field[Global`\[CapitalPhi],{},{a_},{}]]]:=0/;CoordinateFunctionQ[f]&&MemberQ[deriv,a];








(*Expansion of coordinate functions*)
ExpandSuperFields[expr:Field[f_Symbol ,downindices_List, upindices_List,{deriv___}]]:=Module[{derivind=Unique[a]},
{
{expr,Grading[expr]},
{MDIC[NormalOrder[Field[f ,downindices, upindices,{deriv,derivind}],ExpandSuperFields[Field[Global`\[CapitalPhi],{},{derivind},{}]][[2]][[1]] ]] ,Mod[Grading[expr]+1,2]}
}]/;CoordinateFunctionQ[f]&&f=!=\[CapitalPhi]; 

