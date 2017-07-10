
let test_problems =
  [ 
"
%--------------------------------------------------------------------------
% File     :  1-bit-adder
% Domain   : Hardware Verification
% Problem  : See Section 6 in [Gordon91]
% Version  : 
% English  : Specification, Representation of Implementation, and Verification of a 1-bit CMOS full adder
% Refs     : [Gordon91]
% Source   : Formalization by C. Benzmueller following {Gordon91]
% Names    : ???
% Status   : Theorem
% Rating   : ???
% Syntax   : ???
% Comments : Not solvable fully automatically in LEO and METIS.
%--------------------------------------------------------------------------

      thf(times_const,constant,(times : $i -> ($i -> $i))).

      thf(plus_const,constant,(plus : $i -> ($i -> $i))). 

      thf(zero_const,constant,(zero : $i)). 

      thf(one_const,constant,(one : $i)).  
     
      thf(two_const,constant,(two : $i)).  

      thf(three_const,constant,(three : $i)).  

      thf(bit_val_const,constant,(bit_val : $o -> $i)).  

      thf(bit_val,axiom,(((bit_val @ $true) = one) & ((bit_val @ $false) = zero))).  

      thf(times,axiom,((((times @ two) @ zero) = zero) & (((times @ two) @ one) = two))).

      thf(plus,axiom,(
    (((plus @ zero) @ zero) = zero) & 
    (((plus @ one) @ zero) = one) &
    (((plus @ zero) @ one) = one) & 
    (((plus @ one) @ one) = two) & 
    (((plus @ zero) @ two) = two) & 
    (((plus @ one) @ two) = three) & 
    (((plus @ two) @ zero) = two) & 
    (((plus @ two) @ one) = three))).

      thf(pwr_def,definition,(pwr := (^ [P: $o] : (P = $true)))). 

      thf(gnd_def,definition,(gnd := (^ [P: $o] : (P = $false)))). 

      thf(ptran_def,definition,(ptran := (^ [G:$o, A:$o, B:$o] : (G => (A = B))))). 

      thf(ntran_def,definition,(ntran := (^ [G:$o, A:$o, B:$o] : ((~ G) => (A = B))))). 

      % I changed the last application from 'bit_val @ C' to 'bit_val @ CIN' because 'C' was not bound --Arnaud 23.03.07
      thf(add1_spec_def,definition,(add1_spec := (^ [A:$o, B:$o, CIN:$o, SUM:$o, COUT:$o] : (((plus @ ((times @ two) @ (bit_val @ COUT))) @ (bit_val @ SUM)) = ((plus @ (bit_val @ A)) @ ((plus @ (bit_val @ B)) @ (bit_val @ CIN))))))). 

      % I changed the variable occurences in the term to uppercase --Arnaud 23.03.07
      thf(add1_impl_def,definition,(add1_impl := (^ [A:$o, B:$o, CIN:$o, SUM:$o, COUT:$o] : (? [P0:$o, P1:$o, P2:$o, P3:$o, P4:$o, P5:$o, P6:$o, P7:$o, P8:$o, P9:$o, P10:$o, P11:$o] : 
         (
            (((ptran @ P1) @ P0) @ P2)   & 
            (((ptran @ CIN) @ P0) @ P3)  & 
            (((ptran @ B) @ P2) @ P3)    & 
            (((ptran @ A) @ P2) @ P4)    & 
            (((ptran @ P1) @ P3) @ P4)   & 
            (((ntran @ A) @ P4) @ P5)    & 
            (((ntran @ P1) @ P4) @ P6)   & 
            (((ntran @ B) @ P5) @ P6)    & 
            (((ntran @ P1) @ P5) @ P11)  & 
            (((ntran @ CIN) @ P6) @ P11) & 
            (((ptran @ A) @ P0) @ P7)    & 
            (((ptran @ B) @ P0) @ P7)    & 
            (((ptran @ A) @ P0) @ P8)    & 
            (((ptran @ CIN) @ P7) @ P1)  & 
            (((ptran @ B) @ P8) @ P1)    & 
            (((ntran @ CIN) @ P1) @ P9)  & 
            (((ntran @ B) @ P1) @ P10)   & 
            (((ntran @ A) @ P9) @ P11)   & 
            (((ntran @ B) @ P9) @ P11)   & 
            (((ntran @ A) @ P10) @ P11)  & 
            (pwr @ P0)                   & 
            (((ptran @ P4) @ P0) @ SUM)  & 
            (((ntran @ P4) @ SUM) @ P11) & 
            (gnd @ P11)                  & 
            (((ptran @ P1) @ P0) @ COUT) & 
            (((ntran @ P1) @ COUT) @ P11)
      ))))).

      thf(verify_1_bit_adder,theorem,(! [A:$o, B:$o, CIN:$o, SUM:$o, COUT:$o] : (((((add1_impl @ A) @ B) @ CIN) @ SUM) @ COUT) => (((((add1_spec @ A) @ B) @ CIN) @ SUM) @ COUT))).
"
      ;
"
%--------------------------------------------------------------------------
% File     :  BB-1
% Domain   : Test Problems for Henkin Semantics
% Problem  : See [BB05], Problem ???
% Version  : 
% English  : 
% Refs     : [BB05] C.E. Benzmueller and C.E. Brown, In J. Hurd and T. Melham, A Structured Set of 
%               Higher-Order Problems, TPHOLs 2005, LNCS 3606, pp. 66-81, Springer, 2005.
% Source   : Formalization by C. Benzmueller following [BB05]
% Names    : 
% Status   : Theorem
% Rating   : 
% Syntax   : 
% Comments : 
%--------------------------------------------------------------------------

thf(a_const,constant,(a : $o)). 

thf(b_const,constant,(b : $o)). thf(p_const,constant,(p : $o -> $o)). 

thf(thm,theorem,(((p @ a) & (p @ b)) => (p @ (a & b)))).
"
      ;
"
%--------------------------------------------------------------------------
% File     : BB-2
% Domain   : Test Problems for Henkin Semantics
% Problem  : By C. Benzmueller
% Version  : Variation of BB-1 with functional extensionality
% English  : 
% Refs     : [BB05] C.E. Benzmueller and C.E. Brown, In J. Hurd and T. Melham, A Structured Set of 
%               Higher-Order Problems, TPHOLs 2005, LNCS 3606, pp. 66-81, Springer, 2005.
% Source   : Formalization by C. Benzmueller 
% Names    : 
% Status   : Theorem
% Rating   : 
% Syntax   : 
% Comments : 
%--------------------------------------------------------------------------

thf(a_const,constant,(a : $o)). 

thf(b_const,constant,(b : $o)). 

thf(p_const,constant,(p : ($i -> $o) -> $o)). 

thf(thm,theorem,(((p @ (^ [X: $i] : a)) & (p @ (^ [X: $i] : b))) => (p @ (^ [X: $i] : (a & b))))).
"
      ;
"
%--------------------------------------------------------------------------
% File     : SET171+3
% Domain   : Set Theory (Boolean properties)
% Problem  : Union distributes over intersection
% Version  : Encoding in Church's type theory by C. Benzmueller
% English  : Union distributes over intersection
% Refs     : [BSJK05] C. Benzmueller, V. Sorge, M. Jamnik, and M. Kerber, Can a Higher-Order and a 
%             First-Order Theorem Prover Cooperate? In F. Baader, A. Voronkov (eds.), Proceedings 
%             of the 11th International Conference on Logic for Programming Artificial Intelligence 
%             and Reasoning (LPAR), LNAI vol. 3452, pp. 415-431, Montevideo, Uruguay, 2005.  Springer.
%          : [BB05] C.E. Benzmueller and C.E. Brown, In J. Hurd and T. Melham, A Structured Set of 
%             Higher-Order Problems, TPHOLs 2005, LNCS 3606, pp. 66-81, Springer, 2005.
%          : [Try89] Trybulec (1989), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
% Source   : Formalization by C. Benzmueller following [BB05]
% Names    : 
% Status   : Theorem
% Rating   : v3.2.0
% Syntax   : 
% Comments : 
%--------------------------------------------------------------------------

thf(union_def,definition,(union := (^ [A: $i -> $o, B: $i -> $o] : ^ [X: $i] : (A @ X) | (B @ X)))).  

thf(intersection_def,definition,(intersection := (^ [A: $i -> $o, B: $i -> $o] : ^ [X: $i] : (A @ X) & (B @ X)))). 

thf(thm,theorem,(! [A: $i->$o, B: $i->$o, C: $i->$o] : ((union @ A) @ ((intersection @ B) @ C)) = ((intersection @ ((union @ A) @ B)) @ ((union @ A) @ C)))).
"
      ;
"
%--------------------------------------------------------------------------
% File     : SET607+3
% Domain   : Set Theory (Boolean properties)
% Problem  : 
% Version  : Encoding in Church's type theory by C. Benzmueller
% English  : 
% Refs     : [BSJK05] C. Benzmueller, V. Sorge, M. Jamnik, and M. Kerber, Can a Higher-Order and a 
%             First-Order Theorem Prover Cooperate? In F. Baader, A. Voronkov (eds.), Proceedings 
%             of the 11th International Conference on Logic for Programming Artificial Intelligence 
%             and Reasoning (LPAR), LNAI vol. 3452, pp. 415-431, Montevideo, Uruguay, 2005.  Springer.
%          : [BB05] C.E. Benzmueller and C.E. Brown, In J. Hurd and T. Melham, A Structured Set of 
%             Higher-Order Problems, TPHOLs 2005, LNCS 3606, pp. 66-81, Springer, 2005.
%          : [Try89] Trybulec (1989), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
% Source   : Formalization by C. Benzmueller following [BB05]
% Names    : 
% Status   : Theorem
% Rating   : 
% Syntax   : 
% Comments : 
%--------------------------------------------------------------------------

thf(union_def,definition,(union := (^ [A: $i -> $o, B: $i -> $o] : ^ [X: $i] : (A @ X) | (B @ X)))).  

thf(setminus_def,definition,(setminus := (^ [A: $i -> $o, B: $i -> $o] : ^ [X: $i] : (A @ X) & (~ (B @ X))))). 

thf(thm,theorem,(! [A: $i->$o, B: $i->$o] : ((union @ A) @ ((setminus @ B) @ A)) = ((union @ A) @ B))).
"
      ;
"
%--------------------------------------------------------------------------
% File     : SET609+3
% Domain   : Set Theory (Boolean properties)
% Problem  : 
% Version  : Encoding in Church's type theory by C. Benzmueller
% English  : 
% Refs     : [BSJK05] C. Benzmueller, V. Sorge, M. Jamnik, and M. Kerber, Can a Higher-Order and a 
%             First-Order Theorem Prover Cooperate? In F. Baader, A. Voronkov (eds.), Proceedings 
%             of the 11th International Conference on Logic for Programming Artificial Intelligence 
%             and Reasoning (LPAR), LNAI vol. 3452, pp. 415-431, Montevideo, Uruguay, 2005.  Springer.
%          : [BB05] C.E. Benzmueller and C.E. Brown, In J. Hurd and T. Melham, A Structured Set of 
%             Higher-Order Problems, TPHOLs 2005, LNCS 3606, pp. 66-81, Springer, 2005.
%          : [Try89] Trybulec (1989), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
% Source   : Formalization by C. Benzmueller following [BB05]
% Names    : 
% Status   : Theorem
% Rating   : 
% Syntax   : 
% Comments : 
%--------------------------------------------------------------------------

thf(union_def,definition,(union := (^ [A: $i -> $o, B: $i -> $o] : ^ [X: $i] : (A @ X) | (B @ X)))).  

thf(intersection_def,definition,(intersection := (^ [A: $i -> $o, B: $i -> $o] : ^ [X: $i] : (A @ X) & (B @ X)))). 

thf(setminus_def,definition,(setminus := (^ [A: $i -> $o, B: $i -> $o] : ^ [X: $i] : (A @ X) & (~ (B @ X))))). 

thf(thm,theorem,(! [A: $i->$o, B: $i->$o, C: $i->$o] : ((setminus @ A) @ ((setminus @ B) @ C)) = ((union @ ((setminus @ A) @ B)) @ ((intersection @ A) @ C)))).
"
      ;
"
%--------------------------------------------------------------------------
% File     : SET611+3
% Domain   : Set Theory (Boolean properties)
% Problem  : 
% Version  : Encoding in Church's type theory by C. Benzmueller
% English  : 
% Refs     : [BSJK05] C. Benzmueller, V. Sorge, M. Jamnik, and M. Kerber, Can a Higher-Order and a 
%             First-Order Theorem Prover Cooperate? In F. Baader, A. Voronkov (eds.), Proceedings 
%             of the 11th International Conference on Logic for Programming Artificial Intelligence 
%             and Reasoning (LPAR), LNAI vol. 3452, pp. 415-431, Montevideo, Uruguay, 2005.  Springer.
%          : [BB05] C.E. Benzmueller and C.E. Brown, In J. Hurd and T. Melham, A Structured Set of 
%             Higher-Order Problems, TPHOLs 2005, LNCS 3606, pp. 66-81, Springer, 2005.
%          : [Try89] Trybulec (1989), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
% Source   : Formalization by C. Benzmueller following [BB05]
% Names    : 
% Status   : Theorem
% Rating   : 
% Syntax   : 
% Comments : 
%--------------------------------------------------------------------------

thf(union_def,definition,(emptyset := (^ [X: $i] : false))).  

thf(intersection_def,definition,(intersection := (^ [A: $i -> $o, B: $i -> $o] : ^ [X: $i] : (A @ X) & (B @ X)))). 

thf(setminus_def,definition,(setminus := (^ [A: $i -> $o, B: $i -> $o] : ^ [X: $i] : (A @ X) & (~ (B @ X))))). 

thf(thm,theorem,(! [A: $i->$o, B: $i->$o] : (((intersection @ A) @ B) = emptyset) <=> ((setminus @ A) @ B) = A)).
"
      ;
"
thf(intersection_def,definition,(intersection := (^ [A: $i -> $o, B: $i -> $o] : ^ [X: $i] : (A @ X) & (B @ X)))). 
thf(thm,theorem,(! [A: $i->$o, B: $i->$o] : ((intersection @ A) @ B) = ((intersection @ B) @ A))).
"
      ;
    "thf(p_const,constant,(p : $o -> $o)). thf(a_const,constant,(a : $o)). thf(b_const,constant,(b : $o)). thf(thm,theorem,((~ (p @ (a | b))) | (p @ (b | a))))."
      ;
    "thf(p_const,constant,(p : $o -> $o)). thf(a_const,constant,(a : $o)). thf(b_const,constant,(b : $o)). thf(thm,theorem,((~(~((~(p @ a)) | (~(p @ b))))) | (p @ (~((~a) | (~b))))))."
      ;
 "thf(p_const,constant,(p : $o -> $o)). thf(a_const,constant,(a : $o)). thf(b_const,constant,(b : $o)). thf(thm,theorem,(a = b))."
      ;
 "thf(p_const,constant,(q : ($o -> $o) -> $o)). thf(m_const,constant,(m : $o -> $o)). thf(n_const,constant,(n : $o -> $o)). thf(thm,theorem,((q @ m) = (q @ n)))."
      ;
    "thf(a_const,constant,(a : $o)). thf(b_const,constant,(b : $o)). thf(c_const,constant,(c : $o)). thf(d_const,constant,(d : $o)). thf(e_const,constant,(e : $o)). thf(f_const,constant,(f : $o)). thf(thm,theorem,((~ (a | b | c | d) | ~ (e | f ))))."
      ;
    "thf(a_const,constant,(a : $i)). thf(thm,theorem,(~ ![X:$i -> $o]: (~ ![Y:$i -> $o]: ((~ (~ (X @ a))) | (~ (Y @ a))))))."
      ;
    "thf(a_const,constant,(a : $i)). thf(thm,theorem,(~ ![X:$i -> $o]: ![Y:$i -> $o]: ~ ((~ (~ (X @ a))) | (~ (Y @ a)))))."
      ;
    "thf(a_const,constant,(a : $o)). thf(b_const,constant,(b : $o)). thf(c_const,constant,(c :$o)). thf(thm,theorem,((~ (~ a)) | (~ b)))."
      ;
    "thf(a_const,constant,(a : $o)). thf(b_const,constant,(b : $o)). thf(c_const,constant,(c :$o)). thf(thm,theorem,(~ (~ a | ~ ((~ b) | ~ c))))."
      ;
    "thf(thm,theorem,(![X:$o,Y:$o,Z:$o]: ((X = Y) & ((Y) = Z)) => (X = Z)))."
      ;
    "thf(thm,theorem,(?[X:$o]: X))."
      ;
    "thf(a_const,constant,(a : $o)). thf(b_const,constant,(b : $o)). thf(p_const,constant,(p : $o -> $o)). thf(thm,theorem,(((p @ a) & (p @ b)) => (p @ (a & b))))."
      ;
    "thf(thm,theorem,(![O:$o,I:$o,J:$o]: (O = ~ (I & J)) => (?[H:$o]: ((H = (I & J)) & (O = ~ H)))))."
      ;
    "thf(transitive_def,definition,(transitive := ^ [A: $type] : (^ [X: (A > (A > $o))] : (! [U: A,Z: A,Y: A] : ((((X @ U) @ Z) & ((X @ Z) @ Y)) => ((X @ U) @ Y)))))). thf(thm,theorem,(![O:$o,I:$o,J:$o]: (O = ~ (I & J)) => (?[H:$o]: ((H = (I & J)) & (O = ~ H)))))." 
      ;
    "thf(a_const,constant,(a : $o)). thf(b_const,constant,(b : $o)). thf(thm,theorem,( (~ (a = (~ b))) | (~ (a = b)) ))."
      ;
    "thf(a_const,constant,(a : $o)). thf(b_const,constant,(b : $o)). thf(thm,theorem,(![X:$o,Y:$o]: (~ (X = (~ Y))) | (~ (X = Y)) ))."
      ;
    "thf(p_const,constant,(p : $o -> $o)). thf(a_const,constant,(a1 : $o)). thf(b_const,constant,(a2 : $o)). thf(a_const,constant,(a3 : $o)). thf(b_const,constant,(a4 : $o)). thf(a_const,constant,(a5 : $o)). thf(b_const,constant,(a6 : $o)). thf(a_const,constant,(a7 : $o)). thf(b_const,constant,(a8 : $o)). thf(a_const,constant,(a9 : $o)). thf(b_const,constant,(a10 : $o)). thf(thm,theorem,(p @ ( a1 & a2 )) => (p @ ( a2 & a1 )))."
      ;
    "thf(p_const,constant,(p : $o -> $o)). thf(a_const,constant,(a1 : $o)). thf(b_const,constant,(a2 : $o)). thf(a_const,constant,(a3 : $o)). thf(b_const,constant,(a4 : $o)). thf(a_const,constant,(a5 : $o)). thf(b_const,constant,(a6 : $o)). thf(a_const,constant,(a7 : $o)). thf(b_const,constant,(a8 : $o)). thf(a_const,constant,(a9 : $o)). thf(b_const,constant,(a10 : $o)). thf(thm,theorem,(p @ ( a1 & a2 & a3)) => (p @ ( a3 & a2 & a1 )))."
      ;
    "thf(p_const,constant,(p : $o -> $o)). thf(a_const,constant,(a1 : $o)). thf(b_const,constant,(a2 : $o)). thf(a_const,constant,(a3 : $o)). thf(b_const,constant,(a4 : $o)). thf(a_const,constant,(a5 : $o)). thf(b_const,constant,(a6 : $o)). thf(a_const,constant,(a7 : $o)). thf(b_const,constant,(a8 : $o)). thf(a_const,constant,(a9 : $o)). thf(b_const,constant,(a10 : $o)). thf(thm,theorem,(p @ ( a1 & a2 & a3 & a4 & a5 )) => (p @ ( a5 & a4 & a3 & a2 & a1 )))."
      ;
    "thf(p_const,constant,(p : $o -> $o)). thf(a_const,constant,(a1 : $o)). thf(b_const,constant,(a2 : $o)). thf(a_const,constant,(a3 : $o)). thf(b_const,constant,(a4 : $o)). thf(a_const,constant,(a5 : $o)). thf(b_const,constant,(a6 : $o)). thf(a_const,constant,(a7 : $o)). thf(b_const,constant,(a8 : $o)). thf(a_const,constant,(a9 : $o)). thf(b_const,constant,(a10 : $o)). thf(thm,theorem,(p @ (a1 & a2 & a3 & a4 & a5 & a6 & a7 & a8 & a9 & a10)) => (p @ (a10 & a9 & a8 & a7 & a6 & a5 & a4 & a3 & a2 & a1)))."
     ;
    "thf(thm,theorem,$true)."
     ;
    "thf(thm,theorem,?[X:$o] : X & X = $true)."
      ;
"
%--------------------------------------------------------------------------
% File     : SET???
% Domain   : Set Theory (Boolean properties)
% Problem  : 
% Version  : Encoding in Church's type theory by C. Benzmueller
% English  : A set A is subset of its powerset
% Refs     : [BSJK05] C. Benzmueller, V. Sorge, M. Jamnik, and M. Kerber, Can a Higher-Order and a 
%             First-Order Theorem Prover Cooperate? In F. Baader, A. Voronkov (eds.), Proceedings 
%             of the 11th International Conference on Logic for Programming Artificial Intelligence 
%             and Reasoning (LPAR), LNAI vol. 3452, pp. 415-431, Montevideo, Uruguay, 2005.  Springer.
%          : [BB05] C.E. Benzmueller and C.E. Brown, In J. Hurd and T. Melham, A Structured Set of 
%             Higher-Order Problems, TPHOLs 2005, LNCS 3606, pp. 66-81, Springer, 2005.
%          : [Try89] Trybulec (1989), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
% Source   : Formalization by C. Benzmueller following [BB05]
% Names    : 
% Status   : Theorem
% Rating   : 
% Syntax   : 
% Comments : 
%--------------------------------------------------------------------------

thf(subseteq_def,definition,(subseteq := (^ [A: $i -> $o, B: $i -> $o] : (! [X: $i] : (A @ X) => (B @ X))))). 

thf(powerset_def,definition,(powerset := (^ [A: $i -> $o] : (^ [B: $i -> $o] : (subseteq @ B) @ A)))). 

thf(thm,theorem,(! [A: $i->$o] : ((powerset @ A) @ A))).
"
      ;
"
%--------------------------------------------------------------------------
% File     : SET611+3
% Domain   : Set Theory (Boolean properties)
% Problem  : 
% Version  : Encoding in Church's type theory by C. Benzmueller
% English  : 
% Refs     : [BSJK05] C. Benzmueller, V. Sorge, M. Jamnik, and M. Kerber, Can a Higher-Order and a 
%             First-Order Theorem Prover Cooperate? In F. Baader, A. Voronkov (eds.), Proceedings 
%             of the 11th International Conference on Logic for Programming Artificial Intelligence 
%             and Reasoning (LPAR), LNAI vol. 3452, pp. 415-431, Montevideo, Uruguay, 2005.  Springer.
%          : [BB05] C.E. Benzmueller and C.E. Brown, In J. Hurd and T. Melham, A Structured Set of 
%             Higher-Order Problems, TPHOLs 2005, LNCS 3606, pp. 66-81, Springer, 2005.
%          : [Try89] Trybulec (1989), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
% Source   : Formalization by C. Benzmueller following [BB05]
% Names    : 
% Status   : Theorem
% Rating   : 
% Syntax   : 
% Comments : 
%--------------------------------------------------------------------------

thf(union_def,definition,(emptyset := (^ [X: $i] : false))).  

thf(intersection_def,definition,(intersection := (^ [A: $i -> $o, B: $i -> $o] : ^ [X: $i] : (A @ X) & (B @ X)))). 

thf(setminus_def,definition,(setminus := (^ [A: $i -> $o, B: $i -> $o] : ^ [X: $i] : (A @ X) & (~ (B @ X))))). 

thf(thm,theorem,(! [A: $i->$o, B: $i->$o] : (((intersection @ A) @ B) = emptyset) => ((setminus @ A) @ B) = A)).
"
    ;
"thf(thm,theorem,?[X:$o,Y:$o] : (X = Y) & (X = $true))."
    ;
"
%--------------------------------------------------------------------------
% File     : 1-bit-adder-b 
% Domain   : Hardware Verification
% Problem  : See Section 6 in [Gordon91]
% Version  : 
% English  : Specification, Representation of Implementation, and Verification of a 1-bit CMOS full adder
% Refs     : [Gordon91]
% Source   : Formalization by C. Benzmueller following {Gordon91]
% Names    : ???
% Status   : Theorem
% Rating   : ???
% Syntax   : ???
% Comments : Not solvable fully automatically in LEO and METIS.
%--------------------------------------------------------------------------

      thf(times_const,constant,(times : $i -> ($i -> $i))).

      thf(plus_const,constant,(plus : $i -> ($i -> $i))). 

      thf(zero_const,constant,(zero : $i)). 

      thf(one_const,constant,(one : $i)).  
     
      thf(two_const,constant,(two : $i)).  

      thf(three_const,constant,(three : $i)).  

      thf(bit_val_const,constant,(bit_val : $o -> $i)).  

      thf(all_true,definition,(all_true := (^ [A:$o, B:$o, C:$o] : A & B & C))).

      thf(one_false,definition,(one_false := (^ [A:$o, B:$o, C:$o] : (A & B & (~ C)) | (A & (~ B) & C) | ((~ A) & B & C)))).

      thf(two_false,definition,(two_false := (^ [A:$o, B:$o, C:$o] : (A & (~ B) & (~ C)) | ((~ A) & B & (~ C)) | ((~ A) & (~ B) & C)))).

      thf(all_false,definition,(all_false := (^ [A:$o, B:$o, C:$o] : (~ A) & (~ B) & (~ C)))).

      thf(pwr_def,definition,(pwr := (^ [P: $o] : (P = $true)))). 

      thf(gnd_def,definition,(gnd := (^ [P: $o] : (P = $false)))). 

      thf(ptran_def,definition,(ptran := (^ [G:$o, A:$o, B:$o] : (G => (A = B))))). 

      thf(ntran_def,definition,(ntran := (^ [G:$o, A:$o, B:$o] : ((~ G) => (A = B))))). 

      thf(add1_spec_def,definition,(add1_spec := (^ [A:$o, B:$o, CIN:$o, SUM:$o, COUT:$o] : (COUT & SUM & (all_true @ A @ B @ CIN)) | (COUT & (~ SUM) & (one_false @ A @ B @ CIN)) | ((~ COUT) & SUM & (two_false @ A @ B @ CIN)) | ((~ COUT) & (~ SUM) & (all_false @ A @ B @ CIN))))).

(((plus @ ((times @ two) @ (bit_val @ COUT))) @ (bit_val @ SUM)) = ((plus @ (bit_val @ A)) @ ((plus @ (bit_val @ B)) @ (bit_val @ CIN))))))). 

      thf(add1_impl_def,definition,(add1_impl := (^ [A:$o, B:$o, CIN:$o, SUM:$o, COUT:$o] : (? [P0:$o, P1:$o, P2:$o, P3:$o, P4:$o, P5:$o, P6:$o, P7:$o, P8:$o, P9:$o, P10:$o, P11:$o] : 
         (
            (((ptran @ P1) @ P0) @ P2)   & 
            (((ptran @ CIN) @ P0) @ P3)  & 
            (((ptran @ B) @ P2) @ P3)    & 
            (((ptran @ A) @ P2) @ P4)    & 
            (((ptran @ P1) @ P3) @ P4)   & 
            (((ntran @ A) @ P4) @ P5)    & 
            (((ntran @ P1) @ P4) @ P6)   & 
            (((ntran @ B) @ P5) @ P6)    & 
            (((ntran @ P1) @ P5) @ P11)  & 
            (((ntran @ CIN) @ P6) @ P11) & 
            (((ptran @ A) @ P0) @ P7)    & 
            (((ptran @ B) @ P0) @ P7)    & 
            (((ptran @ A) @ P0) @ P8)    & 
            (((ptran @ CIN) @ P7) @ P1)  & 
            (((ptran @ B) @ P8) @ P1)    & 
            (((ntran @ CIN) @ P1) @ P9)  & 
            (((ntran @ B) @ P1) @ P10)   & 
            (((ntran @ A) @ P9) @ P11)   & 
            (((ntran @ B) @ P9) @ P11)   & 
            (((ntran @ A) @ P10) @ P11)  & 
            (pwr @ P0)                   & 
            (((ptran @ P4) @ P0) @ SUM)  & 
            (((ntran @ P4) @ SUM) @ P11) & 
            (gnd @ P11)                  & 
            (((ptran @ P1) @ P0) @ COUT) & 
            (((ntran @ P1) @ COUT) @ P11)
      ))))).

      thf(verify_1_bit_adder,theorem,(! [A:$o, B:$o, CIN:$o, SUM:$o, COUT:$o] : (((((add1_impl @ A) @ B) @ CIN) @ SUM) @ COUT) => (((((add1_spec @ A) @ B) @ CIN) @ SUM) @ COUT))).
"
  ;
"thf(thm,theorem,(![P:$o>$o>$o]: ?[Y:$o]: (P @ Y @ Y) => ![X:$o]: (P @ X @ Y)))."
  ;
"thf(thm,theorem,(![P:$o>$o>$o]: ?[Y:$o]: (![X:$o]: (P @ X @ Y)) => (P @ Y @ Y)))."
  ;
"thf(thm,theorem,(![A:$o]: ?[X:$o,Y:$o,Z:$o]: X = A & Y = X & Y = Z))."
  ;
"thf(thm,theorem,(![A:$o]: ?[X:$o,Y:$o,Z:$o]: X = A & Y = Z & Z = A))."
  ;
"thf(thm,theorem,(![P:$i>$o]: ![F:$i>$i] : ?[X:$i]: (P @ (F @ X)) => (P @ X)))."
  ;
"thf(f,constant,(p:($i>$o)). thf(f,constant,(f:$i>$i)). thf(thm,theorem,(?[X:$i]: (p @ (f @ X)) => (p @ X)))."
  ;
"thf(f,constant,(f:$i>$i)). thf(a,constant,(a:$i)). thf(thm,theorem,(?[X:$i>$i]: (X @ a) = (f @ a)))."
  ;
"thf(f,constant,(f:($i>$i)>($i>$i))). thf(a,constant,(a:$i->$i)). thf(thm,theorem,(?[X:($i>$i)>($i>$i)]: (X @ a) = (f @ a)))."
  ;
"thf(f,constant,(f:($i>$i)>($i>$i))). thf(a,constant,(a:$i->$i)). thf(b,constant,(b:$o)). thf(thm,theorem,((?[X:($i>$i)>($i>$i)]: (X @ a) = (f @ a)) & b))."
  ;
"thf(f,constant,(f:($i>$i))). thf(a,constant,(a:$i)). thf(b,constant,(b:$i>$o)). thf(thm,theorem,((f @ a) = a) => (?[X:($i>$i)]: (((X @ (f @ a)) = (f @ (X @ a))) & (b @ (X @ a)))))."
  ;
"thf(f,constant,(f:($i>$i))). thf(a,constant,(a:$i)). thf(b,constant,(b:$i>$i)). thf(thm,theorem,(((((f @ a) = a) | (f @ (b @ a) = a)) &  (b @ a) = (f @ a)) => ((b @ a) = a)))."
  ;
"thf(f,constant,(c:$i)). thf(a,constant,(a:$i)). thf(b,constant,(b:$i)). thf(thm,theorem,(((a = b) | (b = c)) => (a = c)))."
  ;
"thf(f,constant,(c:$o)). thf(a,constant,(a:$o)). thf(b,constant,(b:$o)). thf(thm,theorem,(a = c))."
  ;
"thf(f,constant,(c:$i>$o)). thf(a,constant,(a:$i>$o)). thf(b,constant,(b:$i>$o)). thf(thm,theorem,(a = c))."
  ]

