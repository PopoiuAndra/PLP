Require Import String.
Open Scope string_scope.

Inductive AExp :=
| num : nat -> AExp
| var : string -> AExp
| add : AExp -> AExp -> AExp
| sub : AExp -> AExp -> AExp
| div : AExp -> AExp -> AExp.


Coercion var : string >-> AExp.
Coercion num : nat >-> AExp.

Notation "A +' B" := (add A B)
                       (at level 50, left associativity).
Notation "A /' B" := (div A B)
                       (at level 40, left associativity).
Notation "A -' B" := (sub A B)
                       (at level 50, left associativity).


Definition Env := string -> option nat.

Require Import Nat.
Check Nat.sub.
Compute (Nat.sub 2 3).

Definition minus'(n m :nat): option nat :=
if Nat.ltb n m
  then None
else Some(Nat.sub n m).

Definition minusOption (n m :option nat) : option nat :=
match n, m with
| Some n', Some m' => minus' n' m'
| _,_ => None
end.
Compute minusOption(minus' 4 3)(minus' 3 3).
Compute minusOption(Some 4)(Some 5).

Definition env0 : Env :=
  fun v => if string_dec v "x"
           then Some 7
           else if string_dec v "y"
                then Some 10
                else None.

Definition update
           (x : string)
           (v : nat)
           (e : Env)
  : Env :=
  fun y => if string_dec y x
           then Some v
           else e y.

Definition adun(n m : option nat) : option nat:=
match n, m with
|Some n', Some m' => Some(n'+m')
|_,_ => None
end.

Definition imp(n m : option nat) : option nat:=
match n, m with
|Some n', Some 0 => None
|Some n',Some m' => Some (n'/m')
|_,_ => None
end.

(*EXERCITIUL 1*)
Fixpoint EX1eval (a : AExp) (e : Env) : option nat :=
  match a with
  | num v => Some v
  | var x => e x
  | a1 +' a2 => adun(EX1eval a1 e) (EX1eval a2 e)
  | a1 -'a2 => minusOption (EX1eval a1 e)( EX1eval a2 e)
 (*EX1eval ((EX1eval a1 e) - (EX1eval a2 e)) e*)
  | a1 /'a2 => imp (EX1eval a1 e) (EX1eval a2 e) 
  end.

Compute EX1eval(7+'"x"/'2) env0.


(*EXERCITIUL 2*)
Inductive Cond :=
| base : bool -> Cond
| bnot : Cond -> Cond
| beq  : AExp -> AExp -> Cond
| less : AExp -> AExp -> Cond
| band : Cond -> Cond -> Cond.
Inductive Stmt :=
| skip : Stmt 
| assign : string -> AExp -> Stmt
| seq : Stmt -> Stmt -> Stmt
| ite : Cond -> Stmt -> Stmt -> Stmt (* if-then-else *)
| while : Cond -> Stmt -> Stmt.

Definition equ(n m : option nat) : bool :=
match n, m with 
| Some n', Some m' => if(Nat.eqb n' m') 
                        then true
                      else false
| _,_ => false
end.

Definition les(n m : option nat) : bool :=
match n, m with 
| Some n', Some m' => if(Nat.ltb n' m') 
                        then true
                      else false
| _,_ => false
end.

Fixpoint beval (b : Cond) (e : Env) : bool :=
 match b with
 | base b' => b'
 | bnot b' => negb (beval b' e)
 | beq a1 a2 => if(equ (EX1eval a1 e) (EX1eval a2 e))
                  then true 
                else false
 | band b1 b2 => if (beval b1 e)
                  then (beval b2 e)
                  else false
 | less a1 a2 => if (les (EX1eval a1 e) (EX1eval a2 e) )
                    then true
                 else false
 end.

Compute beval(bnot (less 11 10))  (env0 ).


Notation "A <' B" := (less A B) (at level 60).
Infix "&&'" := band (at level 81, left associativity).


Notation "A :=' B" := (assign A B) (at level 97, right associativity).
Notation "S1 ;; S2" := (seq S1 S2) (at level 98, right associativity).

Definition ToNat(n : option nat) : nat :=
match n with
| Some n' => n'
|_ => 0
end.

Fixpoint eval
         (s : Stmt)
         (e : Env)
         (fuel : nat)
  : Env :=
  match fuel with
  | 0 => e
  | S n =>
      match s with
      | assign x a  => update x (ToNat(EX1eval a e)) e 
      | ite c s1 s2 => if (beval c e)
                       then eval s1 e n
                       else eval s2 e n
      | skip        => e
      | seq s1 s2   => eval s2 (eval s1 e n) n
      | while c s   => if (beval c e)
                       then
                         (eval
                            (s ;; while c s) e n)
                       else e
      end
  end.

Definition CMMDC(n m : nat) :=
  "x" :=' n;;
  "y" :=' m;;
  while (bnot (beq ("x") ("y"))) (
    ite("y" <' "x") 
          ("x" :=' "x" -' "y") 
          ("y" :=' "y" -' "x")
  );;
  "result" :=' "x".

Check CMMDC 2 3. 
Compute (eval (CMMDC 18 27) env0 100) "result".

Definition Fibonacci(n : nat) :=
  "n" :=' n;;
  "numar1" :=' 1;;
  "numar2" :=' 1;;
  "numar" :=' 0;;
  ite("n" <' 3) ("numar" :='1) (
  "n" :=' n -' 2;;
  while(0 <' "n")(
    "numar" :=' "numar1" +' "numar2";;
    "numar2" :=' "numar1";;
    "numar1" :=' "numar";;
    "n" :=' "n" -' 1
  )
).

Check Fibonacci 2 . 
Compute (eval (Fibonacci 5) env0 30) "numar".


(*Ex 3*)
(*
not , conj, dij
env : sting -> bool
*)

Inductive Propoz :=
  | vari : nat -> Propoz
  | nu : Propoz -> Propoz
  | si : Propoz -> Propoz -> Propoz
  | sau : Propoz -> Propoz -> Propoz.

Coercion vari: nat >-> Propoz.

Require Import List.

Definition Assign := list (nat * bool).

Definition EX3 : Assign :=(0, false) :: (1, true) :: nil.

Fixpoint EX3eval (x : Propoz) (a : Assign) : bool :=
  match x with
  | vari n => match find (fun x => Nat.eqb (fst x) n) a with
             | Some (_, b) => b
             | None => false
             end
  | nu p => negb (EX3eval p a)
  | si p1 p2 => (EX3eval p1 a) && (EX3eval p2 a)
  | sau p1 p2 => (EX3eval p1 a) || (EX3eval p2 a)
  end.

Compute EX3eval( sau 0 (si 1 0)) EX3.
