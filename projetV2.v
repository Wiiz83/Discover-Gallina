(* =========== PARTIE 1 =============== *)

(* Type de l'identite polymorphe *)
Definition tid : Set := forall T: Set, T -> T.
Definition id : tid := fun T:Set => fun x:T => x.

(* test sur des entiers*)
Compute id nat 5.
Compute id nat 1.
Compute id nat 10.

(* test sur des booléens*)
Compute id bool true.
Compute id bool false.


Definition nbtrue1 := fun b =>
match b with
| true => 1
| false => 0
end.

(*test sur une fonction bool vers nat*)
Compute id (bool -> nat) nbtrue1.

(*test sur la fonction id*)
Compute id tid id.

(*preuve du théorème*)
Theorem th_id : forall T: Set, forall x: T, id T x = x.
Proof.
cbv delta [id].
cbv beta.
reflexivity.
Qed.



(* =========== PARTIE 2 =============== *)

(*definition des type polymorphes booleén*)
Definition pbool : Set := forall T: Set, T -> T -> T.

Definition ptr : pbool := fun T:Set => fun (x:T) (y:T) => x.
Definition pfa : pbool := fun T:Set => fun (x:T) (y:T) => y.

(* codage du not 1er méthode*)
Definition pnot := fun b:pbool => fun (T:Set) (x:T) (y:T)  => b T y x .
(*Quelques tests*)
Compute pnot.
Compute pnot pfa.
Compute pnot ptr.

(* codage du not 2éme méthode*)
Definition pnot2 := fun (b:pbool) => b pbool pfa ptr .
(*Quelques tests*)
Compute pnot2.
Compute pnot2 pfa.
Compute pnot2 ptr.

(* codage du and *)
Definition pand := fun (a : pbool) (b : pbool) => fun x y  => a pbool (b pbool x y ) y.
(*Quelques tests*)
Compute pand pfa pfa.
Compute pand ptr ptr.
Compute pand pfa ptr.
Compute pand ptr pfa.

(* codage du or *)
Definition por := fun (a : pbool) (b : pbool) => fun x y  => a pbool x (b pbool x y).
(*Quelques tests*)
Compute por pfa pfa.
Compute por ptr ptr.
Compute por pfa ptr.
Compute por ptr pfa.

(*Quesition 4 générique*)
Definition q4 := fun (b:pbool) => fun x y => b nat x y.
Compute q4 ptr 3 5.
Compute q4 pfa 3 5.

(*Question 5*)
Definition q5 := fun (b:pbool) => b pbool b. 
Compute q5 pfa.
Compute q5 ptr.


(* =========== PARTIE 3 =============== *)

(*Type et constructeur d'un couple (nat,bool)*)
Definition pprod_nb := forall T:Set , (nat -> bool -> T)->T.
Definition ppair_nb : nat -> bool -> pprod_nb := fun b1 b2 => fun (T:Set) (k:nat->bool->T) => k b1 b2.

(*Type et constructeur d'un couple (bool,nat)*)
Definition pprod_bn:= forall T:Set, (bool -> nat -> T)->T.
Definition ppair_bn : bool -> nat -> pprod_bn := fun b1 b2 => fun (T:Set) (k:bool->nat->T) => k b1 b2.


(*Fonction d'echange des arguments*)
Definition echange_bis : nat -> bool -> pprod_bn:= fun b1 b2 => ppair_bn b2 b1.
Definition echange : pprod_nb -> pprod_bn := fun c => c pprod_bn echange_bis .
Compute echange (ppair_nb 10 true).
Compute echange (ppair_nb 5 false).

(*Type et constructeur d'un couple generique*)
Definition pprod (U V:Set) : Set := forall T:Set, (U -> V -> T)->T.
Definition ppair (U V : Set) : U -> V -> (pprod U V) := fun b1 b2 => fun (T:Set) (k: U->V->T) => k b1 b2.
Compute ppair nat bool 10 true.
Compute ppair nat nat 10 10.

(*Definition de pprod_nb en utilisant pprod et ppair*)
Definition pprod_nb_bis := pprod nat bool.
Definition ppair_nb_bis : nat -> bool -> pprod_nb_bis := fun b1 b2 => ppair nat bool b1 b2.
Compute ppair_nb_bis 10 true.

(*exemple de couple d'un nat et d'un bool*)
Compute ppair nat bool 10 true.
Compute ppair nat bool 5 false.


(*Definiton de la somme*)
Definition psom (U V: Set) : Set := forall (T:Set), (U -> T) -> (V -> T) -> T.
Definition C1 (U V: Set) : U -> psom U V := fun u => fun T:Set => fun (k1:U->T) => fun (k2:V->T) => k1 u.
Definition C2 (U V: Set) : V -> psom U V := fun v => fun T:Set => fun (k1:U->T) => fun (k2:V->T) => k2 v.
Compute C1 nat bool 1.
Compute C2 nat bool true.

(*fonction fiche 3 section 2)
Definition q1 (U V : Set) := fun (x:(psom U V)) =>
match x with
| C1 => 1
| C2 => 0
end.*)

(*Type et constructeur d'un nat_ou_bool_prod_bn_n *)
Definition psom_bn_n := psom bool nat .
Definition C1_bn_n := fun (u:bool) => C1 bool nat u.
Definition C2_bn_n := fun (v:nat) => C2 bool nat v.


(*Definition q3 := fun (x:psom_bn_n) =>
match x with
| true => ppair_bn false 1
| false =>  ppair_bn false 0
| _ =>  ppair_bn true x
end.*)


(*Definition q4 (U V : Set) := fun (x:psom U V) =>
match x with
| true => ppair_bn false 1
| false =>  ppai
r_bn false 0
| _ =>  ppair_bn true x
end.*)

(*fonction fiche 3 section 3*)
(*Definiton de la somme a 1, 2 ou 3 arguments*)
Definition b123 (U V W: Set) : Set := forall (T:Set), (U -> T) -> (U -> V -> T) -> (U -> V -> W -> T) -> T.
Definition b123_c1 (U V W: Set) : U -> b123 U V W := fun u => fun T:Set => fun (k1:U->T) => fun (k2:U->V->T) => fun (k3:U->V->W->T) => k1 u.
Definition b123_c2 (U V W: Set) : U->V -> b123 U V W := fun u v => fun T:Set => fun (k1:U->T) => fun (k2:U->V->T) => fun (k3:U->V->W->T) => k2 u v.
Definition b123_c3 (U V W: Set) : U->V->W -> b123 U V W := fun u v w => fun T:Set => fun (k1:U->T) => fun (k2:U->V->T) => fun (k3:U->V->W->T) => k3 u v w.

(*Calcul du nombre de true dans un type somme123*)
Definition nbtrue1 := fun b =>
match b with
| true => 1
| false => 0
end.
(*
Definition nb_true_b123 := fun bbb : b123 bool bool bool => bbb (fun a => nbtrue1 a) (fun a => fun b => (nbtrue1 a) + (nbtrue1 b)) (fun a => fun b => fun c => (nbtrue1 a) + (nbtrue1 b) + (nbtrue1 c)).
Compute nb_true_b123 (b123_c1 bool bool bool false).
Compute nb_true_b123 (b123_c2 bool bool bool false true).
Compute nb_true_b123 (b123_c3 bool bool bool true true false).
Compute nb_true_b123 (b123_c3 bool bool bool true false true).
*)




(* =========== PARTIE 4 =============== *)

Definition pnat := forall (T:Set), (T->T) -> (T->T).
Definition p0: pnat := fun (T:Set) (f:T->T) (x:T) => x.
Definition pS: pnat->pnat := fun (n:pnat) => fun (T:Set) f x => f (n T f x).
Definition pbool : Set := forall T: Set, T -> T -> T.
Definition ptr : pbool := fun T:Set => fun (x:T) (y:T) => x.
Definition pfa : pbool := fun T:Set => fun (x:T) (y:T) => y.

Definition addition: pnat -> pnat -> pnat := fun n => fun m => fun f x => (n f (m f x)).

Definition multiplication : (pnat -> pnat -> pnat) := fun n m => (fun _ s => n _ (m _ s)).
(*tests sur la multiplication*)
Compute multiplication (pS (pS p0)) (pS p0). 
Compute multiplication p0 (pS p0). 
Compute multiplication (pS (pS (pS p0))) (pS (pS p0)). 


Definition test_zero : pnat -> pbool := fun n => fun T:Set => fun (x:T) (y:T) => (n T (fun z => y) x).


(*Autre codage de l'addition, on ecrit n et on lui ajoute m successeur*)
Definition pplus: pnat -> pnat -> pnat := fun n m => n pnat pS m.
Compute pplus p0 (pS p0).
Compute pplus (pS (pS p0)) (pS (pS p0)).
Compute pplus (pS (pS (pS (pS p0)))) (pS p0).


(* Definition de la composition de g et f *)
Definition cnat (T : Set):= (T->T) -> (T->T).
Definition compo (T : Set): (T->T) -> (T->T) -> (T->T) := fun g f => fun x => g (f x).
(* Un raccourci syntaxique pour ecrire g o f au lieu de (compo g f ) *)
Notation "g 'o' f" := (compo g f) (at level 10).

(*Type et constructeur d'un couple (nat,nat)*)
Definition pprod := forall T:Set , (nat -> nat -> T)->T.
Definition ppair : nat -> nat -> pprod := fun b1 b2 => fun (T:Set) (k:nat->nat->T) => k b1 b2.


(* Un iterateur de f, n fois *)
(*
Fixpoint iter (f:T->T) (n1: nat) (n2: nat) :=
match n1 with
| p0 => fun x y => ppair y (pS y) 
| S p => f o (iter f p)
end.



Definition soustraction := fun n m => m (n pred).
Definition inferieur_egal := fun n m =>
match (soustraction n m) with
| p0 => true
| _ => false
end.
*)

