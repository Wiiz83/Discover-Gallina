Section projet.


(* PARTIE 1 *)

(* Type de l'identite polymorphe *)
Definition tid : Set := forall T: Set, T->T.
Definition id : tid := fun T:Set => fun x:T => x.

Compute id nat 3.
Compute id bool true.

(* Converti bool en nat *)
Definition nbtrue1 := fun b =>
match b with
| true => 1
| false => 0
end.

Compute nbtrue1 true.
Compute id (bool->nat) nbtrue1 true.

Compute id tid id.

Theorem th_id : forall T: Set, forall x: T, id T x = x.
Proof. (* marque le debut de la preuve *)
cbv delta [id]. (* les tactiques commencent par des minuscules *)
cbv beta.
(* A ce stade on a une egalite entre deux termes syntaxiquement identiques *)
reflexivity.
Qed. (* marque la fin de la preuve *)


(* PARTIE 2 *)


Definition pbool : Set := forall T: Set, T -> T -> T.
Definition ptr : pbool := fun T:Set => fun (x:T) (y:T) => x.
Definition pfa : pbool := fun T:Set => fun (x:T) (y:T) => y.

Compute ptr bool true false.
Compute pfa bool true false.

(*2.2.méthode 1*)
Definition neg_pbool := fun T:Set => fun (b:pbool) x y => b x y.

(*2.2.méthode 2*)
Definition neg_pbool_2 := fun T:Set => fun (b:bool) => fun (x:T) (y:T) => fun (x:T) (y:T) => x.

Variable T:Set.
Variable x:T.
Variable y:T.
Definition pif := fun T:Set=>( fun (b : pbool) m n => b m n ).

Compute pif (pbool->T->T->T)pfa T x y.
Compute pif (pbool->T->T->T) pfa bool false true.

Definition pand := fun (a : pbool) (b : pbool)  x y  => pif (pbool->T->T->T) a T (pif (pbool->T->T->T) b T x y) y.

Definition pcor := fun (a : pbool) (b : pbool) => fun x y  => pif (pbool->T->T->T) a T x (pif (pbool->T->T->T) b T x y).

Compute pand pfa pfa x y.
Compute pcor ptr ptr x y.


(* PARTIE 3 *)

(*Type produit de deux tye differents*)
Definition pprod_nb_n := (nat->pbool->nat)->nat.
(*Constructeur d'un couple de deux type différents*)
Definition ppair_nb_n : nat -> pbool -> pprod_nb_n := fun a b => fun k => k a b.

(*Type produit de deux tye differents*)
Definition pprod_bn_n := (pbool->nat->nat)->nat.
Print pprod_bn_n.
(*Constructeur d'un couple de deux type différents*)
Definition ppair_bn_n : pbool -> nat -> pprod_bn_n := fun a b => fun k => k a b.
Print ppair_bn_n.

(*Autre Version*)
(*Type produit de deux tye differents*)
Definition  pprod_nb_n_2 : Set := forall T: Set, pbool -> nat -> T -> T.
(*Type produit de deux tye differents*)
Definition  pprod_bn_n_2 : Set := forall T: Set, nat -> pbool -> T -> T.

Definition echange:= fun (a:nat) (b:bool) => (b, a).
Compute echange 5 true.
Compute echange 6 false.

(*Definition pprod : Set -> Set -> Set := fun U V => forall T:Set,T -> T -> T -> T .*)
Definition pprod (U V: Set): Set := forall T:Set, (U -> V -> T) -> T.
Print pprod.
(*Deux Verison *)
Definition ppair (U V: Set):= fun (a:U) (b:V) => fun (k:U->V->T) => k a b.
Definition ppair_2 ( U V : Set) : U->V->pprod U V:= fun a b =>fun T:Set=>fun k => k a b.

Compute ppair_2 T nat.
Compute ppair_2 nat T.
Compute ppair bool T.
Compute ppair T bool.
Compute ppair pbool nat.
Compute ppair T pbool.
Compute ppair_2 bool pbool.

Definition echange_2 (U V: Set):= fun (a:U) (b:V) => (b, a).
Print echange_2.
Compute echange_2 T nat.
Compute echange_2 bool nat.
Definition f := fun x:nat => x+x.
Compute f 3.

(*3.2 SOMME*)
Definition psom (U V: Set) : Set := forall T:Set, (U->T) -> (V->T) -> T.
Print psom.
Definition C1 (U V: Set) : U -> psom U V := fun u => fun T:Set => fun k1 => fun k2 => k1 u.
Definition C2 (U V: Set) : V -> psom U V := fun v => fun T:Set => fun k1 => fun k2 => k2 v.

Compute C1 T nat.
Compute C2 nat T.
Compute C1 bool T.
Compute C2 T bool.
Compute C1 pbool nat.
Compute C2 T pbool.
Compute C1 bool pbool.



(*Meme question pour Echange *)

(*Typage polymorphe*)
(* type b123 de la che 3, section 3, ainsi que les constructeurs correspondants*)
Definition b123 :  Set := forall T: Set,(bool -> nat) ->(bool -> bool -> nat) ->(bool -> bool -> bool -> nat) -> nat.
Definition Co1 : bool -> b123 := fun a => fun T:Set => fun k1 =>fun k2=>fun k3 => k1 a.
Definition Co2 : bool->bool-> b123 := fun a => fun b => fun T:Set => fun k1 =>fun k2=>fun k3 => k2 a b.
Definition Co3 : bool->bool->bool-> b123 := fun a => fun b => fun c => fun T:Set => fun k1 =>fun k2=>fun k3 => k3 a b c.


(* PARTIE 4 *)
Definition pnat :Set := forall T: Set, (T->T)->(T->T).
Definition p0 : pnat := fun T:Set => fun (f:T->T) (x:T) => x.
Definition p1 : pnat := fun T:Set => fun (f:T->T) (x:T) => f x.
Definition p2 : pnat := fun T:Set => fun (f:T->T) (x:T) => f (f x).
Definition p3 : pnat := fun T:Set => fun (f:T->T) (x:T) => f (f (f x)).
Definition p4 : pnat := fun T:Set => fun (f:T->T) (x:T) => f (f (f (f x))).

Definition pS : pnat -> pnat := fun (n:pnat) => fun T:Set => fun f => fun x => f (n T f x).

Compute pS p0.
Compute pS p1.


(*Definition pplus1 : pnat -> pnat -> pnat := fun n => fun m => fun f x => (n f(m f x)).
Compute pplus1 p0 p0.*)




(* MULTIPLICATION SI DESSOUS ! *)
Definition pprod1 : pnat -> pnat-> pnat := fun n => fun m => fun f x => (n f(m f x)).
Compute pprod1 p4 p4.



Definition cbool := T -> T -> T.

Definition testZero : pnat -> cbool := fun n => fun x y => (n (fun z => y) x).


Compute testZero p0.
Compute testZero p4.

Definition testZero : pnat -> pbool := fun (n:pnat) => fun (x:T) (y:T) => (n.


Definition pplus2 : pnat -> pnat -> pnat := fun (n:pnat) (m:pnat) => n pnat pS m.
Compute pplus2 p4 p4.

(* Definition addChurch : cnat -> cnat-> cnat := fun n => fun m => fun f x => (n f(m f x)).
Definition prodChurch : cnat -> cnat-> cnat := fun n => fun m => fun f => (n (m f)). *)

(*
Definition pprod : pnat -> pnat -> pnat := fun (n:pnat) => fun (m:pnat) => fun f => (n (m f)).
Compute pprod p4 p4.

Definition pbool : Set := forall T:Set, T -> T -> T.
Definition testZero : pnat -> pbool := fun (n:pnat) => fun (x:T) (y:T) => (n (fun z => y) x).
Compute testZero p0.
*)



(* PARTIE 5 *)
Definition listen : Set := forall T: Set, T -> (pnat -> T -> T) -> T.
Definition liste A : Set := forall T: Set, T -> (A -> T -> T) -> T.

Definition pnil A : liste A := fun T:Set => fun (x:T) (c:A->T->T) => x.
Definition pcons A : A -> liste A -> liste A := fun (a:A) (q:liste A) => fun T:Set => fun (x:T) (c:A->T->T) => c a(q T x c).


(* PARTIE 6 *)
Definition arbin (A : Set) := forall T: Set, T -> (T -> A -> T -> T) -> T.
(*Arbre vide *)
Definition pV (A :Set) := fun T:Set => fun (x:T) => fun (c:T->A->T->T) => x.
(*Le nœud comprenant un sous-arbre gauche, un habitant de A et un sous-arbre droit*)
Definition pN (A : Set) := fun (g:arbin A) (a:A) (d:arbin A) => fun T:Set => fun (x:T) (c:T->A->T->T) => c (g T x c) a (d T x c).


End projet.