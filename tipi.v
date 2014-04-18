(** * Teorija tipov in λ-račun. *)

(** Tipi so posplošitev množic, topološki prostorov in podatkovnih tipov. Naivno si jih
    lahko predstavljamo kot množice. Dejstvo, da ima izraz [e] tip [A] pišemo [e : A].

    Razne konstrukcije tipov se vedno uvede po istem vzorcu:

    - _formacija_: kako se naredi nov tip

    - _vpeljava_: kako se naredi ali sestavi elemente tipa (konstruktorji)

    - _upraba_: kako se elemente uporabi ali razstavi na sestavne dele (eliminatorji)

    - _enačbe_: kakšne enačbe povezujejo konstruktorje in eliminatorje
*)

(** ** Funkcije

  Za vsaka dva tipa [A] in [B] lahko tvorimo tip funkcij:

  - _formacija_: če sta [A] in [B] tipa, je tudi [A -> B] tip

  - _vpeljava_: če je [x : A] spremenljivka tipa [A] in [t : B] izraz tipa [B],
    odvisen od [x], potem je [fun (x : A) => t] tipa [A -> B]. Izrazu [fun ...]
    pravimo _λ-abstrakcija_, ker se v logiki piše $\lambda x : A . t$.

  - _uporaba_: če je [f : A -> B] in [e : A] potem je [f e : B]. Pravimo, da smo
    funkcijo [f] aplicirali na argumentu [e].

  - _enačbe_:

    - _pravilo $\beta$_: [(fun (x : A) => t) e = t{e/x}] kjer zapis "[t{e/x}]" pomeni,
      da v izrazu [t] vstavimo [e] namesto [x].

    - _pravilo $\eta$_: [(fun (x : A) => f x) = f]
*)
   
(** ** Kartezični produkt

    Da bomo lahko počeli kaj zanimivega, vpeljemo še kartezični produkt tipov:

    - _formacija_: če sta [A] in [B] tipa, je [A * B] tip (matematični zapis $A \times B$)

    - _vpeljava_: če je [a : A] in [b : B], potem je [(a,b) : A * B], _urejeni par_

    - _uporaba_: če je [p : A * B], potem imamo

      - _prva projekcija_: [fst p : A]
      - _druga projekcija_: [snd p : B]

    - enačbe, pri čemer je [a : A], [b : B] in [p : A * B]:
      - [fst (a, b) = a]
      - [snd (a, b) = b]
      - [p = (fst p, snd p)]

    Poznamo še enotski tip:

    - _formacija_: [unit] je tip
    - _vpeljava_: [tt : unit]
    - _uporaba_: pravil za uporabo ni
    - _enačbe_: če je [u : unit], je [u = tt].
*)

(** V Coqu lahko datoteko razdelimo na posamične razdelke z [Section X.] in [End X.] *)
Section RazneFunkcije.

  (* Predpostavimo, da imamo tipe [A], [B] in [C]. *)
  Context {A B C : Type}.

  Definition vaja1_1 : A * B -> B * A :=
    fun (u : A * B) => (snd u, fst u).
                                  
  Definition vaja1_2 : (A * B) * C -> A * (B * C):=
    fun (p : (A * B) * C) => (fst (fst p), (snd (fst p), snd p)).

  Definition vaja1_3 : A -> (B -> A):=
    fun (a : A) => (fun (b : B) => a).
  
  Definition vaja1_4 : (A -> B -> C) -> (A -> B) -> (A -> C):=
    fun (p : A -> B -> C) => fun (f : A -> B) => fun (a : A) => (p a) (f a).

  Definition vaja1_5 : (A * B -> C) -> (A -> (B -> C)):=
    fun (p : A * B -> C) => fun (a : A) => fun (b : B) => p (a,b). 
  
  Definition vaja1_6 : (A -> (B -> C)) -> (A * B -> C):=
    fun (f : A -> (B -> C)) => (fun p: A * B => f (fst p) (snd p)).

  Definition vaja1_7 : unit * A -> A:=
    fun (p : unit*A) => snd p.

  Definition vaja1_8 : A -> unit * A:=
    fun (a : A) => (tt, a).

End RazneFunkcije.

(** Ko zapremo razdelek [RazneFunkcije] nimamo več predpostavke, da so [A], [B], [C] tipi,
    vse definicije iz razdelka pa postanejo funkcije z dodatnimi parametri [A], [B], [C]. *)
Print vaja1_1.

(** Coq pravi: "Arguments [A], [B] are implicit and maximally inserted". To pomeni,
    da jih ni treba podati, ko uporabimo funkcijo [vaja1_1]. *)
Eval compute in vaja1_1 (42, false).

(* Če želimo eksplicitno nastaviti tudi [A] in [B], pišemo [@vaja1_1] namesto [vaja1_1]: *)
Eval compute in @vaja1_1 nat bool (42, false).

(** ** Izomorfni tipi

   Pravimo, da sta tipa [X] in [Y] izomorfna, če obstajata [f : X -> Y] in
   [g : Y -> X], da velja [g (f x) = x] za vse [x : X] in [g (g y) = y] za vse [y : Y].
*)
Definition iso (X : Type) (Y : Type) :=
  exists (f : X -> Y) (g : Y -> X),
    (forall x : X, g (f x) = x) /\ (forall y : Y, f (g y) = y).

(** V Coqu lahko uvedemo prikladno notacijo za izomorfizem. *)
Notation "X <~> Y" := (iso X Y) (at level 100).

Section Izomorfizmi1.
  (** Predpostavimo, da imamo tipe [A], [B] in [C]. *)
  Context {A B C : Type}.

  (** Dokaži, da so naslednji tipi izomorfni. *)

  Lemma vaja2_1 : A * B <~> B * A.
  Proof.
    unfold iso.
    exists (vaja1_1).
    exists (vaja1_1).
    unfold vaja1_1.
    simpl.
    tauto.
  Qed.

  Lemma vaja2_2 : (A * B) * C <~> A * (B * C).
  Proof.
    unfold iso.
    exists (vaja1_2), (fun (x: A * (B * C)) => ((fst x, fst (snd x)), snd (snd x))).
    tauto.
  Qed.

  Lemma vaja2_3 : unit * A <~> A.
  Proof.
    exists vaja1_7, vaja1_8.
    unfold vaja1_7, vaja1_8.
    simpl.
    split.
      - intro.
        destruct x.
        simpl.
        destruct u.
        auto.
        (*reflexivity.*)
      - auto.
  Qed.

  (** Pravimo, da sta funkciji [f g : X -> Y] _enaki po točkah_, če velja [forall x : X, f
      x = g x]. Aksiom _funkcijske ekstenzionalnosti_ pravi, da sta funkciji enaki,
      če sta enaki po točkah. Coq ne verjame v ta aksiom, zato ga po potrebi predpostavimo. 
      Najprej ga definirajmo. *)
  Definition funext :=
    forall (X Y : Type) (f g : X -> Y), (forall x, f x = g x) -> f = g.

  (** S pomočjo ekstenzionalnosti lahko dokažemo nekatere izomorfizme. *)
  Lemma vaja2_4 (F : funext) : (A * B -> C) <~> (A -> (B -> C)).
  Proof.
    unfold iso.
    exists (fun (x: A * B -> C) => fun (y: A) => fun (z:B) => x (y,z)), 
           (fun (x: A -> (B -> C)) => fun (y : A * B) => x (fst y) (snd y)).
    simpl.
    split.
      - intro.
        apply F.
        tauto.
      - intro.
        tauto.
  Qed.

  Lemma vaja2_5 (F : funext) : (unit -> A) <~> A.
  Proof.
    unfold iso.
    exists (fun (h : unit -> A) => h tt), 
           (fun (a : A) (_ : unit) => a).
    split.
      - intro h.
        apply F.
        destruct x.
        auto.
      - auto.
  Qed.

  Lemma vaja2_6 (F : funext) : (A -> unit) <~> unit.
  Proof.
    unfold iso.
    exists (fun (x: A -> unit) => tt), (fun (_: unit) => fun (x : A) => tt).
    split.
      - intro.
        apply F.
        intro.
        destruct x.
        auto.
      - intro.
        destruct y.
        tauto.
  Qed.
End Izomorfizmi1.

(** ** Vsota tipov

   Vsota tipov je kot disjunktna unija v teorijo množic ali koprodukt v kategorijah:

   - _formacija_: če sta [A] in [B] tipa, je [A + B] tip

   - _vpeljava_:

      - če je [a : A], potem je [inl a : A + B]
      - če je [b : B], potem je [inr b : A + B]

   - _uporaba_: če pri predpostavki [x : A] velja [u(x) : C] in
     če pri predpostavki [y : B] velja [v(y) : C] in če je [t : A + B], potem
     ima
     [(match t with
       | inl x => u(x)
       | inr y => v(y)
      end)]
     tip [C].

   - _enačbe_:

      - [match (inl a) with
         | x => u(x)
         | y => v(y)
         end] je enako [u(a)].

      - [match (inr b) with
         | x => u(x)
         | y => v(y)
         end] je enako [v(b)].

      - [match t with
         | inl x => inl x
         | inr y => inr y
         end] je enako [t].

*) 

(** ** Prazen tip

    Nekoliko bolj nenavaden je prazen tip:

    - _formacija_: [Empty_set] je tip
   
    - _vpeljava_: ni pravil za uporabo

    - _uporaba_: če [t : Empty_set], potem ima [match t with end] tip [A]

    - _enačbe_: [match t with end] je enako [a] za vse [a : A]
*)

Section FunkcijeVsote.
  (** Predpostavimo, da imamo tipe [A], [B] in [C]. *)
  Context {A B C : Type}.

  Definition vaja3_1 : (A + B -> C) -> (A -> C) * (B -> C):=
    fun (x : A + B -> C) => (fun (a:A) => x (inl a), fun (b : B) => x (inr b)).

  (* S stavkom match obravnavmo element, ki je vsota tipov. *)

  Definition vaja3_2 : A + B -> B + A:=
    fun (x : A + B) => (match x with 
                          | inl x => inr x 
                          | inr x => inl x
                        end).

  Definition vaja3_3 : (A + B) * C -> A * C + B * C:=
    fun (x : (A + B) * C) => match fst x with
                                | inl z => inl (z, snd x)
                                | inr z => inr (z, snd x)
                             end.
  
  Definition vaja3_4 : A * C + B * C -> (A + B) * C:=
    fun (x : A * C + B * C) => match x with
                                  | inl y => (inl (fst y), snd y)
                                  | inr y => (inr (fst y), snd y)
                                end.

  Definition vaja3_5 : (A -> C) * (B -> C) -> (A + B -> C):=
    fun (x : (A -> C) * (B -> C)) => fun (y : A + B) => match y with 
                                                          | inl z => fst x z
                                                          | inr z => snd x z
                                                        end.

  Definition vaja3_6 : Empty_set -> A:=
    fun (x : Empty_set) => match x with end.

  Definition vaja3_7 : Empty_set + A -> A:=
    fun (x : Empty_set + A) => match x with 
                                | inl z => vaja3_6 z
                                | inr z => z
                              end.

  Definition vaja3_8 : A -> ((A -> Empty_set) -> Empty_set):=
    fun (x : A) => fun (y: (A -> Empty_set)) => y x.

  Definition vaja3_9 : A + (A -> Empty_set) -> (((A -> Empty_set) -> Empty_set) -> A):=
    fun (x : A + (A -> Empty_set)) => fun (y : ((A -> Empty_set) -> Empty_set)) => 
         match x with 
           | inl z => z
           | inr z => vaja3_6 (y z)
         end. 

End FunkcijeVsote.

Section Izomorfizmi2.
  (** Sam ugotovi, kje potrebuješ funkcijsko ekstenzionalnost. *)

  Context {A B C : Type}.

  Definition vaja4_1 : A + B <~> B + A.
  Proof.
    exists vaja3_2, vaja3_2.
    split.
    tauto.
    tauto.
  Qed.

  Definition vaja4_2 : (A + B) * C <~> A * C + B * C.
  Proof.
    exists vaja3_3, vaja3_4.
    split.
    tauto.
    tauto.
  Qed.

  Definition vaja4_3 (F:funext): (A + B -> C) <~> (A -> C) * (B -> C).
  Proof.
    exists (fun (x: (A + B -> C)) => (fun (y : A) => x (inl y), fun (y : B) => x (inr y))),vaja3_5.
    split.
      - intros.
        unfold vaja3_5.
        simpl.
        apply F.
        tauto.
      - tauto.
  Qed.

  Definition vaja4_4 : Empty_set + A <~> A.
  Proof.
    exists vaja3_7, (fun (x : A) => inr x).
    split.
    tauto.
    tauto. 
  Qed.

  Definition vaja4_5 (a : A) (F : funext): (A -> Empty_set) <~> Empty_set.
  Proof.
    exists (fun (x : A -> Empty_set) => x a).
    exists (fun (x : Empty_set) => match x with end).
    split.
      - intro.
        apply F.
        intro.
        destruct x.
      - intro.
        destruct y.
  Qed.

  Definition vaja5_5 (F: funext): (Empty_set -> A) <~> unit.
  Proof.
    exists (fun (x: Empty_set -> A) => tt).
    exists (fun (y:unit) => fun (z : Empty_set) => match z with end).
    split.
      - intro.
        apply F.
        tauto.
      - destruct y.
        tauto.
  Qed.

End Izomorfizmi2.

Section Zabava.
  (** Pa še neka vaj za zabavo. *)
  Context {A B : Type}.

  (* Koliko funkcij A * B -> A + B lahko definiraš? *)  
  Definition vaja5_1_1 : A * B -> A + B:=
   fun (x : A * B) => inl (fst x).

  Definition vaja5_1_2 : A * B -> A + B:=
   fun (x : A * B) => inr (snd x).

  (* Koliko funkcij tipa (A * A) * A -> A * A lahko definiraš? Šest! *)
  Definition vaja5_2_XX : (A * A) * A -> A * A.
  Admitted.

  (* Koliko funkcij tipa (A -> A) -> (A -> A) lahko definiraš? Neskončno. *)
  Definition vaja5_3_XX : (A -> A) -> (A -> A).
  Admitted.

End Zabava.
