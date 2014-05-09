(** V teh vajah se bomo učili uporabljati standardno knjižnico
    v Coqu (http://www.lix.polytechnique.fr/coq/stdlib/).
    Knjižnica ima veliko koristnih izrekov in definicij. Ponavadi
    je glavna težava v tem, da je težko najti izrek, ki ga v
    danem trenutku potrebujemo. Coq ima nekaj ukazov, s katerim
    lahko prgledujemo knjižnico in iščemo potencialno koristne
    izreke.

    Najprej bomo vadili uporabo knjižnice za realna števila, zato jo
    najprej zahtevamo z ukazom [Require Import].
*)

Require Import Reals.

(** Večinoma bomo uporabljali notacijo za realna števila. Na primer,
    želimo, da bi "x + y" pomenilo seštevanje realnih števil, ne naravnih.
    Lahko bi vsakič pisali "(x + y)%R", a je bolj praktično, da vključimo
    notacijo za realna števila z ukazom [Local Open Scope]. *)

Local Open Scope R_scope.

(* Če bomo potrebovali operacije na naravnih številih, lahko še vedno
   pišemo "(x + y)%nat". *)

(** Dokažimo preprosto neenačbo. *)
Theorem vaja_1 (x y : R) :  x^2 + y^2 >= 2 * x * y.
Proof.
  (* Postopek dokaza je naslednji:

     - prenesemo vse na eno stran: x^2 - 2 * x * y + y^2 >= 0
     - faktoriziramo: (x - y)^2 >= 0
     - opazimo, da je kvadrat števila nenegativen

     Prva težava: kako prenesemo [2 * y * x] na drugo stran neenačbe?
     Verjetno obstaja ustrezna lema v knjižnici. Treba je malo brskati.
     Poskusite in če ne najdete odgovora v 5 minutah, poglejte rešitev
     v tej datoteki. Iščite v knižnici [RIneq],
     http://www.lix.polytechnique.fr/coq/stdlib/Coq.Reals.RIneq.html

     Rešitev je nižje spodaj.

              |
              |
              V
































     Lenoba lena, malo bolj se potrudi!








































    Lema, ki jo iščemo je [Rminus_ge]. O njej izvemo več z ukazom
    [Check Rminus_ge.], ki pove:

      Rminus_ge : forall r1 r2 : R, r1 - r2 >= 0 -> r1 >= r2
 *)
 apply Rminus_ge.
 (** Sedaj bi radi faktorizirali. To je najlažje narediti tako,
     da Coq-u povemo, naj zamenja [x^2 + y^2 - 2 * x * y] s
     kvadratom [(x - y)^2]. Če bi to naredili, bi se nam kasneje
     zataknilo: v knjižnici je kvadrat realnega števila definiran
     kot [Rsqr x]. Zato je bolje, da [Rsqr] uporabimo tudi mi.

     Lahko pa bi tudi v knjižnici poiskali lemo [Rsqr_plus],
     vendar tega zdaj ne bomo naredili, da vidimo, kako se dela
     na roke.
 *)
  replace (x^2 + y^2 - 2 * x * y) with (Rsqr (x - y)).
  - (* Spet iščemo lemo, tokrat, da je kvadrat nenegativen.
       Hitro najdemo

         Lemma Rle_0_sqr : forall r, 0 <= Rsqr r. 

       Na žalost gre v napačno smer, mi potrebujemo Rsqr r >= 0.
       Najprej moramo svojo neenačbo obrniti. Torej potrebujemo
       lemo, ki pravi [x <= y -> y >= x]. Spet malo pogledamo in
       najdemo [Rle_ge]. *)
    apply Rle_ge.
    apply Rle_0_sqr.
    (* Kot vidimo, je vse skupaj ena nočna mora. Hej, bomo vsaj imeli dokaz z vsemi
       podrobnostmi. *)
    - (* Tu bi bilo najbolj logično, če bi uporabili poenostavljanje
       izrazov. To se lahko v splošnem naredi s [simpl] in s [compute]. Za delo s
       kolobarji (realna števila tvorijo kolobar, saj tvorijo obseg) imamo taktiki
       [ring_simpify] in [ring]. Z nekaj poskušanja ugotovimo, da je pravo
       zaporedje [compute] in [ring]. *)
       compute.
       ring.
Qed.

(** Naslednjo vajo naredite sami. Ideja: x^4 je treba napisati kot Rsqr (x^2). *)
Theorem vaja_2 : forall x : R, 0 <= x^4.
Proof.
  intros.
  replace (x^4) with (Rsqr (x^2)).
   - apply Rle_0_sqr.
   - unfold Rsqr.
     ring.
Qed.

(** Iskanje po spletnih straneh je lahko precej zamudno. V Coq-u lahko
    iščemo tudi z ukazi:

    - [SearchAbout Rsqr] poišče vse izreke, ki omenjajo [Rsqr].
    - [SearchAbout "+"] poišče vse izreke, ki omenjajo "+" (tu podamo kar notacijo,
      lahko bi tudi rekli [SearchAbout Rplus]).
    - [SearchAbout (Rsqr (?x - ?y))] poišče vse izreke, v katerih se pojavi izraz
       oblike "Rsqr (?x - ?y)", kjer sta ?x in ?y poljubna. V splošnem lahko
       napišemo poljuben vzorec, kjer z ?x, ?y, ... označimo tiste dele vzorca,
       ki so poljubni.

    Polna dokumentacija za [SearchAbout] in [SearchPattern] je na 
    http://coq.inria.fr/V8.2pl1/refman/Reference-Manual009.html#@command105

    Ukaz [SearchPattern vzorec] sprejme vzorec in vrne vse izreke, katerih
    *sklep* ustreza danemu vzorcu.
*)
(** Naslednje vaje reši s pomočjo ukaza [SearchAbout]. Vsaka od vaj je rešljiva
    s preprosto uporabo [apply] izreka iz knjižnice. *)

Theorem vaja_3 (x : R) : 0 < Rsqr x -> x <> 0.
Proof.
  (* Uporabi: SearchAbout Rsqr. *)
  SearchAbout Rsqr.
  apply Rsqr_gt_0_0.
Qed.

Theorem vaja_4 (x : R) : x < x + 1.
Proof.
  (* Uporabi: SearchPattern (?x < ?x + 1). *)
  SearchPattern (?x < ?x + 1).
  apply Rlt_plus_1.
Qed.

Theorem vaja_5 (x : R) : sin (2 * x) = 2 * sin x * cos x.
Proof.
  (* SearchAbout (sin (2 * ?x)). *)
  SearchAbout (sin (2 * ?x)).
  apply sin_2a.
Qed.

(** Tu je še nekaj bolj zanimivih vaj. Pomagajte si s [SearchAbout]
    in [SearchPattern]. *)

Theorem vaja_6 : forall x : R, 0 < x -> 0 < x * x * x.
Proof.
  SearchAbout (0 < ?x -> 0 < ?y).
  intros.
  apply Rmult_lt_0_compat.
  apply Rmult_lt_0_compat.
  assumption.
  assumption.
  assumption.
Qed.

Theorem vaja_7 (x : R) : sin (3 * x) = 3 * (cos x)^2 * sin x - (sin x)^3.
Proof.
  replace (3*x) with ((2*x) + x).
   - replace (sin (2*x +x)) with (sin(2*x)*cos(x)+ cos(2*x)*sin(x)).
     + replace (sin(2*x)) with (2*sin(x)*cos(x)).
       replace (cos(2*x)) with (Rsqr(cos(x)) - Rsqr(sin(x))).
       * unfold Rsqr.
         ring.
       * symmetry.
         apply cos_2a.
       * symmetry.
         apply sin_2a.
     + SearchAbout (?x = ?y -> ?y = ?x).
       symmetry.
       apply sin_plus.
   - ring.
Qed.

Theorem vaja_8 (x y : R) :
  0 <= x -> 0 <= y -> Rabs (x + y) = Rabs x + Rabs y.
Proof.
  SearchAbout (0 <= ?x -> Rabs ?x = ?x).
  intros.
  replace (Rabs(x+y)) with (x+y).
  replace (Rabs(x)+Rabs(y)) with(x+y).
  - auto.
  - replace (Rabs(x)) with x.
    replace (Rabs(y)) with y.
    + auto.
    + symmetry.
      apply Rabs_pos_eq.
      assumption.
    + symmetry.
      apply Rabs_pos_eq.
      assumption.
  - symmetry.
    apply Rabs_pos_eq.
    SearchAbout (0 <= ?x -> 0 <= ?y -> 0 <= ?x + ?y).
    apply Rplus_le_le_0_compat.
    assumption.
    assumption.
Qed.

Theorem vaja_9 : forall x : R, x <= 0 -> x * x * x <= 0.
Proof.
  SearchPattern ( ?x * ?y <= ?z).
  intros.
  replace (x*x*x) with (x*Rsqr(x)).
  replace (0) with (0 * Rsqr(x)).
   - SearchPattern ( ?x * ?y <= ?z).
     apply Rmult_le_compat_r.
      +  apply Rle_0_sqr.
      + assumption.
   - ring.
   - unfold Rsqr.
     ring.
Qed.

Theorem vaja_10 : forall x : R, 0 < x * x * x -> 0 < x.
Proof.
  intros.
  SearchPattern (0 < ?x * ?y ).
  replace (x) with (x*x*x*/(x*x)).
  - apply Fourier_util.Rlt_mult_inv_pos.
    + assumption.
    + assert (x <> 0).
      * (*kako je že protislovej?*) 
  - SearchPattern (0 < ?x * ?y ).
    compute.
Qed.
