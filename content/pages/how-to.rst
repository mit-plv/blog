=======================
 How to read this blog
=======================

:author: Clément Pit-Claudel
:slug: how-to
:status: hidden

Many of the pages in this blog have Coq proofs embedded in them, like this:

.. coq:: none

   Inductive Even : nat -> Prop :=
   | EvenO : Even O
   | EvenS : forall n, Even n -> Even (S (S n)).

   Fixpoint even (n: nat): bool :=
     match n with
     | 0 => true
     | 1 => false
     | S (S n) => even n
     end.

.. coq::

   Fixpoint even_Even_fp (n: nat):
     even n = true <-> Even n.
   Proof.
     destruct n as [ | [ | n ] ].
     all: cbn.
     - (* n ← 0 *)
       split; intros.
       all: constructor.
     - (* n ← 1 *)
       split.
       all: inversion 1.
     - (* n ← S (S _) *)
       split.
       all: (constructor || inversion 1).
       all: apply even_Even_fp.
       all: assumption.
   Qed.

Coq is a *Proof Assistant* that makes heavy use of *tactics* to create proofs.  As a result, Coq proofs are usually not so readable without seeing the intermediate goals that Coq normally displays.

.. coq:: none

   Require Import Coq.Strings.String Coq.Arith.Arith
           Coq.setoid_ring.ArithRing Coq.Bool.Bool.
   Open Scope string_scope.

   Definition rot13c c :=
     let n := Ascii.nat_of_ascii c in
     let n' :=
       if (65 <=? n) && (n <=? 90) then
         65 + (n - 65 + 13) mod 26
       else if (97 <=? n) && (n <=? 122) then
         97 + (n - 97 + 13) mod 26
       else
         n in
     Ascii.ascii_of_nat n'.

   Fixpoint rot13 msg :=
     match msg with
     | EmptyString => EmptyString
     | String c s => String (rot13c c) (rot13 s)
     end.

On this website, you'll notice small bubbles (like this :alectryon-bubble:`_`) next to some of the code.  These bubbles indicate Coq fragments (sentences) that you can interact with.  Try hovering over the sentences below:

.. coq::

   Compute (rot13 "Uryyb, jbeyq!").
   Search (_ + _ = _ -> _ = _).

Clicking on a sentence will inline Coq's output and make it persistently visible.  This is convenient when comparing steps of a proof.  Try it on the unnecessarily long sequence of proof steps below:

.. coq:: none

   Fixpoint sum upto :=
     match upto with
     | O => 0
     | S upto' => upto + sum upto'
     end.

.. coq::

   Lemma Gauss:
     forall n, 2 * (sum n) = n * (n + 1).
   Proof.
     intros.
     induction n.
     - (* n ← 0 *) reflexivity.
     - (* n ← S _ *)
       cbn [sum].
       rewrite Mult.mult_plus_distr_l.
       rewrite IHn.
       change (S n) with (1 + n).
       rewrite !Mult.mult_plus_distr_l, !Mult.mult_plus_distr_r.
       cbn [Nat.mul]; rewrite !Nat.mul_1_r, !Nat.add_0_r.
       rewrite !Nat.add_assoc.
       change (1 + 1) with 2.
       rewrite !(Nat.add_comm _ 1), !Nat.add_assoc.
       change (1 + 1) with 2.
       Show Existentials. (* .no-goals *)
       reflexivity.
   Qed.

One final way to interact with the proofs is using the keyboard, in a style similar to Proof General or CoqIDE.  Try pressing :kbd:`Ctrl+↓` and :kbd:`Ctrl+↑`; you will be taken back to the beginning of this article and shown goals and responses at each step.  You can also click on a sentence while holding :kbd:`Ctrl` (or :kbd:`Cmd` on macOS) to focus on a given goal.

I plan to write about the system that powers this blog in the future.  For now, happy hacking!
