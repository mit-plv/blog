==============================
 Computing with opaque proofs
==============================

:tags: dependent-types, tricks
:category: Coq
:authors: Clément Pit-Claudel
:summary: Computations with dependent types often get stuck on rewrites that use opaque lemmas.  When the corresponding equality is decidable, these lemmas don't need to be made transparent to unblock computation.

.. preview::

   .. coq:: none

      Require Coq.Vectors.Vector.
      Require Import Coq.Strings.String Coq.Arith.PeanoNat.

   A fairly common occurrence when working with dependent types in Coq is to call `Compute` on a benign expression and get back a giant, partially-reduced term, like this:

   .. coq:: unfold

      Import EqNotations Vector.VectorNotations.
      Compute (Vector.hd (rew (Nat.add_1_r 3) in ([1; 2; 3] ++ [4]))).

   This post shows how to work around this issue.

First, a bit of background.  In Coq, constants (like theorems and definitions) come in two flavors: *unfoldable* (also known as *transparent*), and *opaque*.  This distinction is particularly relevant when performing δ-reduction: transparent constants (introduced using  `Definition`, `Fixpoint`, `Let`, etc., or by closing a proof using  `Defined`) can be unfolded, while opaque ones (introduced by closing a proof with `Qed`) are left untouched (unfolding a constant means replacing its name by its body).  In other words, opaque constants are treated very similarly to axioms for computation purposes; according to the manual, …

   … this is to keep with the usual mathematical practice of proof irrelevance: what matters in a mathematical development is the sequence of lemma statements, not their actual proofs. This distinguishes lemmas from the usual defined constants, whose actual values are of course relevant in general.

Concretely, here is how the distinction manifests itself:

.. coq::

   Definition transparent : nat := 1 + 1.
   Compute transparent. (* .unfold *)

   Lemma opaque : 1 + 1 = 2. Proof. auto. Qed.
   Compute opaque. (* .unfold *)

This distinction is usually harmless, but it can bite when working with dependent types, which tend to blur the lines between “lemmas” and “defined constants”.  Let's look at an example in more detail.  Coq's Vector library provides a function `Vector.cons: forall {A}, A -> forall {n}, Vector.t A n -> Vector.t A (1 + n)` to prepend a single element to a vector, but no corresponding function `snoc` to *append* a single element to a vector.  There *is* a function `Vector.append: forall {A} {n p}, Vector.t A n -> Vector.t A p -> Vector.t A (n + p)` though, so it's almost enough to define `snoc` as `fun v a => v ++ [a]`.  If we want `snoc` to have the same type as `cons`, we'll just have to add a type cast, because the type of `v ++ [a]` is `Vector.t nat (n + 1)`, and `n + 1` and `1 + n` are not unifiable.  No big deal:

.. coq::

   Definition snoc {A n} (a: A) (v: Vector.t A n)
     : Vector.t A (S n) :=
     (* [Nat.add_1_r] has type [forall n : nat, n + 1 = S n] *)
     rew (Nat.add_1_r n) in (v ++ [a]).

.. note::

   In this definition I used the `rew` notation (a convenient way to write casts).  Here's a version using the `rewrite` tactic instead:

   .. coq::

      Definition snoc_proofmode {A n} (a: A) (v: Vector.t A n)
        : Vector.t A (S n).
      Proof.
        rewrite <- Nat.add_1_r.
        exact (v ++ [a]).
      Defined.

But now look at what happens if I actually try to compute with this function!

.. coq::

   Compute (Vector.map (fun x => 2 * x) (snoc 4 [1; 2; 3])). (* .unfold *)

Agh.  Could we maybe *prove* that `Vector.map (fun x => 2 * x) (snoc 4 [1; 2; 3])` equals `[2; 4; 6; 8]`, instead of using compute?

.. coq::

   Lemma map_snoc_1234 :
     Vector.map (fun x => 2 * x) (snoc 4 [1; 2; 3]) = [2; 4; 6; 8].
   Proof.

`reflexivity` fails, for the same reason that `Compute` got stuck:

.. coq::

     Fail reflexivity. (* .unfold .no-goals *)

And if I try to simplify things to figure out where I'm stuck, I get exactly where `Compute` took me before:

.. coq:: unfold

     cbv -[Vector.map Nat.mul eq_rect].
     unfold eq_rect.

The problem is that the proof of `Nat.add_1_r` is opaque, so `cbv` can't reduce it.  If you look carefully at the large term from earlier, you'll see that it, too, was blocked on `(Nat.add_1_r n)`.

.. coq::

   Abort.

.. topic:: Finishing the proof without redefining `Nat.add_1_r`

   You might think that `destruct` would help: isn't that how you make a `match` reduce?

   .. coq::

      Lemma map_snoc_1234 :
        Vector.map (fun x => 2 * x) (snoc 4 [1; 2; 3]) = [2; 4; 6; 8].
      Proof.
        cbv -[Vector.map Nat.mul].
        Fail destruct (Nat.add_1_r 3). (* .unfold .no-goals *)
      Abort.

   … apparently not.  When you first see this error, it usually feels a bit disorienting.  We can get a bit closer by swapping the rewrite and the map:

   .. coq:: none

      Lemma map_app {A B} (f: A -> B):
        forall {n1} (v1: Vector.t A n1)
               {n2} (v2: Vector.t A n2),
          Vector.map f (v1 ++ v2) =
          Vector.map f v1 ++ Vector.map f v2.
      Proof. induction v1; cbn; congruence. Qed.

   .. coq:: unfold

      Lemma snoc_map {A B n} :
        forall (v: Vector.t A n) (f: A -> B) a,
          Vector.map f (snoc a v) =
          snoc (f a) (Vector.map f v). (* .fold *)
      Proof. (* .fold *)
        intros; unfold snoc.
        destruct (Nat.add_1_r n).

   (A puzzle: why did *this* destruct work, unlike the previous one?)

   .. coq::

        cbn.
        rewrite map_app. (* .unfold *)
        reflexivity.
      Qed.

   With this, we're tantalizingly close:

   .. coq::

      Lemma map_snoc_1234 :
        Vector.map (fun x => 2 * x) (snoc 4 [1; 2; 3]) = [2; 4; 6; 8].
      Proof.
        rewrite snoc_map.
        cbv. (* .unfold *)

   … agh!  A useless rewrite!  Get it off!

   .. coq:: unfold no-goals

        Fail destruct (Nat.add_1_r 3).

   … agh!

   Turns out you need a pretty powerful theorem to get yourself out of this mess.  Because equality on natural numbers is decidable, it's possible to prove that there's just one proof of `4 = 4`, namely `eq_refl`.  With that proof, we can rewrite `(Nat.add_1_r 3)` into `eq_refl`:

   .. coq:: unfold

        rewrite (Eqdep_dec.UIP_refl_nat _ (Nat.add_1_r 3)).
        reflexivity.
      Qed.

   Of course, that doesn't help with making `Compute` reduce, since `Compute` applies a limited set of reduction rules (it doesn't do rewrites).

The usual fix is to make every proof that might be used in a computation transparent; something like this:

.. coq::

   Lemma add_1_r_transparent_proofmode (n: nat) : n + 1 = S n.
   Proof.
     induction n.
     - reflexivity.
     - cbn.
       rewrite IHn.
       reflexivity.
   Defined. (* [Defined] makes the proof transparent *)

Equivalently, we can write the proof as a recursive function, which makes the fact that it always reduces to `eq_refl` pretty obvious (the second match could also be written as `rew [fun y => S n + 1 = S y] (add_1_r_transparent n) in eq_refl`):

.. coq::

   Fixpoint add_1_r_transparent (n: nat)
     : n + 1 = S n :=
     match n with
     | 0 => eq_refl
     | S n =>
       match add_1_r_transparent n in (_ = y)
         return (S n + 1 = S y) with
       | eq_refl => eq_refl
       end
     end.

… and with this, we can get a definition that computes properly:

.. coq::

   Definition snoc_computational {A n} (a: A) (v: Vector.t A n)
     : Vector.t A (S n) :=
     rew (add_1_r_transparent n) in (v ++ [a]).

.. coq:: unfold

   Compute (Vector.map (fun x => 2 * x)
                       (snoc_computational 4 [1; 2; 3])).

The problem with this approach is that this change needs to be done recursively: you would need to replace `Qed` with `Defined` in the definition of all lemmas that you depend on.  Not ideal.

Instead, here's a cool trick:

.. coq::

   Definition computational_eq {m n} (opaque_eq: m = n) : m = n :=
     match Nat.eq_dec m n with
     | left transparent_eq => transparent_eq
     | _ => opaque_eq (* dead code; could use [False_rect] *)
     end.

.. coq::

   Definition snoc' {A n} (a: A) (v: Vector.t A n) :=
     rew (computational_eq (Nat.add_1_r n)) in (v ++ [a]).

.. coq:: unfold

   Compute (Vector.map (fun x => 2 * x) (snoc' 4 [1; 2; 3])).

🎉️. Here is why this works: in the definition of `snoc`, all that I really need is to have *some* transparent proof that `n + 1` equals `1 + n` — I don't really care which one.  So, because equality is decidable on `nat`, I can just ignore the opaque proof returned by `Nat.add_1_r`, and rebuild a fresh, transparent one using `Nat.eq_dec`.

More precisely, for any given `m` and `n`, one way to construct a proof that `m = n` is to compare the two numbers, using a recursive comparison function (that's what `Nat.eq_dec` is, above; importantly, it returns transparent proofs).  If the comparison succeeds, it returns a transparent equality proof (`eq_refl`) that `computational_eq` returns, allowing computation to proceed.

For arbitrary `m` and `n`, values, the comparison could fail.  But in `computational_eq`, it can't: `computational_eq` takes a proof that its first two arguments are equal, so the second branch of the match is dead code, and the opaque proof isn't computationally relevant anymore.

The key here is that `Nat.eq_dec` builds a transparent proof, so there's really nothing magical happening — all we're doing is discarding potentially opaque equality proofs on `nat`\s and replacing them with a canonical one that we know to be transparent.  The big gain is that we only have to define `Nat.eq_dec` once, instead of having to make all equality proofs transparent.

.. note::

   This issue (computations blocking on equality proofs) highlights one way in which `eq` (and other singleton inductives in Prop) are special in Coq.  If you think about it, it's a bit weird that we even run into this problem at all: since Coq's `Prop`\s are erasable, shouldn't be computationally irrelevant?  If so, how can they block computation?

   It turns out that singleton (and empty) definitions are `special-cased <https://coq.inria.fr/refman/language/cic.html#empty-and-singleton-elimination>`, because they allow useful patterns like typecasts without breaking `Prop` erasure or extraction.  In constrast, Coq prevents other `Prop`\s from being used in any context except to derive a contradiction (that is, as an argument to `False_rect`): that's why the problem only pops up with `eq` and similar `Prop`\s, and why the following example computes without blocking (it never really uses the proof, in the same way that `computational_eq` above never really uses its argument proof):

   .. coq:: unfold

      Compute (@Fin.of_nat_lt 3 4 (PeanoNat.Nat.lt_succ_diag_r 3)).

.. topic:: Computational complexity

   There's something slightly worrying about discarding old proofs to build new ones — aren't we going to be wasting cycles building those new proofs?

   In most cases, not really: `Nat.eq_dec` is linear in its first argument, so it could be slow, but so is our transparent replacement for `Nat.add_1_r`! (`add_1_r_transparent` builds a trivial term, `eq_refl`, but it builds it recursively, traversing its whole argument.)

   Worse, if the proof that we're discarding is built from complex lemmas, discarding it instead of normalizing a transparent variant of it can save quite a bit of time.

   Ultimately, it depends on the reduction strategy, on the actual proof that we're discarding, and on its opacity.  If we reduce in lazy or call-by-need style, the original proof won't be reduced at all.  In call-by-value style, however, we can run into issues: the reduction of `computational_eq pr` will start by reducing `pr`, so in the example above we'll normalize *both* `Nat.eq_dec` and the original proof passed to `computational_eq`.  There are two workarounds:

   - Thunk the original proof (that is, wrap it in a function): `cbv` only reduces arguments to weak-head normal form, so the thunk won't be reduced).

     .. coq::

        Definition computational_eq_cbv {m n: nat}
            (thunked_eq: unit -> m = n) : m = n :=
          match Nat.eq_dec m n with
          | left transparent_eq => transparent_eq
          | _ => thunked_eq tt
          end.

   - Make the original proof opaque.  Ironically, since opacity blocks reduction, the normal form of `Nat.add_1_r` is precisely `Nat.add_1_r`, so we won't run into the double-reduction issue as long as the proof we're passing to `computational_eq` is opaque.

   When extracting to OCaml, none of this matters: `computational_eq` is erased:

   .. coq:: unfold

      Require Import Extraction. (* .none *)
      Extraction computational_eq.
