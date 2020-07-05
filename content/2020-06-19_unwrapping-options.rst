========================================================
 How to write a type-safe ``unwrap`` (aka ``fromJust``)
========================================================

:tags: dependent-types, tricks
:category: Coq
:authors: Clément Pit-Claudel
:summary: Tips and tricks for writing functions that take proofs as arguments.

.. coq:: none

   Require Coq.Strings.String Coq.Lists.List Coq.Arith.Arith.
   Import String Arith List.ListNotations.
   Open Scope list_scope.

.. coq:: none

   Require Import Coq.Bool.Bool.

   Inductive UntypedAST : Type :=
   | UNat (n: nat)
   | UBool (b: bool)
   | UAdd (e1 e2: UntypedAST)
   | UAnd (e1 e2: UntypedAST).

   Inductive Tau :=
   | Nat
   | Bool.

   Fixpoint Value' (tau: Tau) :=
     match tau with
     | Nat => nat
     | Bool => bool
     end.

   Inductive TypedAST' : Tau -> Type :=
   | TNat (n: nat) : TypedAST' Nat
   | TBool (b: bool) : TypedAST' Bool
   | TAdd (e1 e2: TypedAST' Nat): TypedAST' Nat
   | TAnd (e1 e2: TypedAST' Bool): TypedAST' Bool.

   Record TypedAST :=
     { tau: Tau; ast: TypedAST' tau }.

   Fixpoint typecheck (ast: UntypedAST) : option TypedAST :=
     match ast with
     | UNat n => Some {| ast := TNat n |}
     | UBool b => Some {| ast := TBool b |}
     | UAdd e1 e2 =>
       match typecheck e1, typecheck e2 with
       | Some {| tau := Nat; ast := t1 |},
         Some {| tau := Nat; ast := t2 |} =>
         Some {| ast := TAdd t1 t2 |}
       | _, _ => None
       end
     | UAnd e1 e2 =>
       match typecheck e1, typecheck e2 with
       | Some {| tau := Bool; ast := t1 |},
         Some {| tau := Bool; ast := t2 |} =>
         Some {| ast := TAnd t1 t2 |}
       | _, _ => None
       end
     end.

   Fixpoint interp' {tau} (ast: TypedAST' tau) : Value' tau :=
     match ast with
     | TNat n => n
     | TBool b => b
     | TAdd e1 e2 => interp' e1 + interp' e2
     | TAnd e1 e2 => interp' e1 && interp' e2
     end.

   Record Value :=
     { vtau: Tau; val: Value' vtau }.

   Definition interp (t: TypedAST) : Value :=
     {| val := interp' t.(ast) |}.

   (* Arguments Value {tau} : assert. *)

.. preview::

   Let's say you've written a programming language in Coq.  You have nice inductives for your ASTs; one for untyped terms (`UntypedAST`) and one for typed terms (`TypedAST`).  You wrote a simple typechecker, and maybe an interpreter, too!

   .. coq:: unfold out

      Check typecheck.
      Check interp.

   You write a few programs…

   .. coq::

      Example well_typed := UAdd (UNat 1) (UNat 1).
      Example ill_typed := UAdd (UNat 1) (UBool true).

   … typecheck them:

   .. coq:: unfold

      Definition tc_good := typecheck well_typed.
      Compute tc_good. (* Accepted: So far so good. *)

      Definition tc_bad := typecheck ill_typed.
      Compute tc_bad. (* Rejected: all good as well. *)

   … and attempt to run them:

   .. coq:: unfold

      Fail Compute interp tc_good. (* .fails *)

   D'oh!  `interp` takes a `TypedAST`, but `typecheck` returns an `option`.  What do we do?

We can write a simple wrapper though, with a default value for the `None` case:

.. coq::

   Definition unwrap_default (o: option TypedAST) : TypedAST :=
     match o with
     | Some t => t
     | None => {| ast := TNat 1 |}
     end.

   Compute interp (unwrap_default tc_good). (* .unfold *)

But now we silently swallow type errors, which isn't ideal:

.. coq::

   Compute interp (unwrap_default tc_bad). (* .unfold *)

Let's see how we can get a safe but convenient version of `unwrap` (aka ``fromJust`` in the Haskell world and ``Option.get`` in OCaml).

Take 1: Pass a proof as an extra argument
=========================================

The most straightforward way is to generalize `unwrap` by adding a proof that its argument is not `None`:

.. coq::

    Definition unwrap {A} (o: option A)
               (not_none: o <> None) : A :=
      match o return _ = o -> A with
      | Some a => fun _ => a
      | None => fun is_none => False_rect _ (not_none is_none)
      end eq_refl.

… it works, but it's not much fun for callers:

.. coq:: unfold

   Compute interp (unwrap tc_good
     (fun some_eq_none =>
       @eq_rect_r (option TypedAST) None
                  (fun o: option TypedAST =>
                     if o then False else True)
                  I tc_good some_eq_none)).

We can improve things slightly with tactics in terms:

.. coq:: unfold

   Compute interp (unwrap tc_good ltac:(discriminate)).
   Fail Compute interp (unwrap tc_bad ltac:(discriminate)). (* .fails *)

… but the generated terms are not pretty, so if you ever store them unreduced anywhere, you're in for all sorts of unpleasantness:

.. coq:: unfold

   Check (unwrap tc_good ltac:(discriminate)).

Not great.  Still, here is another example for comparison, this time using known-good indices into a list:

.. coq::

   Definition nth_in_bounds {A} (l: list A) (n: nat)
              (in_bounds: n < List.length l) :=
     unwrap (List.nth_error l n)
            (proj2 (List.nth_error_Some l n) in_bounds).

   Compute nth_in_bounds [1; 2; 3] 2
              ltac:(repeat constructor). (* .unfold *)

Note that (maybe surprisingly) the computation doesn't block, despite the fact that the definition of `nth_in_bounds` uses an opaque proof `List.nth_error_Some`.  The reason is that, as we've seen, `unwrap` doesn't actually look at the proof.  In fact, in general, proofs don't tend to block computation, because Coq disallows elimination of informative `Prop`\s into type (that is, programs that return non-`Prop` results can't inspect proofs — except non-informative ones, `like eq_refl`_).

.. |like eq_refl| replace:: like `eq_refl`
.. _like eq_refl: {filename}/2020-06-17_computing-with-opaque-proofs.rst

.. sidebar:: Skipping the proof entirely

   What happens if we just skip the proof completely?

   .. coq:: unfold

      Compute interp (unwrap tc_good _).

   Huh?

   The reason this works is that the definition of `unwrap` never really uses the proof — it only refers to it when deriving a contradiction, in the `None` branch — but the proof guarantees that this branch is unreachable!  Writing (unwrap tc_good _) produces an open term (a term with holes), but `Compute` knows how to reduce those, so it proceeds without complaining.

   Of course, trying to unwrap `None` doesn't go as smoothly: instead, `Compute` blocks on the unspecified proof that `None <> None`:

   .. coq:: unfold

      Compute (unwrap None _).

   The main downside of this `_` trick is that it cannot easily be used in definitions:

   .. coq:: unfold

      Fail Definition good := (* .fails *)
        Eval compute in interp (unwrap tc_good _).

   Oh well.  Still a nice party trick.

Take 2: Use an equality proof
=============================

The main pain point in the previous example was the complexity of the proof terms, so let's simplify them.  Instead of proving `o <> None`, we'll prove that `is_some o = true`, and the proof will always be `eq_refl`:

.. coq::

    Definition is_some {A} (o: option A) : bool :=
      if o then true else false.

    Lemma is_some_not_none {A} {o: option A} :
      is_some o = true -> o <> None.
    Proof. destruct o. all: cbn. all: congruence. Qed.

.. note::

   In Coq the `if _ then _ else _` notation works for any inductive type with two constructors, not just Booleans: the first constructor triggers the true case, and the second one triggers the false case.  Conveniently, the definition of the `option` type in Coq puts `Some _` first and `None` second, so it works intuitively with `if`\s.

   On the other hand, the definitions of `nat`, `list`, and `String` put the base case first, which means that `0`, `[]`, and `""` are truthy in Coq (`Compute (if 0 then true else false)` reduces to `true`), while `42`, `[1; 2; 3]`, and `"coq"` are falsy (`Compute (if "coq" then true else false)` reduces to `false`) — a slightly unfortunate result.

Now we can define a new variant of `unwrap`:

.. coq::

    Definition unwrap_dec {A} (o: option A)
               (is_some_true: is_some o = true) : A :=
      unwrap o (is_some_not_none is_some_true).

    Compute interp (unwrap_dec tc_good eq_refl). (* .unfold *)

Much nicer!  Now the proof is always the same, and we can even define a notation to hide it:

.. coq::

   Notation unwrap_dec' o := (unwrap_dec o eq_refl).

Here's how it looks for list indices:

.. coq::

   Definition nth_in_bounds_dec {A} (l: list A) (n: nat)
              (lt_true: (n <? List.length l) = true) :=
     nth_in_bounds l n (proj1 (Nat.ltb_lt _ _) lt_true).

     Compute nth_in_bounds_dec [1; 2; 3] 2 eq_refl. (* .unfold *)

One significant advantage of this strategy is that we can control the reduction strategy used to check that `eq_refl` has the right type (ensuring that the application of `unwrap_dec` is well-typed requires checking that `eq_refl: is_some _ = true`, which requires reducing `is_some _` to unify it with `true`).  Concretely, we can write `(@eq_refl bool true : is_some tc_good = true)` to using normal unification, `(@eq_refl bool true <: …)` to call `vm_compute`, and `<<:` to call `native_compute`.

As before, though, the proof term that we're passing is in fact dead code, and the error messages are not ideal:

.. coq:: unfold

   Compute interp (unwrap_dec tc_good _).
   Fail Compute interp (unwrap_dec None eq_refl). (* .fails *)
   Compute interp (unwrap_dec None _).

Take 3: Use a dependent return type
===================================

We know that we only intend to call `unwrap` with arguments that reduce to `Some _`.  We can make this explicit in the *return* type, instead of changing the arguments:

.. coq::

   Inductive error : string -> Type := Err (s: string) : error s.

   Definition unwrap_dep {A} (o: option A)
     : if o then A else error _ :=
     match o with
     | Some a => a
     | None => Err "Expecting Some, got None"
     end.

   Compute interp (unwrap_dep tc_good). (* .unfold *)

Here we're saying that we'll return an `A` if given a `Some`, and an `error` otherwise.  And indeed, the error messages are much nicer:

.. coq:: unfold

   Fail Compute interp (unwrap_dep tc_bad). (* .fails *)

Here's how it looks for list indices:

.. coq::

   Definition nth_in_bounds_dep {A} (l: list A) (n: nat)
     : if lt_dec n (List.length l) then A else error _ :=
     match lt_dec n (List.length l) as cmp
       return (if cmp then A else error _) with
     | left in_bounds => nth_in_bounds l n in_bounds
     | right _ => Err "Index is out of bounds"
     end.

.. coq:: unfold

   Compute nth_in_bounds_dep [1; 2; 3] 2.
   Compute nth_in_bounds_dep [1; 2; 3] 7.

.. sidebar:: Reducing types as well as terms

   The commands above reduce values, but not their types: notice how the type of `nth_in_bounds_dep [1; 2; 3] 2`, for example, is printed as `if lt_dec 2 (Datatypes.length [1; 2; 3]) then nat else error …`.  If you want to reduce types as well, the simplest is to use tactics-in-terms:

   .. coq::

      Notation compute_all term :=
        ltac:(let term := (eval compute in term) in
              exact_no_check term) (only parsing).

      Check (compute_all (nth_in_bounds_dep [1; 2; 3] 2)). (* .unfold *)

   The `ltac:(…)` parts says that we're going to derive a term using a proof script, and the call to `exact_no_check` supplies the term that we want, which we obtained using the `eval` Ltac primitive.

   **A puzzle for expert readers:** Is it possible to write a version of this simplification tactic which reduces *just* the type (not the term) without adding a type annotation?  In other words, can you do better than the following, which leaves a cast in the term?

   .. coq::

      Notation compute_in_type term :=
        ltac:(let type := type of term in
              let type := (eval compute in type) in
              exact_no_check (term: type)) (only parsing).

      Check (compute_in_type (nth_in_bounds_dep [1; 2; 3] 2)). (* .unfold *)

   (The only way that I know is using a `Definition` or a `let` binding.)

Bonus 1: Using unification
==========================

After I wrote this post, my colleague Jason Gross showed me another quite clever implementation of `unwrap`, leveraging inference:

.. coq::

   Notation unwrap_refl o :=
     ((fun v (pf : o = Some v) => v) _ eq_refl) (only parsing).

   Compute unwrap_refl tc_good. (* .unfold *)

The trick here is to force unification to infer the value inside the option: Coq will unify `o = Some ?v` (the type of `pf`) with `?a = ?a` (the type of `eq_refl`), and instantiate `?v` in passing, which the function then returns.  Nifty!

Bonus 2: Using tactics in terms
===============================

Here's one final way to proceed with this, using tactics in terms:

.. coq::

   Notation unwrap_tac opt :=
     ltac:(match (eval hnf in opt) with
           | Some ?v => exact v
           | ?other => fail "Error:" other "isn't [Some _]"
           end) (only parsing).

In practice, it works OK, but `hnf` is very slow (it's based on the same code as `simpl`). The `cbv` tactic and its faster cousins like `vm_compute` and `native_compute` are usually faster, but they get very costly if the terms are large and don't need to be fully normalized to determine whether we're in the `Some` or `None` case (think of a case like `Some (very large term)`, where `hnf` will be free and `cbv` very slow).

Knowing this, it's a bit easier to understand why the `unwrap_dec` trick above works well: the type check that ensures that `eq_refl` has type `is_some opt = true` is essentially computing the head-normal form of opt and comparing it to `Some`, but it does that using Coq's fast reduction tactics.  In fact, Jason has done a lot of work on exploring alternative strategies that combine reflection and fast full-reduction tactics such as `vm_compute` or `native_compute` to give `fine-grained control over reduction <https://github.com/mit-plv/rewriter>`_.

.. note::

   Jason correctly points out that this notation won't give you great error messages if you pass it terms with typos:

   .. coq:: unfold fails

      Fail Compute (unwrap_tac (Som 1)).

   One way around this is to tweak the notation to force it to typecheck its argument before passing it into the tactic, like this:

   .. coq::

      Notation unwrap_tac' opt :=
        (match opt with _ =>
         ltac:(match (eval hnf in opt) with
               | Some ?v => exact v
               | ?other => fail "Error:" other "isn't [Some _]"
               end) end) (only parsing).

      Fail Compute (unwrap_tac' (Som 1)). (* .fails .unfold *)

   Using a `match` instead of another construct like `let _ := opt in …` ensures that we don't pollute the term (the match will self-reduce without requiring an explicit reduction).
