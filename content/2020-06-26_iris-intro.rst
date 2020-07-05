==============================
 A brief introduction to Iris
==============================

:tags: iris, concurrency, guest-post
:category: tutorial
:authors: Tej Chajed
:summary: Introduction to concurrency reasoning in the Iris framework, using a
          bank as an example program.

.. preview::

  `Iris <iris home_>`_ is a powerful framework for doing concurrency reasoning.
  In the `PDOS group <pdos_>`_ we've been using it to verify concurrent storage
  systems, including reasoning about code implemented in Go. Iris stands out
  among concurrency frameworks in my mind for two reasons: it is extremely
  modular, allowing us to adapt it to a setting quite different from its
  original purposes; and it is extremely well-engineered, allowing us to work
  with it as a library rather than re-implement it. Iris stands out, especially
  among Coq frameworks, for how *usable* it is.

  .. _iris home: https://iris-project.org/
  .. _pdos: https://pdos.csail.mit.edu/

  Iris is also, unfortunately, a beast to learn. It can be hard to tell where to
  start, hard to figure out what Iris even is, and hard to appreciate why Iris is
  such a good framework. In this post we'll work through a sort of "hello, world"
  example of concurrency verification, proving it correct in Iris. My goal is to
  convince you that the underlying ideas are approachable and get you excited
  about Iris; if I succeed then you'll walk away appreciating Iris a bit
  more and maybe be curious enough to dive deeper into other material.

I'm explicitly not aiming to teach you how to do these proofs on your own - I
give some resources at the `bottom of the post <#what-to-try-next>`_ if you want
to go further and really learn how to use Iris.

This post will assume some knowledge of Hoare logic and Coq (if you want to
follow the proofs). The intention is that even if some of the separation logic
details don't make sense the intuition still comes through. Iris is built on top
of separation logic, though, so to really understand it you do need some
understanding of at least sequential separation logic.

.. _tutorial-popl18: https://gitlab.mpi-sws.org/iris/tutorial-popl18/

A simple proof about a bank
===========================

In this post we'll implement a sort of bank that stores user balances and allows
transfers between accounts. We want to show that in some sense transfers
preserve the sum of balances.

First, let's make a few drastic simplifications to focus on the essential
difficulty: we'll only have two accounts, and only transfer from one to the
other. The balances will be represented as mathematical integers Z and their sum
will be 0. We won't try executing this code, only proving it correct.

What's left is that we will still have a lock per account, acquiring both locks
to do a transfer. This still leaves a difficulty that the balances don't
necessarily sum to zero at every instant in time (for example, they might not
while a transfer is in progress); however, if we acquire both account locks, we
should observe a sum of 0. Thus we'll write a function that acquires both locks
and checks that the sum is zero. If we had more accounts, this check would have
to acquire all of the locks.

We won't prove anything else about the bank functionality or implement anything
else (like reading balances).

First, we'll import some stuff from Iris.

.. sidebar:: What is Iris?

   Many people get confused about this, largely because this isn't
   well-explained in any of the papers and everything is just called "Iris." The
   whole framework is itself highly modular, so here are the pieces we'll be
   using here:

   - The Iris base logic is a separation logic with the usual conjunction and magic
     wand but also ghost state, including impredicative ghost state (where the
     state can refer to arbitrary propositions), and step-indexing to avoid
     circularity when using impredicative ghost state. You don't need to worry
     about the internals of this logic (thankfully), but it's this logic
     that gives the power of basic features like invariants that can hold arbitrary
     propositions.
   - The Iris Proof Mode (IPM) is an embedded DSL for doing interactive proofs
     in separation logic. It works for a large variety of separation logics,
     including simple logics where predicates are just `heap -> Prop` and ranging
     up to the sophisticated Iris base logic. The IPM is actually mostly
     independent of Iris. The implementation only uses tactics and typeclasses
     and thus Iris does not require any Coq plugins.
   - Iris defines a program logic for a generic language interface, which
     specifies a language in terms of its expressions, values, and a small-step
     operational semantics. On top of this you get a weakest-precondition based
     program logic.
   - The Iris framework ships with HeapLang, an instantiation of the generic
     language interface which is fully set up: it has syntax for Hoare triples,
     proofs for all the primitives, and tactics for easier program proofs of
     weakest preconditions. You don't have to use HeapLang, particularly if you
     want to reason about real languages, but it requires the least setup.

   In this post I'll stick to using HeapLang. There's no way to extract and run
   programs in HeapLang, but there are other languages plugged into Iris that model
   real, executable languages, such as Rust, Go, and Scala.

.. coq::

   (* we'll use this library to set up ghost state later *)
   From iris.algebra Require Import lib.excl_auth.
   From iris.heap_lang Require Import proofmode notation.
   From iris.heap_lang.lib Require Import lock spin_lock.

.. coq:: none

   (* set some Coq options for basic sanity *)
   Set Default Proof Using "Type".
   Set Printing Projections.
   Set Default Goal Selector "!".
   Open Scope Z_scope.

   Set Warnings "-convert_concl_no_check".

Implementing the bank
=====================

In this post, we'll implement the bank in HeapLang, a simple default language
for Iris. HeapLang is a core functional language with mutable references that we
can write directly from Coq, with a set of notations to make the syntax
readable.

- We'll write HeapLang functions as Coq definitions of type `val`, which is a
  HeapLang value.
- Variables are represented as strings (and thus need to be quoted everywhere).
- `ref x` allocates a new reference with an initial value `x`.
- `#x` is overloaded to turn `x` into a value; we'll use it for integers
  (`Z` in Coq) and for the unit literal `#()`.
- `!l` dereferences a pointer l ("l" stands for "location").
- Many constructs have a colon to disambiguate them from the analogous Coq
  syntax, such as `let:` and `λ:`
- `λ: <>, ...` uses <> for an anonymous binder, much like `_` in Coq and
  other languages.
- This language has no static type system.

First we'll write a function to create a new bank. `new_bank` constructs a bank
with two accounts that both have zero balance, which initially satisfies the
desired invariant.

.. coq::

   Definition new_bank: val :=
     λ: <>,
        let: "a_bal" := ref #0 in
        let: "b_bal" := ref #0 in
        let: "lk_a" := newlock #() in
        let: "lk_b" := newlock #() in
       (* the bank is represented as a pair of accounts, each of which
       is a pair of a lock and a pointer to its balance *)
        (("lk_a", "a_bal"), ("lk_b", "b_bal")).

`transfer` moves money from the first to the second account (there's no check
that there's enough money, and we totally allow negative balances). We want to
prove this function is safe, but we won't prove that it actually modifies the
bank state correctly because that would require more setup. Note that we need to
be consistent about lock acquisition order to avoid the possibility of a
deadlock; proofs in Iris do not show that code terminates and hence deadlocks
are possible even for verified code.

.. coq::

   Definition transfer: val :=
     λ: "bank" "amt",
     let: "a" := Fst "bank" in
     let: "b" := Snd "bank" in
     acquire (Fst "a");;
     acquire (Fst "b");;
     Snd "a" <- !(Snd "a") - "amt";;
     Snd "b" <- !(Snd "b") + "amt";;
     release (Fst "b");;
     release (Fst "a");;
     #().

`check_consistency` is the core function of interest: we'll eventually prove
that even in the presence of `transfer`'s, this function always returns true.

.. coq::

   Definition check_consistency: val :=
     λ: "bank",
     let: "a" := Fst "bank" in
     let: "b" := Snd "bank" in
     acquire (Fst "a");;
     acquire (Fst "b");;
     let: "a_bal" := !(Snd "a") in
     let: "b_bal" := !(Snd "b") in
     let: "ok" := "a_bal" + "b_bal" = #0 in
     release (Fst "b");;
     release (Fst "a");;
     "ok".

To tie everything together we'll specifically prove that the following function
always returns true, which doesn't take any arguments and does all the setup
internally. The semantics of `Fork e` are to spawn a new thread running `e`, so
the call to `check_consistency` will race with `transfer`. Nonetheless we'll
still be able to prove the whole function always returns true.

.. coq::

   Definition demo_check_consistency: val :=
     λ: <>,
     let: "bank" := new_bank #() in
     Fork (transfer "bank" #5);;
     check_consistency "bank".

Proving the bank correct
========================

Before we can prove it correct, I should briefly talk about what the
specification is. To keep things simple, we're going to prove a Hoare triple
that says `demo_check_consistency` always returns true. However, it's possible
to prove theorems using Iris whose statement doesn't mention anything in the
Iris logic.

.. note::

   Iris isn't just for proving Hoare triples - it can be used to prove
   properties of languages with logical relations and refinement theorems. The
   key is that we can apply the Iris *adequacy theorem* to derive a theorem that
   "eliminates" the Iris logic.

   For example, if we can prove a Hoare triple whose precondition is true and
   whose conclusion is some pure fact `φ(v)` about the return value `v`,
   then if the function runs to a value `v` then `φ(v)` will indeed hold.
   The full adequacy theorem is more powerful than this, giving a way to talk
   about the intermediate behaviors of the program as well (something we would
   need in order to derive a refinement theorem).

Iris is based on separation logic, specifically a variant called *concurrent
separation logic*. If you haven't seen separation logic, here's a one-paragraph
summary: separation logic is a way of describing resources. A predicate `P` in
separation logic represents a collection of resources, which we'll also describe
as ownership of those resources. When reasoning about programs, a typical
resource that comes up is `l ↦ v`, which says pointer `l` points to value
`v` in memory and represents ownership of that location. A crucial idea of
separation logic is the *separating conjunction* `P ∗ Q` (pronounced "P and
separately Q", or just "P and Q" when you've worked in separation logic long
enough), which represents disjoint ownership of (resources satisfying the
predicate) `P` and `Q`. The CACM article `Separation logic <separation
logic_>`_ is an excellent and accessible overview.

.. _separation logic: https://cacm.acm.org/magazines/2019/2/234356-separation-logic/fulltext

The syntax it uses for separation logic here includes:

- `P ∗ Q` (note that's a Unicode symbol) is separating conjunction.
- `P -∗ Q` is separating implication (think of it as P implies Q and just
  remember that `(P -∗ Q) ∗ P ⊢ Q`), sometimes called "magic wand".
- `⌜φ⌝` embeds a "pure" (Coq) proposition `φ: Prop` into separation logic
- `∃ (x:T), ...` is overloaded to also work within separation logic. This is so
  natural you can easily forget that separation logic and Coq exists aren't the
  same thing.
- `|==> P` is an "update modality" (the `|==>` part) around some proposition
  P, which you might pronounce "an update to P." It's the most complicated thing
  we'll need and is an innovation of Iris over the original concurrent
  separation logic. To prove concurrent programs correct, it's necessary in
  general to introduce "ghost state", state that exists logically in the proof
  alongside the program execution but doesn't show up in the operational
  semantics or the running code. This is a resource in Iris that represents the
  ability to update the ghost state in a way that produces resources `P` (for
  example, we'll use a theorem of this form which allows creating new ghost
  variables). If you like you can mostly ignore this and just imagine that we
  can always update ghost state, so that `P` and `|==> P` are the same thing.

Ghost state
-----------

To do this proof we need some simple ghost state. Iris has very general support
for user-extensible ghost state. I'll go over the properties of the type of
ghost variables we're constructing here, just not how it is constructed from the
lower-level primitives.

Ghost state in Iris might be different from what you're used to, if you've seen
them in other implementations. Many frameworks (for example, Dafny) have a
similar mechanism that involves annotating the source program with ghost
variables and ghost code which updates the ghost state. Then, those frameworks
need to prove an *erasure theorem* that shows removing ghost variables doesn't
affect the program, since these operations aren't going to be used at runtime.
By contrast in Iris the ghost state only shows up in the proof, so there's no
need to do any erasure. Instead, Iris has general rules for how ghost state can
be created and manipulated that are proven sound once and for all. The one
downside is that ghost state and ghost updates are no longer adjacent to the
program, but instead show up only as steps in the proof (which we'll see below).
However, the flip side is more flexibility, since the updates can depend on
state that's only in the proof and not the code.

.. sidebar:: What does it mean to construct ghost state?

   If you want to look into this more, Iris allows ghost state to come from any
   implementation of an algebraic structure called a *camera* (this name is for
   historical reasons and doesn't mean anything). You might also hear about
   *resources algebras (RAs)* (a substructure of cameras sufficient for many
   purposes) and *partial commutative monoids (PCMs)* (a slightly different
   formulation that predates Iris). The idea of all of these structures is that
   the structure needs to have some way of combining disjoint things, disjoint
   in a sense that separating conjunction will respect. The canonical example of
   a PCM or RA or camera is the heap camera, where we can combine heaplets
   (mappings from locations to values) when they are disjoint.

   In this mini library, the camera I'll reason about is an "authoritative
   exclusive" camera, which just splits a value of type `A` into two parts: both
   of these parts always have the same value (this is the authoritative part),
   and together they allow arbitrary updates since they represent exclusive
   access (this is the exclusive part). We won't see any algebraic construction
   because this camera is built from combinators, so what I'm doing here is
   proving some properties of this combination.

The ghost state I'll create will have two resources, written `own γ (●E a)` and
`own γ (◯E a)`, where `a:A` is an element of an arbitrary type. The first
one represents "authoritative ownership" and the second one is "fragmentary
ownership," and because this is exclusive ownership (represented by the E),
these two are symmetric. I'll typically pronounce `own γ (●E a)` as just "auth
a" and `own γ (◯E a)` as "fragment a", leaving everything else implicit (since
this particular ghost state is so common). Generally the auth goes in an
invariant and we hand out the fragment in lock invariants and such. There's also
a *ghost name*, which uses the metavariable `γ`, to name this particular
variable.

We can do three things with this type of ghost state: allocate a pair of them
(at any step in the proof, since this is ghost state), derive that the auth and
fragment agree on the same value, and update the variable if we have both. You
can think about this ghost state as being a variable of type `A` which we have
two views of, the auth and the fragment. Both of these views agree because
there's only one underlying value, and together they represent exclusive access
to the variable and hence we can update it if we have both.

.. coq:: none

   Section heap.
     (* you can ignore these; this mini-library is parameterized by a bunch of very
     general things *)
     Definition ghostR (A: ofeT) := authR (optionUR (exclR A)).
     Context {A: ofeT} `{Hequiv: @LeibnizEquiv _ A.(ofe_equiv)} `{Hdiscrete: OfeDiscrete A}.
     Context {Σ} {Hin: inG Σ (authR (optionUR (exclR A)))}.

We can allocate a new ghost variable, under an update modality because this
requires modifying the global ghost state. The proof for this lemma will likely
be a bit inscrutable; I'll focus mostly on explaining the program proofs of
Hoare triples below, and just try to convey what these lemma statements mean.

.. coq::

   Lemma ghost_var_alloc (a: A) :
     ⊢ |==> ∃ γ, own γ (●E a) ∗ own γ (◯E a).
   Proof.
     iMod (own_alloc (●E a ⋅ ◯E a)) as (γ) "[H1 H2]".
     { apply excl_auth_valid. }
     iModIntro. iExists γ. iFrame.
   Qed.

Now I'll prove that the two parts always agree, written using *separating
implication* (also pronounced "magic wand" but that obscures its meaning). You
can read `-∗` exactly like `->` and you'll basically have the right
intuition.

.. coq::

   Lemma ghost_var_agree γ (a1 a2: A) :
     own γ (●E a1) -∗ own γ (◯E a2) -∗ ⌜ a1 = a2 ⌝.
   Proof using All.
     iIntros "Hγ1 Hγ2".
     iDestruct (own_valid_2 with "Hγ1 Hγ2") as "H".
     iDestruct "H" as %<-%excl_auth_agree%leibniz_equiv.
     done.
   Qed.

Finally I'll prove a theorem that lets us change ghost state. It requires the
right to change ghost state, hence producing a conclusion under `|==>`. Unlike
the previous theorem this consumes the old ownership and gives new resources,
having modified the ghost variable. Reading the whole thing, it says we can use an auth and a fragment for a particular variable `γ` and update them to an auth and a fragment for some new value `a1'`.

.. coq::

   Lemma ghost_var_update {γ} (a1' a1 a2 : A) :
     own γ (●E a1) -∗ own γ (◯E a2) -∗
       |==> own γ (●E a1') ∗ own γ (◯E a1').
   Proof.
     iIntros "Hγ● Hγ◯".
     iMod (own_update_2 _ _ _ (●E a1' ⋅ ◯E a1')
             with "Hγ● Hγ◯") as "[$$]".
     { apply excl_auth_update. }
     done.
   Qed.

It's also true that two auth or fragments for the same ghost name are
contradictory, but we don't need that in this particular proof so I won't prove
it.

.. coq:: none

   End heap.

.. note:: **How do you type these funny symbols?**

   Even if you aren't ready (yet!) to prove things in Iris, you might be
   wondering how you're supposed to type all of these funny Unicode symbols. You
   also might think the Iris developers are crazy for such a rich syntax.

   I use Emacs, so I type them with a special math input mode. For example, I
   can write `own \gname (\aaE a1) -\sep own \gname (\afE a1)` to get ``own γ
   (●E a1) -∗ own γ (◯E a1)``. If you're using CoqIDE or VSCode you can set up
   fairly similar support; see the `Iris editor setup documentation
   <editor-docs_>`_ for details.

   Unicode syntax sometimes puts people off, but I think it's actually quite
   helpful. It means Iris code is both more compact and looks closer to
   mathematical practice (for example, the papers), which makes it much easier
   to read once you're used to it. Having lots of symbols not used anywhere else
   also makes it vastly easier to get this code to parse correctly without long
   sequences of ASCII symbols.

.. _editor-docs: https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/editor.md

.. coq::

   Section heap.

   (* mostly standard boilerplate *)
   Context `{!heapG Σ}.
   Context `{!lockG Σ}.
   Context `{!inG Σ (ghostR ZO)}.
   Let N := nroot.@"bank".

We can now talk about `iProp Σ`, the type of Iris propositions. This includes
the `own` fact we saw above for ghost resources, `l ↦ v` for the usual points-to
in HeapLang, and all the separation logic connectives. You can ignore the `Σ`,
which is there for technical reasons.

The overall idea of the proof is to use two Z-valued ghost variables to
represent the logical balance of each account. These logical balances will
always add up to zero. We'll relate the logical balance to the physical balance
of an account by requiring them to match up *only when the lock is free*. This
means that upon acquiring both locks, the balances will satisfy the global
invariant, and during the transfer operation we're free to let the logical and
physical balances get out-of-sync until the operation is done.

Now we just need to implement that in a machine-checked way using Iris!

Setting up the invariants
-------------------------

The first thing we need is a lock invariant for each account's lock. The idea of
lock invariants is that first the proof associates a lock invariant `P` to the lock.
When a thread acquires a lock, it get (resources satisfying) `P`, and when it releases
it has to give back (resources satisfying) `P`. Crucially during the
critical section the thread has access to `P` and can violate this proposition
freely. Once a lock invariant is allocated, the resources protected by the lock
are "owned" by the lock and governed through the lock, which is what makes this
specification sound.

`account_inv` will be the lock invariant associated with each account. It
exposes a ghost name `γ` used to tie the account balance to a ghost variable,
and also takes the location `bal_ref` where this account balance is stored.

.. coq::

   Definition account_inv γ bal_ref : iProp Σ :=
     ∃ (bal: Z), bal_ref ↦ #bal ∗ own γ (◯E bal).

An account is a pair of a lock and an account protected by the lock, where
`is_lock` associates the lock to the lock invariant written above.

.. coq::

   Definition is_account (acct: val) γ : iProp Σ :=
     ∃ (bal_ref: loc) lk,
       ⌜acct = (lk, #bal_ref)%V⌝ ∗
       (* you can ignore this ghost name associated with the lock *)
       ∃ (γl: gname), is_lock γl lk (account_inv γ bal_ref).

`bank_inv` is an invariant (the usual one that holds at all intermediate points,
not a lock invariant) that holds the fragments for the account balances and,
importantly, states that the logical balances sum to 0. Any thread can open the
invariant to "read" the logical balances, but modifications must respect the
constraint here.

We need to give names for the logical account balance variables, so this
definition also takes two ghost names.

.. coq::

   Definition bank_inv (γ: gname * gname) : iProp Σ :=
   (* the values in the accounts are arbitrary... *)
   ∃ (bal1 bal2: Z),
       own γ.1 (●E bal1) ∗
       own γ.2 (●E bal2) ∗
       (* ... except that they add up to 0 *)
       ⌜(bal1 + bal2)%Z = 0⌝.

Finally `is_bank` ties together the per-account and global invariant:

.. coq::

   Definition is_bank (b: val): iProp Σ :=
     ∃ (acct1 acct2: val) (γ: gname*gname),
     ⌜b = (acct1, acct2)%V⌝ ∗
     is_account acct1 γ.1 ∗
     is_account acct2 γ.2 ∗
     inv N (bank_inv γ).

Importantly `is_bank b` is *persistent*, which means we can share it among
threads. We'll see this used in `wp_demo_check_consistency`.

.. coq:: no-goals

   Instance is_bank_Persistent b : Persistent (is_bank b).
   Proof. apply _. Qed.

This proof was trivial because the components of `is_bank` are persistent,
which typeclass resolution can figure out. These include the pure facts (it
should be intuitive that these are persistent, since they don't talk about
resources at all), the invariant (because `inv N P` is just knowledge of an
invariant, which can and should be shared) and `is_lock γl lk P` (similarly,
this is knowledge that there is a lock at lk and is
shareable)

A specification for `new_bank`
------------------------------

`new_bank` is actually interesting because its proof has to create all the ghost
state, lock invariants, and invariant, and argue these things initially hold.

I won't completely explain how these proofs work but I'll highlight a few
things. The code is fairly simple and can basically be symbolically executed.
The most parts will be related to ghost state. In particular look out for the
`iMod` tactic, which "executes" a ghost state change under a `|==>`.

.. coq::

   Theorem wp_new_bank :
     (* This is a Hoare triple using Iris's program logic. *)
     {{{ True }}}
       new_bank #()
       (* the `b,` part is a shorthand for `∃ b, ...` in the
       postcondition, and RET b says the function returns b. *)
     {{{ b, RET b; is_bank b }}}.
   Proof.
     iIntros (Φ) "_ HΦ".
     wp_rec. (* unfold new_bank and runs a step of reduction *)
     wp_alloc a_ref as "Ha".
     wp_alloc b_ref as "Hb". (* .unfold *)

.. note::

   Before moving on it's worth explaining what's going on in this proof goal.
   First, there's the Coq context you're used to, which is rendered with bold
   variable names and separated with a solid horizontal line due to the blog infrastructure
   (thanks Clément!). Then in the Coq goal is *another* context, which is being
   rendered by the Iris Proof Mode (IPM), using fancy Coq notations. This is a
   spatial context, which has three hypotheses, for example on of them is `"Ha"
   : a_ref ↦ #0`.

   The IPM comes with tactics like `iDestruct`, `iIntros`, and
   `iApply` which work like the analogous Coq tactics but manipulate these
   spatial hypotheses. The context/goal display and tactics let you do proofs
   within separation logic as if it were the native logic of Coq instead of
   (just) dependent types and higher-order logic. Learning these tactics is a
   lot like learning how to do Coq proofs all over again (that is, there is a
   learning curve but you do get used to it). Separation logic does introduce
   some fundamental complexity into these tactics not seen in Coq: the basic
   difference is that whenever you need to prove `P ∗ Q`, you have to decide
   how to split the hypotheses to prove `P` vs `Q`, whereas you don't need
   to make any analogous decision in Coq (the technical term for this is that
   separation logic is a *substructural* logic, while Coq's higher-order logic
   is structural).

The first interesting step of the proof is that we execute the ghost variable
change in `ghost_var_alloc` and at the same time destruct it with `as (γ1)
"(Hown1&Hγ1)"`, using `γ1` for the ghost name and `Hown1` and `Hγ` for
the two halves, respectively:

.. coq::

     iMod (ghost_var_alloc (0: ZO)) as (γ1) "(Hown1&Hγ1)". (* .unfold *)

Now we can initialize the lock invariant for the first account, which will own
the auth `"Hγ1"` created above.

.. coq::

     wp_apply (newlock_spec (account_inv γ1 a_ref) with "[Ha Hγ1]").
     { iExists _; iFrame. }
     iIntros (lk_a γlk1) "Hlk1".
     iMod (ghost_var_alloc (0: ZO)) as (γ2) "(Hown2&Hγ2)".
     wp_apply (newlock_spec (account_inv γ2 b_ref) with "[Hb Hγ2]").
     { iExists _; iFrame. }
     iIntros (lk_b γlk2) "Hlk2". (* .unfold *)

At this point we'll allocate the `bank_inv` invariant. For reference here's what it says:

.. coq::

   Print bank_inv. (* .unfold .messages *)

The invariant says the logical balances add up to 0, which we'll prove initially
holds here. Notice in the current proof state (shown above), we still have the
auths (`own γ (●E 0)`), but the fragments have been used up by calls to
`newlock_spec`, which is a typical feature of separation logic. Those
resources are now permanently owned by the account lock invariants.

.. coq::

     iMod (inv_alloc N _ (bank_inv (γ1,γ2))
             with "[Hown1 Hown2]") as "Hinv".
     { iNext. iExists _, _; iFrame.
       iPureIntro; auto. }
     wp_pures.
     iApply "HΦ".
     iExists _, _, (γ1,γ2); iFrame.
     iSplit; first eauto.
     simpl.
     iSplitL "Hlk1".
     - iExists _; eauto with iFrame.
     - iExists _; eauto with iFrame.
   Qed.

A specification for `transfer`
------------------------------

As mentioned above, we don't prove anything except for safety for
`transfer`. This still has to prove that we follow the lock invariants and
global invariant - after `is_bank` is created we can no longer add to a single
account in isolation, for example.

You might expect because this is separation logic that we should return ``is_bank
b`` here. It turns out we don't need to since the fact is persistent, so the
caller will never lose this fact.

.. coq::

   Theorem wp_transfer b (amt: Z) :
     {{{ is_bank b }}}
       transfer b #amt
     {{{ RET #(); True }}}.
   Proof.
     iIntros (Φ) "#Hb HΦ".
     (* Breaking apart the above definitions is really quite painful.
     I have written better infrastructure for this but it isn't
     upstream in Iris (yet!) *)
     iDestruct "Hb" as (acct1 acct2 γ ->) "(Hacct1&Hacct2&Hinv)".
     iDestruct "Hacct1" as (bal_ref1 lk1 ->) "Hlk".
     iDestruct "Hlk" as (γl1) "Hlk1".
     iDestruct "Hacct2" as (bal_ref2 lk ->) "Hlk".
     iDestruct "Hlk" as (γl2) "Hlk2".
     wp_rec.
     wp_pures.
     wp_apply (acquire_spec with "Hlk1").
     iIntros "(Hlocked1&Haccount1)".
     wp_apply (acquire_spec with "Hlk2").
     iIntros "(Hlocked2&Haccount2)".
     iDestruct "Haccount1" as (bal1) "(Hbal1&Hown1)".
     iDestruct "Haccount2" as (bal2) "(Hbal2&Hown2)". (* .unfold *)

If you look at the proof goal now, there are a bunch of things going on.
The Iris Proof Mode (IPM) embeds a separation logic context within the Coq
goal. This means we have the Coq context and the IPM context. Furthermore, it
actually uses two contexts: a persistent context (which comes first and is
separated by `---------□`) of facts that are duplicable and thus don't go away
when we need to split, and then a spatial context (separated by `---------∗`) of
ordinary spatial premises.

.. coq::

   (* this steps through the critical section *)
   wp_pures; wp_load; wp_pures; wp_store; wp_pures.
   wp_pures; wp_load; wp_pures; wp_store; wp_pures. (* .unfold *)

Now the physical state is updated but not the logical balances in ghost
state. In order to restore the lock invariant, we have to do that, and this
requires using the invariant with `iInv`.

`iInv` opens the invariant for us and also takes a pattern to destruct the
resulting `bank_inv` right away. You can see that it gives us resources in the
context but also adds `bank_inv γ` to the goal, since this invariant needs to
hold at all points. The `|={⊤ ∖ ↑N}=>` in the goal is another modality (called
a "fancy update"), which you should read as `|==>` but with a label of `⊤ ∖
↑N`. This label is the set of invariants we're allowed to open, and currently
it's everything (`⊤` or "top") except for the namespace `N`, which is the
name chosen for the bank invariant.

.. coq::

   rewrite -fupd_wp. (* we need to do this for iInv to work *)
   iInv "Hinv" as (bal1' bal2') ">(Hγ1&Hγ2&%)". (* .unfold *)
   (* we use the agreement and update theorems above for these ghost
   variables *)
   iDestruct (ghost_var_agree with "Hγ1 [$]") as %->.
   iDestruct (ghost_var_agree with "Hγ2 [$]") as %->.
   iMod (ghost_var_update (bal1-amt) with "Hγ1 Hown1") as "(Hγ1&Hown1)".
   iMod (ghost_var_update (bal2+amt) with "Hγ2 Hown2") as "(Hγ2&Hown2)".
   iModIntro.
   (* we can't just modify ghost state however we want - to continue,
   `iInv` added `bank_inv` to our goal to prove, requiring us to restore
   the invariant *)
   iSplitL "Hγ1 Hγ2".
   { iNext. iExists _, _; iFrame.
     iPureIntro.
     lia. }
   iModIntro.

We've done all the hard work of maintaining the invariant and updating the
ghost variables to their new values.

Now we'll be able to release both locks (in any order, actually) by re-proving
their lock invariants, with the new values of the ghost variables.

.. coq::

     wp_apply (release_spec with "[$Hlk2 $Hlocked2 Hbal2 Hown2]").
     { iExists _; iFrame. }
     iIntros "_".
     wp_apply (release_spec with "[$Hlk1 $Hlocked1 Hbal1 Hown1]").
     { iExists _; iFrame. }
     iIntros "_".
     wp_pures.
     by iApply "HΦ".
   Qed.

A specification for `check_consistency`
---------------------------------------

We'll now prove that `check_consistency` always returns true, using the
protocol established by `is_bank`. This proof is fairly similar to the one
above, and simpler because it doesn't modify any state.

.. coq::

   Theorem wp_check_consistency b :
     {{{ is_bank b }}}
        check_consistency b
     {{{ RET #true; True }}}.
   Proof.
     (* most of this proof is the same: open everything up and acquire
     the locks, then destruct the lock invariants *)
     iIntros (Φ) "#Hb HΦ".
     iDestruct "Hb" as (acct1 acct2 γ ->) "(Hacct1&Hacct2&Hinv)".
     iDestruct "Hacct1" as (bal_ref1 lk1 ->) "Hlk".
     iDestruct "Hlk" as (γl1) "Hlk1".
     iDestruct "Hacct2" as (bal_ref2 lk ->) "Hlk".
     iDestruct "Hlk" as (γl2) "Hlk2".
     wp_rec.
     wp_pures.
     wp_apply (acquire_spec with "Hlk1").
     iIntros "(Hlocked1&Haccount1)".
     wp_apply (acquire_spec with "Hlk2").
     iIntros "(Hlocked2&Haccount2)".
     iDestruct "Haccount1" as (bal1) "(Hbal1&Hown1)".
     iDestruct "Haccount2" as (bal2) "(Hbal2&Hown2)".

     (* the critical section is easy *)
     wp_pures; wp_load.
     wp_pures; wp_load.
     wp_pures.

     (* Now we need to prove something about our return value using information
     derived from the invariant. As before we'll open the invariant, but this time
     we don't need to modify anything, just extract a pure fact. *)
     rewrite -fupd_wp.
     (* the [%] here is the pure fact, actually *)
     iInv N as (bal1' bal2') ">(Hγ1 & Hγ2 & %)".
     iDestruct (ghost_var_agree with "Hγ1 [$]") as %->.
     iDestruct (ghost_var_agree with "Hγ2 [$]") as %->.
     iModIntro.
     iSplitL "Hγ1 Hγ2".
     { iNext. iExists _, _; iFrame.
       iPureIntro.
       lia. }
     iModIntro.

     wp_apply (release_spec with "[$Hlk2 $Hlocked2 Hbal2 Hown2]").
     { iExists _; iFrame. }
     iIntros "_".
     wp_apply (release_spec with "[$Hlk1 $Hlocked1 Hbal1 Hown1]").
     { iExists _; iFrame. }
     iIntros "_".
     wp_pures. (* .unfold *)
     (* the calculation always returns true because of the H hypothesis we got
     from the invariant *)
     rewrite bool_decide_eq_true_2; last congruence.
     by iApply "HΦ".
   Qed.

The final theorem
-----------------

The final theorem we'll prove is `demo_check_consistency`, which ties everything
together into a Hoare triple that has no precondition. The intuition is that
this theorem says that if `demo_check_consistency` terminates, it returns true,
which implies the consistency check works at least with one concurrent transfer.
We could prove a theorem along these lines more directly, but I won't do that
here.

.. coq::

   Theorem wp_demo_check_consistency :
     {{{ True }}}
       demo_check_consistency #()
     {{{ RET #true; True }}}.
   Proof using All.
     iIntros (Φ) "_ HΦ".
     wp_rec.
     wp_apply wp_new_bank; first auto.
     (* we use `#Hb` to put the newly created `is_bank` in the
     "persistent context" in the Iris Proof Mode - these are persistent
     facts and thus are available even when we need to split to prove a
     separating conjunction *)
     iIntros (b) "#Hb". (* .unfold *)

The proof is easy now - the fork rule requires us to split the context and
prove any Hoare triple for the forked thread. `transfer` only needs `Hb`, but
that's persistent and will thus be available. We've coincidentally already
proven a triple for it with a postcondition of `True`.

.. coq::

     wp_apply wp_fork.
     - wp_apply (wp_transfer with "Hb").
       auto.
     - (* `check_consistency` always returns true, using `is_bank` *)
       wp_apply (wp_check_consistency with "Hb").
       iIntros "_".
       by iApply "HΦ".
   Qed.

The above proof and specification for `wp_fork` might not be clear; here's a
derived specification for `Fork` that might be easier to interpret. This
specification makes explicit that the caller splits their context into two
parts, one to use for proving `e` and the other for the remainder of the
program `e'`.

.. coq::

   Theorem wp_fork_alt (P Q: iProp Σ) (e e': expr) :
     (P -∗ WP e {{ λ _, True }}) -∗
     ∀ (Φ: val → iProp Σ), (Q -∗ WP e' {{ Φ }}) -∗
     (P ∗ Q -∗ WP Fork e;; e' {{ Φ }}).
   Proof.
     iIntros "Hwp1" (Φ) "Hwp2 (HP&HQ)". (* .unfold *)

The goal here shows that we assumed some resources `P` and `Q`, and what
we'll do is distribute them to prove that `e` is safe and that we can continue
with running `e'`.

.. coq::

     (* the details of the rest of this proof aren't important *)
     wp_apply (wp_fork with "(Hwp1 HP)").
     wp_apply ("Hwp2" with "HQ").
   Qed.

   End heap.

Conclusions
===========

Now you've seen the whole process of writing some code and reasoning about in
Iris! Many parts of this proof will surely seem mysterious, but I hope you still
saw the basic parts of the argument show up in the formal, machine-checked
reasoning.

Taking a step back, I want to emphasize again that this is just a taste of what
Iris can do. You don't have to use HeapLang, you can write your own, like our
GooseLang language (heavily based on HeapLang) which we use to model Go. You
don't have to prove Hoare triples, you can prove refinement. You don't even have
to use the Iris base logic to take advantage of the interactive proof mode. It
still takes quite a bit of expertise to do these things, but we're talking about
concurrent verification here. Iris has significantly lowered the barrier to
entry, and it makes it possible to do all these proofs in a machine-checked
way.

.. sidebar:: What about automation?

   I get asked reasonably often about automation in Iris, so here's my brief
   answer (feel free to ask if you want more details). Basically, you'd be
   surprised that you don't actually need automation that symbolically steps
   through code, automatically applying specifications and solving separation
   logic entailments. Instead, what Iris gives is the *concise language of
   separation logic* for creating abstractions and *powerful interactive proofs*
   for manipulating them manually. There are two reasons this works. First,
   these (manually constructed!) abstractions are so powerful, it's possible to
   be productive without doing proofs by brute force. Second, because we're
   doing proofs about interesting concurrent software, almost every line of code
   is interesting in some way and a lot of guidance is needed, so it's hard to
   imagine saving much with simple automation. I do need to write an obvious
   line of code (like `wp_alloc` or `wp_load`) for every source line of
   code, but this is a small fraction of my total lines of proof code and an
   even smaller fraction of my time.

   I'll also note that it is possible to do some level of automation in Iris at
   the level of creating new tactics, along the same lines as creating specific
   Ltac tactics to automate common parts of proofs. This is how the HeapLang
   weakest-precondition-specific tactics like `wp_apply` and `wp_load` are
   written, and it's possible to learn how to do the same thing for your own
   abstractions.

What to try next
----------------

If you're now excited about Iris, here are a few things you can try next:

- The `POPL 2018 tutorial <tutorial-popl18_>`_ is fairly accessible and
  well-documented, and will help you actually write program proofs using Iris.
  There's also a `POPL 2020 tutorial <tutorial-popl20_>`_, which is about a
  semantic type soundness proof using Iris, another big use case for Iris (other
  than program proofs).

.. _tutorial-popl20: https://gitlab.mpi-sws.org/iris/tutorial-popl20

- The journal paper `Iris from the ground up <ground-up_>`_ explains the theory
  and logical foundations behind Iris. It does an excellent job of teaching
  Iris, well, from the ground up, especially compared to the papers because Iris
  was developed over the course of several conference papers, none of which
  quite explain the technical details for the current version. However, it
  spends almost no time *motivating* Iris, leaving that to the many papers
  published using Iris.

.. _ground-up: https://people.mpi-sws.org/~dreyer/papers/iris-ground-up/paper.pdf

- If you still want more to convince you Iris is great, you can look at the
  variety of papers published using it, which you can see on the `Iris website
  <iris-website_>`_. I think some papers that highlight the diversity of
  applications include the following:

  - The original `RustBelt <rustbelt_>`_ POPL 2018 paper defines semantic type
    safety for Rust. Iris is essential to correctly model Rust's higher-order
    features, like first-class functions.
  - The original `Iris Proof Mode <ipm_>`_ POPL 2017 paper shows off the proof
    mode and how it is used for both program proofs and logical relations.
    (Unfortunately some terminology has to be translated to relate this paper to
    the current implementation, which is based on a generalized proof mode
    described in the `MoSeL <mosel_>`_ ICFP 2018 paper.)
  - The `gDOT <gdot_>`_ ICFP 2020 paper proves soundness of the Scala type
    system using an interesting subset of the Iris framework (notably it uses
    step indexing, the proof mode, and a program logic, but no separation
    logic).
  - In a shameless plug, our own `Perennial <perennial_>`_ SOSP 2019 paper uses
    Iris to do crash-safety reasoning for Go code.

    .. _iris-website: https://iris-project.org/
    .. _rustbelt: https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf
    .. _ipm: https://iris-project.org/pdfs/2017-popl-proofmode-final.pdf
    .. _mosel: https://iris-project.org/pdfs/2018-icfp-mosel-final.pdf
    .. _gdot: https://iris-project.org/pdfs/2020-icfp-dot-final.pdf
    .. _perennial: https://www.chajed.io/papers/perennial:sosp2019.pdf

  You don't actually have to *read* all of these papers, even just looking at
  the abstracts gives a sense for what Iris can be used for.

Learning Iris is hard - if you're seriously considering it, do reach out and
find someone who can help you while you're getting started! The Iris community
is not large but it is welcoming.
