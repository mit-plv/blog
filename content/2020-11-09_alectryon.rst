==============================
 Untangling mechanized proofs
==============================

:tags: alectryon
:category: Tools
:authors: Clément Pit-Claudel
:summary: An introduction to Alectryon

.. preview::

   `Alectryon <https://github.com/cpitclaudel/alectryon/>`_ (named after the Greek god of chicken) is a collection of tools for writing technical documents that mix Coq code and prose, in a style sometimes called *literate programming*.

   Coq proofs are hard to understand in isolation: unlike pen-and-paper proofs, proof scripts only record the steps to take (induct on *x*, apply a theorem, …), but the *states* (*goals*) that these steps lead to are crucial to understanding what goes on in a proof.  As a result, plain proof scripts are essentially incomprehensible without the assistance of an interactive interface like CoqIDE or Proof General.

   The most common approach these days for sharing proofs with readers without forcing them to run Coq is to manually copy Coq's output into source code comments — a tedious, error-prone, and brittle process.  Any text that accompanies the proof is also embedded in comments, making for a painful editing experience.

   Alectryon does better: it automatically captures and interleaves Coq's output with proof scripts to produce interactive webpages, and it lets you toggle between prose- and code-oriented perspectives on the same document so that you can use your favorite text editing mode for writing prose and your favorite Coq IDE for writing proofs.

I have a talk about this `at SLE2020 <https://conf.researchr.org/details/sle-2020/sle-2020-papers/11/Untangling-mechanized-proofs>`__ on November 16th; you should join!

Below, you can see three examples: in the first one I asked Alectryon to record the result of a single `Check` command.  In the second, I recorded an error message printed by Coq.  In the third, I recorded a simple proof script — try hovering or clicking on Coq sentences.  In the last, I've used hidden ``Show Proof`` commands to show how each tactic participates in constructing a proof term.

.. coq::

   Check bool_ind. (* .unfold *)

.. coq::

   Fail Check (1 + true). (* .unfold .fails *)

.. coq::

   Require Import List. (* .none *)
   Lemma rev_rev {A} (l: list A) :
     List.rev (List.rev l) = l.
   Proof.
     induction l.
     - (* l ← [] *)
       cbn. reflexivity.
     - (* l ← _ :: _ *)
       cbn.
       rewrite rev_app_distr.
       rewrite IHl.
       cbn. reflexivity.
   Qed.

.. coq::

   Section classical. (* .none *)
   Context (classical: forall A, A \/ ~ A).
   Example double_negation : (forall A, ~~A -> A).
   Proof.
     intros A notnot_A.
     Show Proof. (* .messages .unfold *)
     destruct (classical A) as [_A | not_A].
     Show Proof. (* .messages .unfold *)
     - (* A holds *)
       assumption.
       Show Proof. (* .messages .unfold *)
     - (* A does not hold *)
       elim (notnot_A not_A).
       Show Proof. (* .messages .unfold *)
   Qed.
   End classical. (* .none *)

By the way, I wrote `an academic paper <https://doi.org/10.1145/3426425.3426940>`__ at `SLE2020 <https://cpitclaudel.github.io/alectryon-sle2020-talk/>`__ (November 16) on Alectryon (`preprint on my website <https://pit-claudel.fr/clement/papers/alectryon-SLE20.pdf>`__ since the DOI link doesn't resolve yet).  It has plenty of cool visualizations and examples, it goes into much more depth than this intro, and importantly it has all the related work, including lots of stuff on procedural vs declarative proofs.  This blog post, the paper, and the `talk <https://cpitclaudel.github.io/alectryon-sle2020-talk/>`__ were all built with Alectryon.

If this is your first time on this blog, you might want to check the `very short tutorial on navigating these visualizations </blog/pages/how-to.html#how-to>`__ before proceeding with the rest of this post.

A quick tour of Alectryon
=========================

The library was written with two scenarios in mind:

- Making it easier to browse Coq developments (even if these developments are not written in literate style) by turning Coq source files into webpages allowing readers to replay proofs in their browser (the “Proviola” style). As a demo, I recorded goals and responses for `a <https://alectryon-paper.github.io/bench/flocq-3.3.1/src/Core/Digits.html>`_ `complete <https://alectryon-paper.github.io/bench/flocq-3.3.1/src/Core/Round_NE.html>`_ `build <https://alectryon-paper.github.io/bench/flocq-3.3.1/src/Prop/Sterbenz.html>`_ of the `Flocq library <https://alectryon-paper.github.io/bench/flocq-3.3.1/src/>`_.

- Writing documents mixing Coq source code and explanatory prose, either starting from a text file containing special directives (the “coqtex” and “coqrst” style, used in Coq's reference manual), or starting from a Coq file containing special comments (the “coqdoc” style, used in `CPDT <http://adam.chlipala.net/cpdt/>`_, `Software foundations <https://softwarefoundations.cis.upenn.edu>`_, etc.).

  The Alectryon paper, this blog post, and my SLE talk are examples of the former (they are written in reStructuredText, a Markdown-like markup language); as another example, here is `a chapter from FRAP <https://alectryon-paper.github.io/bench/books/interpreters.html>`_ and `one from CPDT <https://alectryon-paper.github.io/bench/books/proof-by-reflection.html>`_, converted to reStructuredText by hand (change the URLs to ``.rst`` to see the sources).

  As a demo of the latter here's `a full build of Logical Foundations <https://alectryon-paper.github.io/bench/lf/>`_.

There's no support for attaching bits of documentation to specific bits of code, like definitions, axioms, variables, etc.  As `I've written in the past <https://coq.discourse.group/t/would-coq-benefit-from-docstrings/849/3>`_, I think this is a different job (“docstrings”), ideally to be handled by Coq itself (similar to how it tracks the body and location of definitions).  Alectryon also doesn't support hyperlink Coq terms to their definitions like coqdoc can, but I plan to implement this eventually.

Generating webpages
-------------------

Alectryon's main purpose is to record Coq's outputs and interleave them with the corresponding inputs to create an interactive webpage:

.. coq::

   Require Import Coq.Unicode.Utf8 Coq.Lists.List Coq.Arith.Arith. (* .none *)
   Theorem rev_length : ∀ l : list nat,
       length (rev l) = length l.
   Proof.
     intros l.
     induction l as [| n l' IHl'].
     - (* l ← [] *)
       reflexivity.
     - (* l ← _ :: _ *)
       simpl.
       rewrite app_length.
       rewrite Nat.add_comm.
       simpl.
       rewrite IHl'.
       reflexivity.
   Qed.

   Check rev_length.

Because this is an interactive webpage, we can apply all sorts of post-processing to the output, like using MathJax to make a math proof a bit more readable:

.. raw:: html

   <div style="display: none">
       \(\newcommand{\ccQ}{\mathbb{Q}}\)
       \(\newcommand{\ccNat}{\mathbb{N}}\)
       \(\newcommand{\ccSucc}[1]{\mathrm{S}\:#1}\)
       \(\newcommand{\ccFrac}[2]{\frac{#1}{#2}}\)
       \(\newcommand{\ccPow}[2]{{#1}^{#2}}\)
       \(\newcommand{\ccNot}[1]{{\lnot #1}}\)
       \(\newcommand{\ccEvar}[1]{\textit{\texttt{#1}}}\)
       \(\newcommand{\ccForall}[2]{\forall \: #1. \; #2}\)
       \(\newcommand{\ccNsum}[3]{\sum_{#1 = 0}^{#2} #3}\)
   </div>

.. coq:: none

   Require Export Coq.Unicode.Utf8.
   Require Export NArith ArithRing.

   Fixpoint nsum max f :=
     match max with
     | O => f 0
     | S max' => f max + nsum max' f
     end.

   Module LatexNotations.
     Infix "\wedge" := and (at level 190, right associativity).
     Notation "A \Rightarrow{} B" := (∀ (_ : A), B) (at level 200, right associativity).
     Notation "'\ccForall{' x .. y '}{' P '}'" := (∀ x, .. (∀ y, P) ..) (at level 200, x binder, y binder, right associativity, format "'\ccForall{' x .. y '}{' P '}'").
     Notation "'\ccNat{}'" := nat.
     Notation "'\ccSucc{' n '}'" := (S n).
     Infix "\times" := mult (at level 30).
     Notation "\ccNot{ x }" := (not x) (at level 100).

     Notation "'\ccNsum{' x '}{' max '}{' f '}'" :=
       (nsum max (fun x => f))
         (format "'\ccNsum{' x '}{' max '}{' f '}'").
   End LatexNotations.

.. container:: coq-mathjax

   .. coq:: unfold

      Module Gauss. (* .none *)
      Import LatexNotations. (* .none *)
      Lemma Gauss: ∀ n, 2 * (nsum n (fun i => i)) = n * (n + 1).
      Proof. (* .fold *)
        induction n; cbn [nsum]. (* .fold *)
        - (* n ← 0 *)
          reflexivity.
        - (* n ← S _ *)
          rewrite Mult.mult_plus_distr_l. (* .no-hyps *)
          rewrite IHn. (* .no-hyps *)
          ring.
      Qed.
      End Gauss. (* .none *)

… or using the browser's native support for vector graphics to render *Game of Life* boards encoded as lists of Booleans into small images:

.. coq:: none

   Require Coq.Numbers.Cyclic.Int63.Int63.
   Require Coq.Lists.List.
   Require Coq.Lists.Streams.

   Module GameOfLife.
     Import Int63.

     Module Type Array.
       Axiom array: Type -> Type.

       Parameter make : forall A, int -> A -> array A.
       Arguments make {_} _ _.

       Parameter get : forall A, array A -> int -> A.
       Arguments get {_} _ _.

       Parameter default : forall A, array A -> A.
       Arguments default {_} _.

       Parameter set : forall A, array A -> int -> A -> array A.
       Arguments set {_} _ _ _.

       Parameter length : forall A, array A -> int.
       Arguments length {_} _.

       Parameter copy : forall A, array A -> array A.
       Arguments copy {_} _.

       Declare Scope array_scope.
       Delimit Scope array_scope with array.
       Notation "t .[ i ]" :=
         (get t i)
           (at level 2, left associativity, format "t .[ i ]").
       Notation "t .[ i <- a ]" :=
         (set t i a)
           (at level 2, left associativity, format "t .[ i <- a ]").

       (* Local Open Scope int63_scope. *)
       (* Axiom get_set_same : forall A t i (a:A), (i < length t) = true -> t.[i<-a].[i] = a. *)
       (* Axiom get_set_other : forall A t i j (a:A), i <> j -> t.[i<-a].[j] = t.[j]. *)
     End Array.

     Import Coq.Lists.List.

     Module ListArray <: Array.
       Import ListNotations.

       Record _array {A: Type} :=
         { arr_data: list A;
           arr_default: A }.
       Arguments _array : clear implicits.
       Definition array := _array.

       Definition nat_of_int i := BinInt.Z.to_nat (Int63.to_Z i).
       Definition int_of_nat n := Int63.of_Z (BinInt.Z.of_nat n).

       Definition make {A: Type} (l: int) (a: A) : array A :=
         let mk :=
             fix mk (l: nat) {struct l} :=
               match l with
               | 0 => []
               | S l => a :: mk l
               end in
         {| arr_data := mk (nat_of_int l);
            arr_default := a |}.

       Local Open Scope int63_scope.

       Definition length {A} (x: array A) :=
         int_of_nat (List.length x.(arr_data)).

       Definition get {A} (x: array A) (i: int) :=
         let get :=
             fix get (l: list A) (i: int) {struct l} :=
               match l with
               | [] => x.(arr_default)
               | hd :: tl =>
                 if i == 0 then hd else get tl (i - 1)
               end in
         get x.(arr_data) i.

       Definition default {A} (x: array A) :=
         x.(arr_default).

       Definition set {A} (x: array A) (i: int) (a: A) : array A :=
         let set :=
             fix set (i: int) (l: list A) {struct l} :=
               match l with
               | [] => []
               | hd :: tl =>
                 if i == 0 then a :: tl else hd :: set (i - 1) tl
               end in
         {| arr_data := set i x.(arr_data);
            arr_default := x.(arr_default) |}.

       Definition copy {A} (x: array A) : array A := x.

       Declare Scope array_scope.
       Delimit Scope array_scope with array.
       Notation "t .[ i ]" :=
         (get t i)
           (at level 2, left associativity, format "t .[ i ]").
       Notation "t .[ i <- a ]" :=
         (set t i a)
           (at level 2, left associativity, format "t .[ i <- a ]").
     End ListArray.

     Import ListArray.

     Definition board := array (array bool).

     Definition bget (b: board) x y :=
       b.[y].[x].

     Open Scope int63.
     Import ListNotations.
     Import Bool.

     Definition bi (b: board) x y :=
       b2i (bget b x y).

     Definition neighbors (b: board) x y :=
       [bget b (x - 1) (y - 1); bget b (x) (y - 1); bget b (x + 1) (y - 1);
        bget b (x - 1) (y)    ; bget b (x) (y)    ; bget b (x + 1) (y)    ;
        bget b (x - 1) (y + 1); bget b (x) (y + 1); bget b (x + 1) (y + 1)].

     Definition live_neighbors (b: board) x y :=
       bi b (x - 1) (y - 1) + bi b (x) (y - 1) + bi b (x + 1) (y - 1) +
       bi b (x - 1) (y)     +                    bi b (x + 1) (y)     +
       bi b (x - 1) (y + 1) + bi b (x) (y + 1) + bi b (x + 1) (y + 1).

       (* List.fold_left *)
       (*   (fun acc (x: bool) => if x then (acc + 1) else acc) *)
       (*   (neighbors b x y) 0 *)

     Definition step_one (b: board) x y :=
       let live := live_neighbors b x y in
       if bget b x y then
         orb (live == 2) (live == 3)
       else
         (live == 3).

     Definition iter {B} (n: int) (b: B) (f: int -> B -> B) :=
       let it :=
           fix it (fuel: nat) (idx: int) (b: B) {struct fuel} :=
             match fuel with
             | 0 => b
             | S fuel => it fuel (idx - 1)%int63 (f idx b)
             end
       in it (nat_of_int n) (n - 1)%int63 b.

     Definition make_board (sz: int) (f: int -> int -> bool) :=
       iter sz (make sz (make sz false))
            (fun y board =>
               set board y
                   (iter sz (make sz false)
                         (fun x row =>
                            set row x (f x y)))).

     Definition init (l: list (list bool)) :=
       make_board
         (int_of_nat (List.length l))
         (fun x y => List.nth_default
                    false
                    (List.nth_default [] l (nat_of_int y))
                    (nat_of_int x)).

     Definition flatten (b: board) :=
       List.map (fun row => row.(arr_data)) b.(arr_data).

     Definition step (b: board) :=
       make_board (length b) (step_one b).

     Definition conway_life b :=
       flatten (step (init b)).

     Module Streams.
       Import Coq.Lists.Streams.

       CoFixpoint iter {A} (f: A -> A) (init: A) :=
         Cons init (iter f (f init)).

       Fixpoint take {A} (n: nat) (s: Stream A) : list A :=
         match n with
         | 0 => []
         | S n => match s with
                 | Cons hd tl => hd :: take n tl
                 end
         end.
     End Streams.

     Import Streams.

     Notation "0" := false.
     Notation "1" := true.

.. container:: coq-life

   .. coq::

      Definition glider := [[0;1;0;0;0];
                            [0;0;1;0;0];
                            [1;1;1;0;0];
                            [0;0;0;0;0];
                            [0;0;0;0;0]].
      Compute take 9 (iter conway_life glider). (* .unfold *)

.. coq:: none

   End GameOfLife. (* .none *)

… or using a graph library to draw visualizations that makes it clearer what happens when one builds a red-black tree with ``Coq.MSets.MSetRBT``.

.. coq:: none

   Require Coq.MSets.MSetRBT
           Coq.Arith.Arith
           Coq.Structures.OrderedTypeEx
           Coq.Structures.OrdersAlt
           Coq.Lists.List.

   Module RBTExample.
     Import Coq.MSets.MSetRBT
            Coq.Arith.Arith
            Coq.Structures.OrderedTypeEx
            Coq.Structures.OrdersAlt
            Coq.Lists.List.
     Import ListNotations.

     Module Nat_as_OT := Update_OT Nat_as_OT.

.. coq::

   Module RBT := MSets.MSetRBT.Make Nat_as_OT.

.. coq:: none

     Module RBTNotations.
       Notation "'{' ''kind':' ''node'' ; ''color':' ''' color ''' ; ''value':' ''' value ''' ; ''left':' left ; ''right':' right '}'" :=
         (RBT.Raw.Node color left value right)
           (format  "'{'  ''kind':' ''node'' ;  ''color':'  ''' color ''' ;  ''value':'  ''' value ''' ;  ''left':'  left ;  ''right':'  right  '}'").

       Notation "'{' ''kind':' ''leaf'' '}'" :=
         (RBT.Raw.Leaf).

       Notation "'{' ''tree':' this '}'" :=
         {| RBT.this := this |}.
     End RBTNotations.

     Notation "v |> f" := (f v) (at level 10, only parsing).
     Arguments List.rev {A}.

.. container:: coq-rbt

   .. coq::

      Definition build_trees (leaves: list nat) :=
        List.fold_left (fun trs n =>
              RBT.add n (hd RBT.empty trs) :: trs)
          leaves [] |> List.rev.

      Module Pretty. (* .none *)
      Import RBTNotations. (* .none *)
      Compute build_trees [1;2;3;4;5]. (* .unfold *)
      Compute build_trees [2;1;4;3;6]. (* .unfold *)
      End Pretty. (* .none *)

Do these visualizations really help?  You be the judge: here's how the red-black tree example looks with plain-text output:

.. container:: coq-rbt-raw

   .. coq:: none

      Module Raw. (* .none *)
      Definition build_trees (leaves: list nat) :=
        List.fold_left (fun trs n =>
              RBT.add n (hd RBT.empty trs) :: trs)
          leaves [] |> List.rev |> (List.map RBT.this).
      Import RBT.Raw. (* .none *)

   .. coq::

      Compute build_trees [1;2;3;4;5]. (* .unfold *)
      Compute build_trees [2;1;4;3;6]. (* .unfold *)
      End Raw. (* .none *)

.. coq:: none

   End RBTExample.

.. raw:: html

   <link rel="stylesheet" href="{static}/static/libs/2020-11-09_alectryon.css">
   <script src="{static}/static/libs/svg.v3.0.min.js" defer></script>
   <script src="{static}/static/libs/d3.v5.min.js" defer></script>
   <script src="{static}/static/libs/dagre-d3.v0.6.4.min.js" defer></script>
   <script src="{static}/static/libs/2020-11-09_alectryon.js" defer></script>
   <script type="text/javascript" id="MathJax-script" defer src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js"></script>

Even if you don't use Alectryon's literate programming features, these webpages have one additional advantage beyond convenient browsing: because they record both your code and Coq's responses, they can serve as a permanent record of your developments immune to bitrot and suitable for archival.

Editing literate Coq documents
------------------------------

Besides generating webpages from standalone Coq files, Alectryon can help you write documentation, blog posts, and all sorts of other documents mixing proofs and prose.  Alectryon's ``literate`` module implements translations from Coq to reStructuredText and from reStructuredText to Coq, which allow you to toggle between two independent views of the same document: one best for editing code, and one best for editing reST prose.  Concretely, Alectryon knows how to convert between this:

.. code-block:: rst

   =============================
    Writing decision procedures
   =============================

   Here's an inductive type:

   .. coq::

      Inductive Even : nat -> Prop :=
      | EvenO : Even O
      | EvenS : forall n, Even n -> Even (S (S n)).

   .. note::

      It has two constructors:

      .. coq:: unfold out

         Check EvenO.
         Check EvenS.

… and this:

.. code-block:: coq

   (*|
   =============================
    Writing decision procedures
   =============================

   Here's an inductive type:
   |*)

   Inductive Even : nat -> Prop :=
   | EvenO : Even O
   | EvenS : forall n, Even n -> Even (S (S n)).

   (*|
   .. note::

      It has two constructors:
   |*)

   Check EvenO.
   Check EvenS.

Because the transformations are (essentially) inverses of each other, you don't have to pick one of these two styles and stick to it (or worse, to maintain two copies of the same document, copy-pasting snippets back and forth).  Instead, you can freely switch between using your favorite Coq IDE to write code and proofs while editing bits of prose within comments, and using your favorite reStructuredText editor to write prose.

The reason for picking reStructuredText as the markup language for comments is that it's designed with extensibility in mind, which allows me to plug Alectryon into the standard Docutils and Sphinx compilation pipelines for reStructuredText (Sphinx is what the documentations of Haskell, Agda, Coq, and Python are written in).  This is how this blog is written, and in fact you can `download the sources <https://github.com/mit-plv/blog/blob/master/content/2020-11-09_alectryon.rst>`__ if you're curious to see what it looks like.  This is also how I made my `SLE2020 slides <https://cpitclaudel.github.io/alectryon-sle2020-talk/>`__ (press ``p`` to see the presenter notes) and how I wrote my SLE2020 paper.

A small Emacs package (``alectryon.el``), allows you to toggle quickly between Coq and reST.  The screenshot below demonstrates this feature: on the left is the Coq view of an edited excerpt of *Software Foundations*, in ``coq-mode``; on the right is the reST view of the same excerpt, in a ``rst-mode`` buffer.  The conversion is transparent, so editing either view updates the same ``.v`` file on disk.  Notice the highlight indicating a reStructuredText warning on both sides:

.. image:: {static}/static/images/alectryon_emacs-mode-screenshot.svg
   :alt: Side-by-side comparisons of Coq and reStructuredText views of the same document

Alectryon's syntax-highlighting is done with Pygments, but it uses an update Coq grammar with a database of keywords and commands extracted directly from the reference manual (ultimately, this part should be merged upstream, and the database-generation tool should be merged into the Coq reference manual; I'll write a separate blog post about it at some point).

Recording Coq's output and caching it
-------------------------------------

Alectryon's design is pretty modular, so if you want to use it for other purposes it's easy to use just some parts of it.  In particular, its core is a simple API that takes a list of code snippets, feeds them to Coq through SerAPI, and records goals and messages.  This functionality is exposed on the command line (taking json as input and producing json as output) and also as a Python module:

.. code-block:: python

   >>> from alectryon.core import annotate
   >>> annotate(["Example xyz (H: False): True. (* ... *) exact I. Qed.", "Print xyz."])
   [[CoqSentence(
        sentence='Example xyz (H: False): True.',
        responses=[],
        goals=[CoqGoal(name='2',
                       conclusion='True',
                       hypotheses=[CoqHypothesis(name='H', body=None, type='False')])]),
     CoqText(string=' (* ... *) '),
     CoqSentence(sentence='exact I.', responses=[], goals=[]),
     CoqText(string=' '),
     CoqSentence(sentence='Qed.', responses=[], goals=[])],

    [CoqSentence(sentence='Print xyz.',
                 responses=['xyz = fun _ : False => I\n     : False -> True'],
             goals=[])]]

Alectryon uses JSON caches to speed up consecutive runs, but even when performance isn't a problem caches provide a very useful form of regression testing for embedded Coq snippets.  Without such tests, it's easy for seemingly innocuous changes in a library to break its documentation in subtle ways. For example, you might have the following snippet:

    .. coq:: none

       Module Old.
         Fixpoint plus n m :=
           match n with
           | 0 => m
           | S p => S (plus p m)
           end.

    The function ``plus`` is defined recursively:

    .. coq::

       Print plus.
       End Old. (* .none *)

If you rename ``plus`` to ``Nat.add`` and add a compatibility notation, this is what your documentation will silently become, with no error or warning to let you realize that something went wrong:

    .. coq::

       Print plus.

This was such a common problem in the reference manual that we implemented workarounds to catch the most egregious cases (where changes caused snippets to print errors instead of executing successfully).  But if you check in Alectryon's caches into source control, then the following will show up pretty clearly:

.. code:: diff

     "contents": "Print plus.",
     "messages": [
       {
         "_type": "message",
   -     "contents": "plus = \nfix plus (n m : nat) {struct n} : nat := …"
   +     "contents": "Notation plus := Nat.add"
       }

----

All these features are exposed through a command line interface documented in `Alectryon's README <https://github.com/cpitclaudel/alectryon/>`_.  This project has been in development for over a year, but there's still lots of rough bits, so expect bugs and please `report them <https://github.com/cpitclaudel/alectryon/issues/>`_!

Using Alectryon
===============

Standalone usage
----------------

The easiest way to get started Alectryon is to use it very much like coqdoc, but using reStructuredText syntax in special comments delimited with ``(*|`` and ``|*)``, like in this hypothetical ``even.v`` document:

.. code-block:: coq

   (*|
   =======
    Title
   =======

   Prose. *Emphasis*; **strong emphasis**; ``code``; `coq code`; `link <url>`__.
   |*)

   Inductive Even : nat -> Prop :=
   | EvenO : Even O
   | EvenS : forall n, Even n -> Even (S (S n)).

… which can then be compiled into a static webpage using ``../alectryon.py --frontend coq+rst --backend webpage even.v -o even.html``.

This is what I did for FRAP and CPDT.  For Software foundations and Flocq, I used a compatibility layer combining Alectryon to render the code and coqdoc to render the prose::

   find . -name *.v -exec alectryon.py --frontend coqdoc --backend webpage {} \;

Authoring tips
~~~~~~~~~~~~~~

There's a great `reStructuredText <https://www.sphinx-doc.org/en/master/usage/restructuredtext/basics.html>`_ primer on Sphinx's website, if you're new to this markup language (there's also an `official quick-reference guide <https://docutils.sourceforge.io/docs/user/rst/quickref.html>`_, which is as ugly as it is comprehensive).  reStructuredText is no panacea, but it's a decent language with a good story about extensibility, and it's popular for writing documentation (Haskell, Agda, and Coq use it for their reference manuals).

If you use Emacs, you can install ``alectryon.el``, a small Emacs library that makes it easy to toggle between reStructuredText and Coq:

.. code-block:: elisp

   (add-to-list 'load-path "path/to/alectryon/clone/")
   (require 'alectryon)

With this, you'll get improved rendering of `(*| … |*)` comment markers, and you'll be able to toggle between reStructuredText and Coq with a simple press of :kbd:`C-c C-S-a`.  You probably also want to ``M-x package-install flycheck`` and ``pip3 install --user docutils``, though neither of these are hard dependencies.

    (Hi, reader! Are you thinking “why isn't this on MELPA?”  Great question!  It's because I haven't had the time to do it yet.  But you can — `yes <https://github.com/melpa/melpa/blob/master/README.md>`__, *you*!  In exchange, I promise I'll sing your praises every time your name comes up in conversation — I might even refer to you as ‘writer-of-MELPA-recipes extraordinaire’.

    Alternatively, if you're a member of this most distinguished category of people who write more grant proposals than Emacs Lisp programs, you should drop me a line: I'm on the academic job market this year, so we should chat!)

Integrated into a blog or manual
--------------------------------

Alectryon is very easy to integrate with platforms and tools that support Sphinx or Docutils, like `Pelican <https://docs.getpelican.com/en/stable/>`_, `readthedocs <https://readthedocs.org/>`_, `Nikola <https://getnikola.com/>`_, etc. (In the long run, I hope to migrate Coq's reference manual to Alectryon. It currently uses ``coqrst``, a previous iteration of Alectryon that I wrote a few years ago based on ``coqtop`` instead of SerAPI).

For this blog, for example, I just added the following snippet to our ``pelicanconf.py``:

.. code-block:: python

   import alectryon
   import alectryon.docutils
   from alectryon.html import ASSETS

   # Register the ‘.. coq::’ directive
   alectryon.docutils.register()

   # Copy Alectryon's stylesheet
   alectryon_assets = path.relpath(ASSETS.PATH, PATH)
   STATIC_PATHS.append(alectryon_assets)
   EXTRA_PATH_METADATA[alectryon_assets] = {'path': 'static/alectryon/'}

   # Copy a custom Pygments theme with good contrast to theme/pygments
   for pth in ("tango_subtle.css", "tango_subtle.min.css"):
       EXTRA_PATH_METADATA[path.join(alectryon_assets, pth)] = \
             {'path': path.join('theme/pygments/', pth)}

Similar steps would be needed for Sphinx, though using ``alectryon.sphinx.register()`` instead.  I hear that there's work in progress to integrate with other blog platforms.

As a library
------------

The choice of reStructuredText is a bit arbitrary, so it's not a hard dependency of Alectryon.  It should be relatively straightforward to combine it with other input languages (like LaTeX, Markdown, etc.) — I just haven't found the time to do it.  There's even an output mode that takes Coq fragments as input and produces individual HTML snippets for each, to make integration easier.  See `Alectryon's README <https://github.com/cpitclaudel/alectryon/>`_ for more info.

As an example, I made a compatibility shim for Coqdoc that uses Alectryon to render Coq code, responses, and goals, but calls to coqdoc to render the contents of `(** … **)` comments; look for ``coqdoc`` in file ``cli.py`` of the distribution to see how it works.

Writing Coq proofs in Coq+reST
==============================

In reStructuredText documents, code in ``.. coq::`` blocks is executed at compilation time; goals and responses are recorded and displayed along with the code.  Here's an example:

.. alectryon-toggle::

.. coq::

   Inductive Even : nat -> Prop :=
   | EvenO : Even O
   | EvenS : forall n, Even n -> Even (S (S n)).

   Fixpoint even (n : nat) : bool :=
     match n with
     | 0 => true
     | 1 => false | S (S n) => even n
     end.

   Lemma even_Even : forall n, even n = true -> Even n.
     fix IHn 1.
     destruct n as [ | [ | ] ].
     all: simpl.
     all: intros.

     - (* Base case: 0 *)
       constructor.

     - (* Base case: 1 *)
       discriminate.

     - (* Inductive case: [S (S _)] *)
       constructor.
       auto.
   Qed.

.. topic:: Interacting with the proof

   A small bubble (like this: :alectryon-bubble:`_`) next to a Coq fragment indicates that it produced output: you can either hover, click, or tap on the fragment to show the corresponding goals and messages.

   A special ‘*Display all goals and responses*’ checkbox is added at the beginning of the document, as shown above; its position can be adjusted by adding an explicit ``.. alectryon-toggle::`` directive.

   These features do not require JavaScript (only a modern CSS implementation). Optionally, a small Javascript library can be used to enable keyboard navigation, which significantly improves accessibility.  You can try it on this page by pressing :kbd:`Ctrl+↑` or :kbd:`Ctrl+↓`.

Here is another example of highlighting:

.. coq::

   Lemma some_not_none : forall {A: Type} (a: A),
             Some a = None -> False.
     progress intros.
     change (match Some a with
             | Some _ => False
             | None => True
             end).
     set (Some _) as s in *.
     clearbody s.
     match goal with
     | [ H: ?x = _ |- context[?x] ] => rewrite H
     end.
     first [exact I].
     Show Proof.
   Defined.

   Eval compute in some_not_none.

Customizing the output
----------------------

Directive arguments and special comments can be used to customize the display of Coq blocks.  The `documentation of Alectryon <https://github.com/cpitclaudel/alectryon#as-a-docutils-or-sphinx-module>`_ has details, but here are a few examples:

- Run a piece of code silently:

  .. code-block:: rst

     .. coq:: none

        Require Import Coq.Arith.Arith.

  .. coq:: none

     Require Import Coq.Arith.Arith.

- Start with all intermediate states shown, hide selectively:

  .. code-block:: rst

     .. coq:: unfold

        Goal True /\ True. (* .fold *)
          split.
          - (* .fold *)
            idtac "hello". (* .no-goals *)
            apply I.
          - auto.
        Qed.

  .. coq:: unfold

     Goal True /\ True. (* .fold *)
       split.
       - (* .fold *)
         idtac "hello". (* .no-goals *)
         apply I.
       - auto.
     Qed.

- Show only a message, hiding the input:

  .. code-block:: rst

     .. coq::

        Compute (1 + 1). (* .unfold .messages *)

  .. coq::

     Compute (1 + 1). (* .unfold .messages *)

  Of course, if you're going to hide the input but show some output (as with ``.no-input``, ``.messages``, or ``.goals``), you'll need to add ``.unfold``, since the usual way to show the output (clicking on the input) won't be available.

The default ``alectryon.css`` stylesheet supports two display modes: the proviola style (two windows side by side, with code shown on one side and goals on the other), and this blog's style (with goals shown alongside each fragment when the window is wide enough and below the input line otherwise).  Both modes support clicking on an input line to show the output right below it.  You can pick a mode by placing the

Some interesting technical bits
===============================

- The vast majority of the processing time in Alectryon is spent parsing and unparsing s-expressions.    I wrote Alectryon's s-exp parser myself to minimize dependencies and got it reasonably fast, but if you're a Python speed geek you should definitely `have a look <https://github.com/cpitclaudel/alectryon/blob/master/alectryon/sexp.py>`_ (I wonder if cython would help here — I'm not sure how good it is at bytestring manipulation).  Hopefully this problem (and the corresponding code) will evaporate once SerAPI supports JSON.

- The default HTML backend works without JavaScript — it uses only CSS.  It stores its state in checkboxes: each input line is a label for a hidden checkbox, whose state controls the visibility of the output through conditional CSS rules.  The document-wide toggle works the same way, overriding all individual checkboxes.  You can see the page without the styles by typing ``javascript:document.querySelector("link[href$=\"alectryon.css\"]").remove()`` into your address bar (all responses, goals, and checkboxes will be displayed, and you'll lose the interactivity, of course).

- Block comments in Coq are relatively complicated: parsers need to track not just nested comments but also nested strings, an oddity we inherited from OCaml (string delimiters in comments must be properly matched, and comment markers within them are ignored).  The idea there was to make commenting more robust, so that wrapping a valid bit of code in `(* … *)` would always work.  As an example, the following is valid OCaml code:

  .. code-block:: ocaml

     let a = "x *) y" in
     (* let a = "x *) y" in *) a

  … though as you may have guessed from the broken syntax highlighting, not many tools handle this properly — it will happily break Emacs' ``tuareg-mode``, Pygments, etc.

  But the whole point is moot in Coq, because `*)` is a fairly common token, and it's not disallowed (unlike in OCaml):

  .. code-block:: coq

     split; (try reflexivity; intros *).

  Single-line comments solve this problem nicely.  I've seen suggestions to use ``(*)`` in OCaml and Coq, but (1) it's quite unpleasant to type, (2) it'll break every editor that currently supports OCaml, and (3) it doesn't have natural variants (`(*` is a regular comment and `(**` is a coqdoc one; what would a literate variant of ``(*)`` be? Not `(**)`, since that's the same as `(* *)`)

  Still, single-line comments would be nice.  A few years ago I wrote a `predecessor of Alectryon for F* <https://github.com/FStarLang/fstar-mode.el/tree/master/etc/fslit>`_, and using ``///`` for literate comments makes it much easier to start new reST blocks, compared to relatively unwieldy `(*| … |*)` markers.  As a bonus, the parsing/unparsing algorithms are a lot simpler (it turns out that ``(*`` and ``*)`` are pretty common token in reST as well, ``(like *this*)``, so Alectryon needs to do some quoting and unquoting instead of treating all text opaquely).

- The conversion between Coq and reStructuredText keeps track of input positions and carries them throughout the translation, allowing it to annotate output lines with the input they came from.  I use this when compiling from Coq+reST to HTML, to map reStructuredText error messages back to the original Coq sources. Additionally, if you have Flycheck installed, the ``alectryon.el`` Emacs mode uses that to lint the reStructuredText code embedded in Alectryon comments.

  It actually took me a while to converge on a good design for this.  One of the requirements is that the translator should be able to keep the position of at least one point, since we want to preserve the user's position in the document when we switch.  With a rich string type this is trivial, but the string types in Python (and OCaml, and most languages really) are quite minimal.  In Emacs Lisp, for example, we'd create a “point” marker, and convert the contents of the buffer from Coq to reST or vice-versa by making insertions and deletions into it, which would move the marker around automatically.

  This would work in Python too, but it would be a lot of code to maintain for a single application (including reimplementing regex matching on top of this new structure), so instead I used a simpler type of strings annotated with position information only (in fact, for performance, these strings are just views over the original document, implemented as a string and a pair of offsets).  Then I segment the original document into a collection of these views annotated with their kind (prose or code), slice and dice them further to add or remove indentation, ‘.. coq::’ markers, or comment delimiters, and finally assemble them into a Frankenstein monster of a document, composed of fragments from the original document pieced together by a few added strings (annoyingly, having to escape comment delimiters throws an extra complication, since there's no straightforward notion of replacement for these string views (instead, unescaping ``(\ *`` to produce `(*` requires splitting `(*` into three parts, dropping the middle one, and stitching the remaining two together).

- The conversion from reST to Coq tries hard to keep as few ``.. coq::`` directives as possible.  For example:

  .. list-table::
     :width: 100%
     :widths: 50 50
     :header-rows: 1

     * - reST
       - Coq
     * - .. code-block:: rst

            Some text

            .. coq::

               Let a := 1.

            .. coq:: unfold

               Let b := 1.

            .. note::

               More text.

            .. coq::

               Let aa := 1.

            Final text.

            .. coq::

               Let bb := 1.

       - .. code-block:: coq

            (*|
            Some text
            |*)

            Let a := 1.

            (*|
            .. coq:: unfold
            |*)

            Let b := 1.

            (*|
            .. note::

               More text.

            .. coq::
            |*)

            Let aa := 1.

            (*|
            Final text.
            |*)

            Let bb := 1.

  Note how two of the ``.. coq::`` directives were omitted from the output, and two were kept (can you guess why?).  The behavior is basically a compromise between two constraints: the conversion functions should be bijective (modulo whitespace), and their composition should be idempotent.  The logic I implemented (though I'm sure I forgot one corner case, or 7), is to remove all ``.. coq::`` markers that can be unambiguously reconstructed from the context.  This means removing all markers that (1) do not have custom flags (hence the first preserved header) and (2) have an indentation (nesting) level matching the immediately preceding line (hence the second preserved header, or else when converting back `Let aa := 1` would be nested under the ``.. note::``).

Future work
===========

There are a few things that would improve the quality of the documents produced by Alectryon, but I don't have immediate plans to tackle all of them, mostly for lack of time:

- Adding a LaTeX backend.  This is `mostly done <https://github.com/cpitclaudel/alectryon/blob/master/alectryon/latex.py>`__.

- Working on other advanced visualizations, hopefully culminating in a Coq enhancement proposal to have a standardized way to do non-textual notations (you'd attach a function to a type that says how to render it as a graph, or a LaTeX formula, or an SVG picture, or any other form of rendering).  I have early results on this for separation logic; please get in touch if you'd like to hear more.

- Extending the system to other languages, probably starting with Lean, F*, easyCrypt, and possibly HOL4?  It'd be interesting to see how well this generalizes.

- Integrating with `jsCoq <https://x80.org/rhino-coq/>`_, to allow users to interact with the code directly in the browser (most of the output would be precomputed, but users would also be able to edit the code and recompute the output).  For a mock-up of the experience, see `the related tools that I built for F* <https://people.csail.mit.edu/cpitcla/fstar.js/stlc.html>`_.

- Highlighting differences between consecutive goals, possibly using the support that's now built-in in Coq, though see `this issue <https://github.com/coq/coq/issues/13218>`__.

- Replacing the `coqrst <https://github.com/coq/coq/tree/master/doc/sphinx>`_ tool used by the Coq refman with a version based on Alectryon, which will likely require merging SerAPI into Coq (pretty please?).  (This doesn't mean getting rid of ``coqdomain.py`` or changing the syntax used in the manual, just changing the backend that's used to calculate Coq output).  Most of the work is done: I built `a prototype <https://github.com/cpitclaudel/coq/tree/alectryon>`__ for SLE2020.

  Ideally, we'd take this opportunity to generate not just highlighted snippets but also JSON output, as a giant regression test (we'd check in the generated JSON, so changes would be indicated by ``git diff`` and updating the file would just be a matter of committing it).

- Porting Coq's box layout algorithm to JavaScript, or just compiling the existing implementation with ``js_of_ocaml``, and using that to reflow code and messages when page dimensions change.  I think CSS is close to being able to support this — I know how to do ``hov`` boxes (mostly), but I'm not sure whether ``hv`` boxes can be done (and in any case, it would likely be quite slow).  It's funny that pretty-printing is a whole subfield of PL, but we've never managed to get implementers of web browsers interested.

- Integrating Alectryon with CI to automatically produce annotated listings for all files in a repository.

Let me know if you're interested in tackling one of these.  I'd love to work together or offer tips / pointers.
