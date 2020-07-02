================================
 Getting started with Alectryon
================================

:tags: alectryon
:category: Tools
:authors: Clément Pit-Claudel
:summary: An introduction to Alectryon
:status: draft

.. preview::

   `Alectryon <https://github.com/cpitclaudel/alectryon/>`_ (named after the Greek god of chicken) is a collection of tools for writing technical documents that mix Coq code and prose, in a style sometimes called *literate programming*.

   Coq proof scripts are hard to understand in isolation: the *goals* that they operate on, which Coq keeps track of and displays to the user, provide crucial context.  Yet, until now, authors hoping to record and display these goals have found themselves painstakingly copying Coq's output — a tedious, error-prone, and brittle process.

   Alectryon offers a solution.

Below, you can see three examples: in the first one I recorded the result of a single `Check` command.  In the second, I recorded an error message printed by Coq.  In the third, I recorded a simple proof script — try hovering or clicking on Coq sentences.  In the last, I've mixed hidden command with code to record partially constructed proof terms, a style often used to explain how tactics and holes work:

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

Alectryon is a collection of mostly-independent tools:

- A ``core`` module takes a list of code snippets, feeds them to Coq through SerAPI, and records goals and messages.  This functionality is exposed on the command line (taking json as input and producing json as output) and as a Python API:

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

- An ``html`` module formats goals and responses as HTML, which, paired with appropriate CSS, can be explored interactively:

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

- A ``docutils`` module integrates Alectryon into reStructuredText, making it easy to embed Coq snippets in reStructuredText documents.  This is how this blog is written, and you can read the sources of this post at `<https://github.com/mit-plv/blog/blob/master/content/2020-06-06_alectryon.rst>`_.

- A ``pygments`` module implements syntax-highlighting for Coq, using a database of keywords and commands extracted from the manual (Ultimately, this part should be merged upstream, and the database-generation tool should be merged into the Coq reference manual; I'll write a separate blog post about it at some point).

- A ``json`` module serializes Coq's messages and responses to disk.  This is useful for caching results between runs, but also as a way to implement regression testing on documents including Coq contents.  This helps keeps code and text in sync, as it quickly catches Coq changes that affect a document: without this, when a tactic or command changes, Coq documents that include copy-pasted output will show outdated goals and messages, and Coq documents that use automatically-generated output will display goals and messages that do not match the surrounding prose.  This is a real and common problem, and in fact we have implemented workarounds in the reference manual to catch the most egregious cases (where changes caused snippets to print errors instead of executing successfully).

- A ``literate`` module implements translations from Coq to reStructuredText and from reStructuredText to Coq.  From Coq to reST it recognizes special `(*| … |*)` comments and turns them into reStructuredText, and from reST to Coq it wraps all text except ``.. coq::`` blocks into special comments, adjusting indentation as needed.  Concretely, Alectryon knows how to convert between this:

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

  Because the transformations are (essentially) inverses of each other, you don't have to pick one of these two styles and stick to it (or worse, having to maintaining two copies of the same document, copy-pasting snippets back and forth).  Instead, you can freely switch between using your favorite Coq IDE to write code and proofs while editing bits of prose within comments, and using your favorite reStructuredText editor to write prose.

- Finally, a small Emacs package (``alectryon.el``), allows you to toggle quickly between these two views.  The screenshot below demonstrates this feature: on the left is the Coq view of an edited excerpt of *Software Foundations*, in ``coq-mode``; on the right is the reST view of the same excerpt, in a ``rst-mode`` buffer.  The conversion is transparent, so editing either view updates the same ``.v`` file on disk.  Notice the highlight indicating a reStructuredText warning on both sides:

  .. image:: {static}/static/images/alectryon_emacs-mode-screenshot.png
     :alt: Side-by-side comparisons of Coq and reStructuredText views of the same document

All these features are exposed through a command line interface, documented in `Alectryon's README <https://github.com/cpitclaudel/alectryon/>`_.  This project has been in development for over a year, but there's still lots of rough bits, so expect bugs and please `report them <https://github.com/cpitclaudel/alectryon/issues/>`_!

Using Alectryon
===============

The library was written with two scenarios in mind:

- Making it easier to browse Coq developments (even if these developments are not written in literate style) by turning Coq source files into webpages allowing readers to replay proofs in their browser (the “Proviola” style). As a demo, I recorded goals and responses for `a <https://people.csail.mit.edu/cpitcla/alectryon/flocq/Core/Digits.html>`_ `complete <https://people.csail.mit.edu/cpitcla/alectryon/flocq/Core/Round_NE.html>`_ `build <https://people.csail.mit.edu/cpitcla/alectryon/flocq/Prop/Sterbenz.html>`_ of the `Flocq library <https://people.csail.mit.edu/cpitcla/alectryon/flocq/>`_.

- Writing documents mixing Coq source code and explanatory prose, either starting from a text file containing special directives (the “coqtex” and “coqrst” style, used in Coq's reference manual), or starting from a Coq file containing special comments (the “coqdoc” style, used in `CPDT <http://adam.chlipala.net/cpdt/>`_, `Software foundations <https://softwarefoundations.cis.upenn.edu>`_, etc.).

  This blog post is an example of the former (it is written in reStructuredText); as another example, here are `two <https://people.csail.mit.edu/cpitcla/alectryon/frap/interpreters.html>`_ `chapters <https://people.csail.mit.edu/cpitcla/alectryon/frap/proof-by-reflection.html>`_ of FRAP, converted to reStructuredText by hand (change the URLs to ``.rst`` to see the sources).

  As a demo of the latter here's `a chapter of CPDT <https://people.csail.mit.edu/cpitcla/alectryon/cpdt/>`_ rendered with Alectryon, as well as `a full build of Software Foundations <https://people.csail.mit.edu/cpitcla/alectryon/lf/>`_.

There's no support for attaching bits of documentation to specific bits of code, like definitions, axioms, variables, etc.  As `I've written in the past <https://coq.discourse.group/t/would-coq-benefit-from-docstrings/849/3>`_, I think this is a different job (“docstrings”), ideally to be handled by Coq itself (similar to how it tracks the body and location of definitions).  It also doesn't hyperlink Coq terms to their definitions like coqdoc can, but I plan to implement this eventually.

Standalone
----------

The easiest way to get started Alectryon is to use il very much like coqdoc, but using reStructuredText syntax in special comments delimited with `(*|` and `|*)`, like in this hypothetical ``even.v`` document:

.. code-block:: coq

   (*|
   =======
    Title
   =======

   Prose. *Emphasis*; **strong emphasis**; ``code``; `coq code`; `link <url>`_.
   |*)

   Inductive Even : nat -> Prop :=
   | EvenO : Even O
   | EvenS : forall n, Even n -> Even (S (S n)).

… which can then be compiled into a static webpage using ``../alectryon.py --frontend coq+rst --backend webpage even.v -o even.html``.

This is what I did for CPDT.  For Software foundations and Flocq, I used a compatibility layer combining Alectryon to render the code and coqdoc to render the prose::

   find . -name *.v -exec alectryon.py --frontend coqdoc --backend webpage {} \;

Authoring tips
~~~~~~~~~~~~~~

There's a great `reStructuredText <https://www.sphinx-doc.org/en/master/usage/restructuredtext/basics.html>`_ primer on Sphinx's website, if you're new to this markup language (there's also an `official quick-reference guide <https://docutils.sourceforge.io/docs/user/rst/quickref.html>`_, which is as ugly as it is comprehensive).  reStructuredText is no panacea, but it's a decent language with a good story about extensibility, and it's popular for writing focumentation (Haskell, Agda, and Coq use it for their reference manuals).

If you use Emacs, you can install ``alectryon.el``, a small Emacs library that makes it easy to toggle between reStructuredText and Coq:

.. code-block:: elisp

   (add-to-list 'load-path "path/to/alectryon/clone/")
   (require 'alectryon)

With this, you'll get improved rendering of `(*| … |*)` comment markers, and you'll be able to toggle between reStructuredText and Coq with a simple press of :kbd:`C-c C-S-a`.  You probably also want to ``M-x package-install flycheck`` and ``pip3 install --user docutils``, though neither of these are hard dependencies.

(Hi, reader! Are you thinking “why isn't this on MELPA?”  Great question!  It's because I haven't had the time to do it yet.  But you can — yes, *you*!  In exchange, I promise I'll sing your praises every time your name comes up in conversation — I might even refer to you as ‘xxx, writer-of-MELPA-recipes extraordinaire’ in passing.  Alternatively, if you're a member of this most distinguished category of people who write more grant proposals than Emacs Lisp programs, you should drop me a line: I'm probably going to be looking for postdocs or jobs soon, so we should chat!)

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

Similar steps would be needed for Sphinx, though using ``alectryon.sphinx.register()`` instead.

As a library
------------

The choice of reStructuredText is a bit arbitrary, so it's not a hard dependency of Alectryon.  It should be relatively straightforward to combine it with other input languages (like LaTeX, Markdown, etc.) — I just haven't found the time to do it.  There's even an output mode that takes Coq fragments as input and produces individual HTML snippets for each, to make integration easier.  See `Alectryon's README <https://github.com/cpitclaudel/alectryon/>`_ for more info.

As an example, I made a compatibility shim that uses Alectryon to render Coq code, responses, and goals, but calls to coqdoc to render the contents of `(** … **)` comments; look for ``coqdoc`` in file ``cli.py`` of the distribution.

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

- The design of the Coq ↔ reStructuredText translator is heavily influenced by a tool that I wrote for F* a few years ago, called `fslit <https://github.com/FStarLang/fstar-mode.el/tree/master/etc/fslit>`_.  I'm a bit partial to the F* version: there, literate comments are introduced using ``///`` markers that comment out a full line, much like literate Haskell uses ``>`` markers.  This makes it much easier to start new reST blocks, compared to relatively unwieldy `(*| … |*)` markers).

  Compounding the problem is the issue that block comments in Coq are relatively complicated: parsers need to track not just nested comments but also nested strings, an oddity we inherited from OCaml (string delimiters in comments must be properly matched, and comment markers within them are ignored).  The idea there was to make commenting more robust, so that wrapping a valid bit of code in `(* … *)` would always work.  As an example, the following is valid OCaml code:

  .. code-block:: ocaml

     let a = "x *) y" in
     (* let a = "x *) y" in *) a

  … though as you may have guessed from the broken syntax highlighting, not many tools handle this properly — it will happily break Emacs' ``tuareg-mode``, Pygments, etc.

  But the whole point is moot in Coq, because `*)` is a fairly common token, and it's not disallowed (unlike in OCaml):

  .. code-block:: coq

     split; (try reflexivity; intros *).

  Single-line comments solve this problem nicely.  I've seen suggestions to use ``(*)`` in OCaml and Coq, but (1) it's quite unpleasant to type, (2) it'll break every editor that currently supports OCaml, and (3) it doesn't have natural variants.  In F* for example ``//`` is a regular comment and ``///`` is a literate one; in Coq `(*` is a regular comment and `(**` is a coqdoc one; what would a literate variant of ``(*)`` be? Not `(**)`, for obvious reasons, so ``(*))``?

  Still, single-line comments would be nice — they allow commenting out regions much more reliably, and in Alectryon's case they make the parsing/unparsing algorithms a lot simpler (it turns out that ``(*`` and ``*)`` are pretty common token in reST as well, ``(like *this*)``, so Alectryon needs to do some quoting and unquoting instead of treating all text opaquely).

- The conversion between Coq and reStructuredText keeps track of input positions and carries them throughout the translation, allowing it to annotate output lines with the input they came from.  I use this when compiling from Coq+reST to HTML, to map reStructuredText error messages back to the original Coq sources. Additionally, if you have Flycheck installed, the ``alectryon.el`` Emacs mode uses that to lint the reStructuredText code embedded in Alectryon comments.

  It actually took me a while to converge on a good design for this.  One of the requirements is that the translator should be able to keep the position of at least one point, since we want to preserve the user's position in the document when we switch.  With a rich string type this is trivial, but the string types in Python (and OCaml, and most languages really) are quite minimal.  In Emacs Lisp, for example, we'd create a “point” marker, and convert the contents of the buffer from Coq to reST or vice-versa by making insertions and deletions into it, which would move the marker around automatically.

  This would work in Python too, but it would be a lot of code to maintain for a single application (including reimplementing regexp matching on top of this new structure), so instead I used a simpler type of strings annotated with position information only (in fact, for performance, these strings are just views over the original document, implemented as a string and a pair of offsets).  Then I segment the original document into a collection of these views annotated with their kind (prose or code), slice and dice them further to add or remove indentation, ‘.. coq::’ markers, or comment delimiters, and finally assemble them into a Frankenstein monster of a document, composed of fragments from the original document pieced together by a few added strings (annoyingly, having to escape comment delimiters throws an extra complication, since there's no straightforward notion of replacement for these string views (instead, unescaping ``(\ *`` to produce `(*` requires splitting `(*` into three parts, dropping the middle one, and stitching the remaining two together).

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

There are a few things that would improve the quality of the documents produced by Alectryon, but I don't have immediate plans to tackle them, mostly for lack of time:

- Integrating with `jsCoq <https://x80.org/rhino-coq/>`_, to allow users to interact with the code directly in the browser.  For a mock-up, see `the related tools that I built for F* <https://people.csail.mit.edu/cpitcla/fstar.js/stlc.html>`_.

- Highlighting differences between consecutive goals, using the support that's now built-in in Coq.

- Replacing the `coqrst <https://github.com/coq/coq/tree/master/doc/sphinx>`_ tool used by the Coq refman with a version based on Alectryon, which will likely require merging SerAPI into Coq (pretty please?).  (This doesn't mean getting rid of ``coqdomain.py`` or changing the syntax used in the manual, just changing the backend that's used to calculate Coq output).

  Ideally, we'd take this opportunity to generate not just highlighted snippets but also JSON output, as a giant regression test (we'd check in the generated JSON, so changes would be indicated by ``git diff`` and updating the file would just be a matter of committing it).

- Porting Coq's box layout algorithm to JavaScript, or just compiling the existing implementation with ``js_of_ocaml``, and using that to reflow code and messages when page dimensions change.  I think CSS is close to being able to support this — I know how to do ``hov`` boxes (mostly), but I'm not sure whether ``hv`` boxes can be done (and in any case, it would likely be quite slow).  It's funny that pretty-printing is a whole subfield of PL, but we've never managed to get browser implementers interested.

- Integrating Alectryon with CI to automatically produce annotated listing for all files in a repository.

Let me know if you're interested on tackling one of these.  I can provide guidance.
