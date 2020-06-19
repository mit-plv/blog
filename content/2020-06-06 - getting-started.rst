============
 Blog demo!
============

:tags: alectryon
:category: Tools
:authors: Clément Pit-Claudel
:summary: A tutorial on writing posts with Pelican & Alectryon

This blog is built with `Pelican <https://blog.getpelican.com/>`_ and `Alectryon <https://github.com/cpitclaudel/alectryon>`_.

Local setup
===========

Clone the |plv/blog|_ repository recursively (``git clone --recurse-submodules``) to get a copy of `Alectryon <https://github.com/cpitclaudel/alectryon>`_ (or use ``git submodule update --init`` to download it after cloning).

.. |plv/blog| replace:: ``plv/blog``
.. _plv/blog: https://github.mit.edu/plv/blog

Dependencies:
    | ``opam install coq-serapi=8.10.0+0.7.0``
    | ``python3 -m pip install --user pelican==4.2.0 markdown==3.1.1 docutils==0.16``
    | ``python3 -m pip install --user pygments==2.5.2 dominate==2.4.0``
Build:
    | ``make devserver`` (this will serve a live-updated copy of the blog at ``http://localhost:8000``)

Writing new posts
=================

Write a draft, then make a PR to this repository.

Posts go to ``content/$year-$month-$day - $slug.$ext``; you can use `reStructuredText <https://www.sphinx-doc.org/en/master/usage/restructuredtext/basics.html>`_ (``$ext=rst``) or markdown if you don't need advanced Coq highlighting (``$ext=md``).  Pelican will generate one page per post, named ``$slug.html``.

Here's a basic template for new posts (see `the Pelican docs <https://docs.getpelican.com/en/3.6.3/content.html#articles-and-pages>`_ for more information), which you might put in e.g. ``content/2019-06-02 - short-title.rst``:

.. code-block:: rst

   ============
    Post Title
   ============

   :tags: t1, t2
   :category: category-name
   :authors: author1, author2
   :summary: Short summary here.

   Article text here.

   .. coq::

      Goal False -> True.
        intros.
        exact I.

Writing Coq proofs
==================

Code in ``.. coq::`` blocks is executed at build time; goals and responses are recorded and displayed along with the code.  Here's an example:

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

     (* Base case: 0 *)
     - constructor.

     (* Base case: 1 *)
     - discriminate.

     (* Inductive case: [S (S n)] *)
     - constructor.
       auto.
   Qed.

.. topic:: Interacting with the proof

   A small bubble (like this: :alectryon-bubble:`_`) next to a Coq fragment
   indicates that it produced output: you can either hover, click, or tap on the
   fragment to show the corresponding goals and messages.

   A special ‘*Display all goals and responses*’ checkbox is added at the
   beginning of the document; its position can be adjusted by adding an explicit
   ``.. alectryon-toggle::`` directive.

   The `documentation of Alectryon <https://github.com/cpitclaudel/alectryon#as-a-docutils-or-sphinx-module>`_ has more details.

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

Tips
====

- Indent contents of ``.. coq::`` directives three spaces deeper than the directive itself (further indentation is included in the output).

- To link to another blog post, such as ``/content/xyz.rst``, use the following syntax:

  .. code-block:: rst

      `A link to xyz <{filename}/xyz.rst>`_

- For reStructuredText tips, browse to https://www.sphinx-doc.org/en/master/usage/restructuredtext/basics.html.

- For help with Pelican, browse to https://docs.getpelican.com/en/stable/index.html.
