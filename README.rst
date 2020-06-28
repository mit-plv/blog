=========
 PLV@MIT
=========

The PLV blog, built with `Pelican <https://blog.getpelican.com/>`_ and `Alectryon <https://github.com/cpitclaudel/alectryon>`_.  See `the tutorial blogpost <content/2019-06-06 - getting-started.rst>`_ for details about Alectryon.

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

You can render your new post using ``make devserver``; the website will be at http://localhost:8000.  If you want to share the rendered version, you can use ``make rsync_upload``; the default configuration pushes to ``https://people.csail.mit.edu/$(SSH_USER)/plv-blog-drafts`` through ``login.csail.mit.edu``.

Writing Coq proofs
==================

Code in ``.. coq::`` blocks is executed at build time; goals and responses are recorded and displayed along with the code.

.. topic:: Interacting with the proof

   A small bubble next to a Coq fragment indicates that it produced output:
   readers can either hover, click, or tap on the fragment to show the
   corresponding goals and messages.

   A special ‘*Display all goals and responses*’ checkbox is added at the
   beginning of the document; its position can be adjusted by adding an explicit
   ``.. alectryon-toggle::`` directive.

Customizing the output
----------------------

Directive arguments and special comments can be used to customize the display of Coq sessions.  The `documentation of Alectryon <https://github.mit.edu/plv/alectryon#as-a-docutils-or-sphinx-module>`_ has details, but the easiest is probably to look at other blog posts for examples.

Tips
====

- Indent contents of ``.. coq::`` directives three spaces deeper than the directive itself (further indentation is included in the output).

- To link to another blog post, such as ``/content/xyz.rst``, use the following syntax:

  .. code-block:: rst

      `A link to xyz <{filename}/xyz.rst>`_

- For reStructuredText tips, browse to https://www.sphinx-doc.org/en/master/usage/restructuredtext/basics.html.

- For help with Pelican, browse to https://docs.getpelican.com/en/stable/index.html.
