=========
 PLV@MIT
=========

The PLV blog, built with `Pelican <https://blog.getpelican.com/>`_.

Local setup
===========

Clone this repository recursively (``git clone --recurse-submodules``) to get a copy of `Alectryon <../alectryon>`_ (or use ``git submodule update --init`` to download it after cloning).

Dependencies:
    | ``opam install coq-serapi=8.9.0+0.6.1``
    | ``pip3 install --user pelican==4.0.1 markdown==3.1 docutils==0.14``
    | ``pip3 install --user pygments==2.3.1 dominate==2.3.5``
Build:
    | ``make devserver`` (this will serve a live-updated copy of the blog at ``http://localhost:8000``)

Writing new posts
=================

Write a draft, then make a PR to this repository.

Posts go to ``content/$year-$month-$day - $slug.$ext``; you can use `reStructuredText <https://www.sphinx-doc.org/en/master/usage/restructuredtext/basics.html>`_ (``$ext=rst``) or markdown (``$ext=md``; only if you don't need advanced Coq highlighting).  ``$slug`` is the name of the webpage that Pelican will generate.

Here's a basic template for new posts (see `the Pelican docs <https://docs.getpelican.com/en/3.6.3/content.html#articles-and-pages>`_ for more information), which you might put in e.g. ``content/2019-06-02 - short-title.rst``:

.. code-block:: rst

   ============
    Post Title
   ============

   :tags: t1; t2
   :category: category-name
   :authors: author1; author2
   :summary: Short summary here.

   Article text here.

   .. coq::

      Goal False -> True.
        intros.
        exact I.

Code in ``.. coq::`` blocks is executed at build time; goals and responses are
recorded and displayed along with the code.  A special ‘*Display all goals and
responses*’ checkbox is added at the beginning of the document; its position can
be adjusted by adding an explicit ``.. alectryon-toggle::`` directive.

Tips
====

- Indent contents of ``.. coq::`` directives three spaces deeper than the directive itself (further indentation is included in the output).

- To link to another blog post, such as ``/content/xyz.rst``, use the following syntax:

  .. code-block:: rst

      `A link to xyz <{filename}/xyz.rst>`_

- For reStructuredText tips, browse to https://www.sphinx-doc.org/en/master/usage/restructuredtext/basics.html.

- For help with Pelican, browse to https://docs.getpelican.com/en/stable/index.html.
