=========
 PLV@MIT
=========

Local setup
===========

Clone this repository recursively (``git clone --recurse-submodules``) to get a copy of `Alectryon <../alectryon>`_ (or use ``git submodule update --init`` to download it after cloning).

Dependencies:
    ``opam install coq-serapi=8.9.0+0.6.1``
    ``pip3 install --user pelican==4.0.1 markdown==3.1 docutils==0.14``
    ``pip3 install --user pygments==2.3.1 dominate==2.3.5``
Build:
    ``make devserver`` (this will serve a live-updated copy of the blog at ``http://localhost:8000``)

Writing new posts
=================

Write a draft, then make a PR to this repository.

Posts go to ``content/$year-$month-$day-$slug.$ext``; you can use markdown (``ext=md``) or `reStructuredText <https://www.sphinx-doc.org/en/master/usage/restructuredtext/basics.html>`_ (``ext=rst``).  ``slug`` is the name of the webpage that Pelican will generate.

Here's a basic template for new posts (see `the Pelican docs <https://docs.getpelican.com/en/3.6.3/content.html#articles-and-pages>`_ for more information):

``content/2019-05-02-short-title.rst``
    .. code:: rst

       ============
        Post Title
       ============

       :tags: t1; t2
       :category: category-name
       :authors: author1; author2
       :summary: Short summary here.

       Article text here.

Tips
----

- To link to ``/content/xyz.rst``, use the following syntax::

      `A link to xyz <{filename}/xyz.rst>`_

  or in Markdown::

      [A link to xyz]({filename}/xyz.rst)

- For reStructuredText tips, browse to https://www.sphinx-doc.org/en/master/usage/restructuredtext/basics.html.

- For help with Pelican, browse to https://docs.getpelican.com/en/stable/index.html.

TODOs
=====

- If we move this repo to the public version of Github, add ``GITHUB_URL = "plv/blog"`` to ``pelicanconf.py``.
