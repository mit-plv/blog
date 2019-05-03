=========
 PLV@MIT
=========

Local setup
===========

Dependencies:
    ``pip3 install --user pelican==4.0.1 markdown==3.1 docutils==0.14``
    ``pip3 install --user pexpect==4.7.0 pygments==2.3.1 dominate==2.3.5 sexpdata==0.0.3``
Build:
    ``make devserver`` (this will serve a live-updated copy of the blog at ``http://localhost:8000``)

Writing new posts
=================

Write a draft, then make a PR to this repository.

Posts go to ``content/$year-$month-$day-$slug.$ext``; you can use markdown (``ext=md``) or `reStructuredText <https://www.sphinx-doc.org/en/master/usage/restructuredtext/basics.html>`_ (``ext=rst``).  ``slug`` is the name of the webpage that Pelican will generate.

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
