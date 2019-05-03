#!/usr/bin/env python
# -*- coding: utf-8 -*- #
from __future__ import unicode_literals

AUTHOR = 'PLV'
SITENAME = 'PLV@MIT'
SITEURL = ''
SITESUBTITLE = "Updates from Adam Chlipala's PLV group at MIT"

PATH = 'content'
FILENAME_METADATA = r'(?P<date>\d{4}-\d{2}-\d{2})-(?P<slug>.*)'

TIMEZONE = 'America/New_York'

DEFAULT_LANG = 'en'

# Feed generation is usually not desired when developing
FEED_ALL_ATOM = None
CATEGORY_FEED_ATOM = None
TRANSLATION_FEED_ATOM = None
AUTHOR_FEED_ATOM = None
AUTHOR_FEED_RSS = None

# Blogroll
LINKS = (('PLV', 'http://plv.csail.mit.edu/'),
         ('Bedrock', 'http://plv.csail.mit.edu/bedrock/'),
         ('Fiat', 'http://plv.csail.mit.edu/fiat/'),
         ('Ur/Web', 'http://plv.csail.mit.edu/bedrock/ur/'),
         ('Kami', 'http://plv.csail.mit.edu/kami/'),)

# Social widget
SOCIAL = None

DEFAULT_PAGINATION = 10

# Uncomment following line if you want document-relative URLs when developing
RELATIVE_URLS = True
