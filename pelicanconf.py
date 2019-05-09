#!/usr/bin/env python
# -*- coding: utf-8 -*- #
from __future__ import unicode_literals

AUTHOR = 'PLV'
SITENAME = 'PLV@MIT'
SITEURL = ''
FEED_DOMAIN = SITEURL

LOCALE = ('usa', 'en_US', 'en_US.utf8')
TIMEZONE = 'America/New_York'
DEFAULT_LANG = 'en'

PATH = 'content'
THEME_TEMPLATES_OVERRIDES = ['templates']
STATIC_PATHS = ['images', 'static']
CUSTOM_CSS = None # Set using a template override (custom_head.html)
FILENAME_METADATA = r'(?P<date>\d{4}-\d{2}-\d{2})-(?P<slug>.*)'

THEME = 'flex-theme'

# Feed generation is usually not desired when developing
FEED_ALL_ATOM = None
CATEGORY_FEED_ATOM = None
TRANSLATION_FEED_ATOM = None
AUTHOR_FEED_ATOM = None
AUTHOR_FEED_RSS = None

LINKS = (('Bedrock', 'http://plv.csail.mit.edu/bedrock/'),
         ('Fiat', 'http://plv.csail.mit.edu/fiat/'),
         ('Ur/Web', 'http://plv.csail.mit.edu/bedrock/ur/'),
         ('Kami', 'http://plv.csail.mit.edu/kami/'),)

SOCIAL = ()

DEFAULT_PAGINATION = 10

# Document-relative URLs when developing
RELATIVE_URLS = True

## Flex-theme specific ##
SITETITLE = SITENAME
SITESUBTITLE = SITEDESCRIPTION = "Updates from Adam Chlipala's PLV group at MIT"

BROWSER_COLOR = '#333'
USE_GOOGLE_FONTS = False

MAIN_MENU = True
ROBOTS = 'index, follow'

COPYRIGHT_YEAR = 2019
COPYRIGHT_NAME = 'PLV @ MIT'
CC_LICENSE = None
# {
#     'name': 'Creative Commons Attribution',
#     'version': '4.0',
#     'slug': 'by',
#     'local_icons': True
# }

PYGMENTS_STYLE = 'emacs'

MENUITEMS = (('PLV (main site)', 'http://plv.csail.mit.edu/'),)


EXTRA_PATH_METADATA = {
    'static/plv.png': {'path': 'theme/img/profile.png'}
}
#########################

## Alectryon support ##
import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from alectryon.externals import docutils_support

docutils_support.register()
STATIC_PATHS.append('../alectryon/alectryon.css')
EXTRA_PATH_METADATA['../alectryon/alectryon.css'] = {'path': 'static/alectryon.css'}
#######################
