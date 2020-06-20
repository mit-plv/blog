#!/usr/bin/env python
# -*- coding: utf-8 -*- #
from __future__ import unicode_literals
import os

AUTHOR = 'PLV'
SITENAME = 'PLV@MIT'

# If your site is available via HTTPS, make sure SITEURL begins with https://
SITEURL = os.getenv('SITE_URL', default='')
FEED_DOMAIN = SITEURL

LOCALE = ('usa', 'en_US', 'en_US.utf8')
TIMEZONE = 'America/New_York'
DEFAULT_LANG = 'en'

PATH = 'content'
THEME_TEMPLATES_OVERRIDES = ['templates']
STATIC_PATHS = ['images', 'static']
CUSTOM_CSS = None # Set using a template override (custom_head.html)
FILENAME_METADATA = r'(?P<date>\d{4}-\d{2}-\d{2})_(?P<slug>.*)'

THEME = 'flex-theme'
PYGMENTS_STYLE = 'tango_subtle'

EXTRA_PATH_METADATA = {}
for pth in ("tango_subtle.css", "tango_subtle.min.css"):
    EXTRA_PATH_METADATA['static/' + pth] = {'path': 'theme/pygments/' + pth}

# Feed generation is usually not desired when developing
FEED_ALL_ATOM = None
CATEGORY_FEED_ATOM = None
TRANSLATION_FEED_ATOM = None
AUTHOR_FEED_ATOM = None
AUTHOR_FEED_RSS = None

LINKS = ()
#          ('Bedrock', 'http://plv.csail.mit.edu/bedrock/'),
#          ('Fiat', 'http://plv.csail.mit.edu/fiat/'),
#          ('Ur/Web', 'http://plv.csail.mit.edu/bedrock/ur/'),
#          ('Kami', 'http://plv.csail.mit.edu/kami/'),)

SOCIAL = ()#(('rss', SITEURL + '/feeds/all.atom.xml'),)

DEFAULT_PAGINATION = 10

# Document-relative URLs when developing
RELATIVE_URLS = True

## DOCUTILS config ##

DOCUTILS_SETTINGS = {
    'halt_level': 3, # Error
    'warning_stream': None # stderr
}

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

MENUITEMS = (('PLV (main site)', 'https://plv.csail.mit.edu/'),
             ('Archives', '/archives.html'),
             ('Categories', '/categories.html'),
             ('Tags', '/tags.html'))
EXTRA_PATH_METADATA['static/plv.png'] = {'path': 'theme/img/profile.png'}
#########################

## Alectryon support ##
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "alectryon"))

import alectryon.pygments
alectryon.pygments.add_tokens({
    'tacn-solve': ['maps_neq', 'linear_arithmetic',
                   'equality', 'model_check_done'],
    'tacn': [
        'same_structure', 'inList', 'inductN', 'instantiate_obvious1',
        'instantiate_obvious', 'instantiate_obviouses', 'induct', "invert'",
        'invertN', 'invert', 'invert0', 'invert1', 'invert2', "maps_equal'",
        'fancy_neq', 'removeDups', 'doSubtract', 'simpl_maps', 'simplify',
        'propositional', 'cases', 'maps_equal', 'first_order', 'sets0', 'sets',
        'model_check_invert1', 'model_check_invert', 'singletoner', 'closure',
        'model_check_step0', 'model_check_step', 'model_check_steps1',
        'model_check_steps', 'model_check_finish', 'model_check_infer',
        'model_check_find_invariant', 'model_check', 'total_ordering',
        'maybe_simplify_map', "simplify_map'", 'simplify_map',
        'excluded_middle', 'dep_cases'
    ]
})

import alectryon.docutils
alectryon.docutils.register()

STATIC_PATHS.append('../alectryon/alectryon.css')
STATIC_PATHS.append('../alectryon/alectryon-slideshow.js')
EXTRA_PATH_METADATA['../alectryon/alectryon.css'] = {'path': 'static/alectryon.css'}
EXTRA_PATH_METADATA['../alectryon/alectryon-slideshow.js'] = {'path': 'static/alectryon-slideshow.js'}
#######################
