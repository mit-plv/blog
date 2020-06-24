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
EXTRA_PATH_METADATA = {}
EXTRA_PATH_METADATA['static/plv.png'] = {'path': 'theme/img/profile.png'}
#########################

## reST tweaks ##

from docutils import nodes
from docutils.parsers.rst import roles
from docutils.writers._html_base import HTMLTranslator

class htmlnode(nodes.inline):
    pass

def visit_htmlnode(self, node):
    self.body.append(self.starttag(node, node['tag'], ''))
def depart_htmlnode(self, node):
    self.body.append('</{}>'.format(node['tag']))

HTMLTranslator.visit_htmlnode = visit_htmlnode
HTMLTranslator.depart_htmlnode = depart_htmlnode

def html_role(role, rawtext, text, _lineno, _inliner, options={}, _content=[]):
    options['tag'] = role
    roles.set_classes(options)
    return [htmlnode(rawtext, text, **options)], []

roles.register_canonical_role('del', html_role)
roles.register_canonical_role('kbd', html_role)

## Alectryon support ##

import sys
from os import path
sys.path.insert(0, path.join(path.dirname(__file__), "alectryon"))

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

import alectryon
import alectryon.docutils
from alectryon.html import ASSETS

alectryon.docutils.register()
alectryon.docutils.LONG_LINE_THRESHOLD = 64

alectryon_assets = path.relpath(ASSETS.PATH, PATH)

STATIC_PATHS.append(alectryon_assets)
EXTRA_PATH_METADATA[alectryon_assets] = {'path': 'static/alectryon/'}

for pth in ("tango_subtle.css", "tango_subtle.min.css"):
    rel = path.join(alectryon_assets, pth)
    EXTRA_PATH_METADATA[rel] = {'path': path.join('theme/pygments/', pth)}
#######################
