#!/usr/bin/env python
#
# Mark the nodes in a protocol graph if they actually appear in the
# proof graph.
# Nik Sultana, Cambridge University Computer Lab, October 2013
#
# NOTE highly unpolished. Notes for using this are included
#  with my thesis files, I need to include them here too.
#  The DOT file is assumed to be generating by my tptp_graph
#  tool, distributed with Isabelle.

import sys
import string
import re

#DOT (GraphViz) representation of a protocol trace associated with a problem.
protocol_dot = sys.argv[1]
#List of names of nodes appearing in the proof trace.
proof_nodes_file = sys.argv[2]

HIGHLIGHT_COLOUR = 'yellow'
NONHIGHLIGHT_COLOUR = 'lightgray'

proof_nodes = []

FD = open(proof_nodes_file, 'r')
for line in FD:
  if line <> '':
    proof_nodes.append(line.strip('\n'))
FD.close()

matcher = re.compile('^"(.+)" \[(.+)$') #e.g. "1" [shape="house", style="filled", label="1"];

FD = open(protocol_dot, 'r')
for line in FD:
  line = line.strip('\n')
  matching = matcher.match(line)
  if matching <> None:
    if matching.group(1) in proof_nodes:
      print '"' + matching.group(1) + '" [fillcolor=' + HIGHLIGHT_COLOUR + ', ' + matching.group(2)
    else:
      print '"' + matching.group(1) + '" [fillcolor=' + NONHIGHLIGHT_COLOUR + ', style="filled", ' + matching.group(2)
  else:
    print line

FD.close()
