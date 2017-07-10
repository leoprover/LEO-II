#!/bin/bash
if [ "$1" = profile ]
then
  echo "building (profiling) native version of Leo2."
  OUT=leo.p.native
  TAG="-tag profile"
else
  echo "building native version of Leo2."
  OUT=leo.native
  TAG=
fi
FLAGS=
if [ "$extunix" = "true" ]; then
  echo "...with extunix"
  EXTUNIX=$(ocamlfind query extunix)
  FLAGS="-cflags -I,$EXTUNIX -lflags -I,$EXTUNIX -lib extunix"
  PPFLAG="-DEXTUNIX"
fi
#FIXME this uses non-native camlp4 (and thus is slower).
#      see Makefile about using native camlp4.
ocamlbuild $TAG $FLAGS -pp "camlp4o pa_macro.cmo $PPFLAG" \
  -Is general,calculus,datastructure,interfaces,interfaces/translation,interfaces/minisat,parser-hotptp,toplevel toplevel/$OUT \
 && cp -L $OUT ../bin/leo \
 && rm $OUT
echo "done."
