/* File: Ointerface.cc
 * Author: Chad E. Brown, Nov 30, 2010 -- Updated Nov, 2011 for Minisat 2.2.0
 * OCaml interface to MiniSat used by Satallax
 * Code based on Main.C in MiniSat (Niklas Eeen, Niklas Sorensson)
 * and MiniSat-ocaml (Flavio Lerda, Pietro Abate).
 * Also used Chapter 25 of _Practical OCaml_ Joshua B. Smith.
 * The most useful thing I found was the tutorial "How to wrap C functions to OCaml" by Florent Monnier:
 * http://www.linux-nantes.org/~fmonnier/ocaml/ocaml-wrapping-c.php
 */

#include <ctime>
#include <cstring>
#include <stdint.h>
#include <errno.h>

#include <signal.h>
#include <zlib.h>

#include "utils/Options.h"
#include "core/Solver.h"
#include "simp/SimpSolver.h"

extern "C" {
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/fail.h>
#include <caml/callback.h>
}

using namespace Minisat;
SimpSolver*    solver;
vec<Lit>       lits;

bool redirect = true;

void printState () {
  printf("minisat state:\nnClauses: %d\nnVars:%d\n",(*solver).nClauses(),(*solver).nVars());
}

extern "C" value minisat_init(value _l) {
  CAMLparam1(_l);
  int v = Int_val(_l);
  if (solver != NULL) { delete solver; }
  solver = new SimpSolver;
  /*  (*solver).verbosity = 0; */
  (*solver).use_elim = false;
  if (redirect && (v < 10)) { freopen("/dev/null", "w", stderr); redirect = false; } // redirect stderr to avoid reportf info being printed
  CAMLreturn(Val_unit);
}

Lit litof (int p) {
  int var = abs(p)-1;
  //  printf("litof %d\n",p);
  while (var >= (*solver).nVars()) {
    Var v = (*solver).newVar();
    //    (*solver).setFrozen(v,true);
    // printf("made lit %d\n",v);
  }
  //  printf("returning lit %d\n",p);
  return (mkLit(var,(p > 0)));
}

extern "C" value minisat_addLit(value _l) {
  CAMLparam1(_l);
  int p = Int_val(_l);
  lits.push(litof(p));
  CAMLreturn(Val_unit);
}

extern "C" value minisat_addClause() {
  bool ret = (*solver).addClause_(lits);
  lits.clear();
  return Val_bool(ret);
}

// add unit clause
extern "C" value minisat_addClause1(value _l) {
  CAMLparam1(_l);
  int p = Int_val(_l);
  //  printf("here1 %d\n",p);
  bool ret = (*solver).addClause(litof(p));
  //  printf("here2 %d\n",p);
  CAMLreturn(Val_bool(ret));
}

// add binary clause
extern "C" value minisat_addClause2(value _l1,value _l2) {
  CAMLparam2(_l1,_l2);
  int p1 = Int_val(_l1);
  int p2 = Int_val(_l2);
  //  printf("here1 %d %d\n",p1,p2);
  bool ret = (*solver).addClause(litof(p1),litof(p2));
  //  printf("here2 %d %d\n",p1,p2);
  CAMLreturn(Val_bool(ret));
}

// add binary clause
extern "C" value minisat_addClause3(value _l1,value _l2,value _l3) {
  CAMLparam3(_l1,_l2,_l3);
  int p1 = Int_val(_l1);
  int p2 = Int_val(_l2);
  int p3 = Int_val(_l3);
  //  printf("here1 %d %d %d\n",p1,p2,p3);
  bool ret = (*solver).addClause(litof(p1),litof(p2),litof(p3));
  //  printf("here2 %d %d %d\n",p1,p2,p3);
  CAMLreturn(Val_bool(ret));
}

extern "C" value minisat_search () {
  //  printf("calling minisat_search\n");
  //  printState();
  if (!(*solver).simplify()){
    return Val_bool(0);
  }
  bool ret = (*solver).solve(true,true);
  //  printf("minisat_search: %d\nnClauses: %d\nnVars:%d\n",ret,(*solver).nClauses(),(*solver).nVars());
  //  printState();
  return Val_bool(ret);
}

// search, with 1 assumed lit
extern "C" value minisat_search1 (value _l) {
  CAMLparam1(_l);
  int parsed_lit = Int_val(_l);
  int var = abs(parsed_lit)-1;
  bool ret = true;
  if (var < (*solver).nVars()) {
    vec<Lit> a;
    a.push(mkLit(var,(parsed_lit > 0)));
    ret = (*solver).solve(a,true,true);
  }
  CAMLreturn(Val_bool(ret));
}

// get the value of a variable
// return value: 0 true, 1 false, 2 undefined
extern "C" value modelValue (value _l) {
  CAMLparam1(_l);
  int parsed_lit = Int_val(_l);
  int var = abs(parsed_lit)-1;
  int ret = 3;
  if (var < (*solver).nVars()) {
    ret = toInt((*solver).modelValue(mkLit(var,(parsed_lit > 0))));
  }
  CAMLreturn(Val_int(ret));
}
