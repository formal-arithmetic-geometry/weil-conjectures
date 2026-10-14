## What changed

Pruned the unused project-specific public import from the empty module
Sheaf.RingTheory.ZariskisMainAway and updated its module documentation.
The duplicate Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime and its three
caller conversions were already repaired upstream; this delivery completes the
remaining dependency cleanup. Change record:
coord/changes/zariskisMainAway-unused-imports.md.

Compiled the edited module and the original, unchanged sole remaining importer
Sheaf.RingTheory.QuasiFiniteIntegralClosureOpen together with lcompile.py --all:
exit 0, no warnings. The temporary importer source is not delivered.

## Proved and sorry left

Zero holes closed, zero holes added, zero split off. The assigned module has
no declarations and no sorry. No intermediate theorem is introduced.
The unchanged importer still has its existing hole
Algebra.quasiFinite_integralClosure_open, node
lem-weil-pbc-quasi-finite-ring-map-integral-closure-open; it is not modified or
delivered here. This is an import-pruning repair, not a new mathematical proof.

## No longer needed

Removed imports from the assigned module:

- Sheaf.RingTheory.QuasiFiniteAtPrime.

The compatibility module now exposes Mathlib alone. This removes its Sheaf dependency edge;
QuasiFiniteAtPrime remains necessary elsewhere in the library. No mathematical
node becomes unnecessary beyond the already retired duplicate wrapper. The
node lem-weil-pbc-integral-closure-zariski-main-away already points to Mathlib.
Its unit route and the three caller-local Mathlib conversions are unchanged.

## Where the brief, the DAG or earlier work was wrong

The mathematical wrapper repair was already landed, as recorded by
coord/changes/zariskisMainProperty-wrapper-retirement.md. Earlier retries treated
that as preventing any necessary work, but the obsolete Sheaf dependency in the retired
module can still be pruned. The sole current importer independently imports its
statement dependencies and compiles unchanged against this pruning, so there
are no forced adaptations. The separate scheme predicates mentioned in review
#1428 belong to Sheaf.AlgebraicGeometry.QuasiFiniteMorphism; this held module's
cleanup does not force a change to that interface, and it is not changed here.
No DAG statement or proof change, new node, arbitrary witness, or target signature
change is needed. The second reading is left to the independent reader.

The first dry run after removing both imports exposed a limitation of the
appended axiom probe on an import-free module (the module itself compiled).
The final cleanup preserves the Mathlib compatibility import and removes only
the obsolete Sheaf import.

## Second reading by R4

1. Compared the complete delivered module with the repository using `diff -u`.
   There are no existing declarations, signatures or definitions in either version.
   The only changes are removal of the public QuasiFiniteAtPrime import and the
   module documentation. The public-interface change is explicitly declared in
   coord/changes/zariskisMainAway-unused-imports.md. Verdict: pass.
2. Independently compiled the edited module and a temporary, byte-identical copy
   of the repository's sole remaining direct importer,
   Sheaf.RingTheory.QuasiFiniteIntegralClosureOpen, with `lcompile.py --all`.
   Both compile with exit 0 and no warnings (1.4 and 1.7 seconds respectively).
   The assigned module contains no declarations, sorry, axiom, unsafe, opaque,
   implemented_by or extern; there is therefore no declaration for a
   `#print axioms` probe. The temporary importer was removed before delivery.
   Verdict: pass; no proof holes are closed or added.
3. There are no split-off statements, new declarations, new nodes or chosen data
   to test or search for duplicates. The report lists the unchanged importer's
   existing hole separately and does not count it as delivered work. Verdict: pass.
4. Checked all source references to the module: the sole direct importer already
   publicly imports QuasiFiniteAtPrime independently. The retired wrapper's
   mathematical route already uses Mathlib directly; no shorter mathematical
   proof remains to implement in this empty module. The removed Sheaf edge is
   completely listed under No longer needed. The remaining Mathlib public import
   preserves the existing compatibility entry point and allows the delivery
   tool's axiom-probe machinery to run, as the first reader documented.
   Read dag/units/sk-thm-p1.json, including its realized route: unchanged.
   Verdict: pass as dependency cleanup, not mathematical proof progress or
   pruning of an entire module from the targets' closure.
5. Read lem-weil-pbc-integral-closure-zariski-main-away.json: its lean record
   already names Mathlib's ZariskisMainProperty.of_finiteType; its proof and
   proof_origin explicitly describe caller-local conversion and the empty
   compatibility module. No proof dependency is newly bypassed by this import
   cleanup, so no node edit is needed. Verdict: pass.

Second reading changed only this report by adding the independent review and
fresh compilation evidence; the Lean module and change record required no repair.
