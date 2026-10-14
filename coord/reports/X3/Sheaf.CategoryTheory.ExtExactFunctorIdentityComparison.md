## What changed

Listed upstream review #1424 repair of
Sheaf.CategoryTheory.ExtExactFunctorIdentityComparison. The proof applies Mathlib
LocalizerMorphism.equiv_smallShiftedHomMap directly to the termwise comparison
F ≅ identity, identifies its components on single complexes degreewise, and
cancels the inverse comparison. The candidate combines the two termwise
isomorphisms before checking shift compatibility and simplifies cancellation.
All existing signatures and visibility are unchanged. In particular, retained
commShift_of_localization: HigherDirectImageRawPullbackIdentity imports this
private helper with import all.

The repository advanced while this item was being worked on: its current
version already contains an independently landed direct localization proof
from M3, with the same single public Mathlib import. Relative to that version,
this delivery simplifies the existing proof and updates its node's proof and
proof_origin; it does not newly remove a dependency.

## Proved and sorry left

CategoryTheory.Abelian.Ext.exactFunctorIdentityComparison has a complete proof.
The module already had no sorry in the current repository: this is a listed
repair, not a newly closed hole. Holes closed: 0. Holes added: 0. Split off: 0.
No sorry remains in the module; no new modules or declarations were added.
The independent reader compiled the module cleanly with lcompile.py and checked
#print axioms for both declarations: only propext, Classical.choice, Quot.sound.
The delivery also probes all declarations automatically.

## No longer needed

None newly removed relative to the current repository. The earlier candidate
removed Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison and node
lem-weil-pbc-ext-exact-functor-composition-comparison, but that pruning is already
present in the current M3 baseline and must not be counted twice. The current
proof_deps are the exact-functor factorization and localized Ext nodes. No unit
statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The assignment describes an unproved module, but this is a listed repair and
both the earlier and current checkouts contain a complete proof. The suggested
mapExactFunctor_eq_of_iso and mapExactFunctor_id declarations are absent from
pinned Mathlib and the source library. A fresh second-reader search for natural
transformation, isomorphism and identity variants confirms no shorter pinned
Ext API: online Loogle lists id_mapExactFunctor and
mapExactFunctor_comp_mk₀_natTransApp from a newer Mathlib, absent in the pinned
Ext.Map source. The proof therefore uses the existing localization API directly.
The initial report's newly pruned import claim became stale after M3 landed;
the second reader corrected it. No statement was changed.

## Second reading by X3

1. Compared the entire delivered module and node with the repository using
   diff. Both declaration signatures, visibility, docstrings, options and all
   definitions are unchanged byte for byte. Only the main theorem's proof
   changes. No change record or caller adaptation is necessary. Verdict: pass.
2. Read the localization calculation, degreewise single-complex comparison,
   inverse cancellation and final Ext.ext conversion. Compiled locally with no
   errors or warnings. No sorry, axiom, unsafe, opaque, implemented_by or extern
   occurs. Explicit axiom prints for the main theorem and retained private
   helper show only the three allowed axioms. Verdict: pass.
3. No statements were split off or added, and no data is chosen from an unproved
   existence theorem. For n = 0 the statement is the naturality equation for
   e; for identity e and zero x the same cancellation calculation applies.
   Fresh msearch Loogle and grep searches and rg of the pinned Mathlib/source
   library confirmed the suggested higher-level API is unavailable. Verdict:
   pass; no new statement or DAG node needs review.
4. The proof uses Mathlib directly, with no Sheaf proof-dependency imports.
   Its sole public import Ext.Map is required by the public statement's
   mapExactFunctor. The apparently unused private helper is retained because
   HigherDirectImageRawPullbackIdentity uses it through import all. Read
   dag/units/sk-thm-p1.json, including realized: this auxiliary identity
   comparison bypasses none of its realized statement or steps. Compared old
   and new proof_deps: identical, so no newly pruned node. Verdict: pass after
   correcting the stale pruning claim in the report.
5. Read the node and its dependency records. Its unchanged Lean statement
   matches the theorem. The two proof steps describe the termwise localization
   calculation and component cancellation actually used; proof_deps is their
   union, and proof_origin identifies this candidate's direct Mathlib route.
   No new node is delivered. Verdict: pass.

Second reading changed only this report: corrected attribution of the direct
route and pruning against the current M3 baseline, and recorded independent
checks. The submitted Lean proof and node needed no repair.
