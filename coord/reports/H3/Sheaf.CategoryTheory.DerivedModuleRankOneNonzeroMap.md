## What changed

`Sheaf.CategoryTheory.DerivedModuleRankOneNonzeroMap` replaces its one original
proof hole with a homology nonvanishing argument followed by the fixed-degree
cycle-to-map step. Its existing signature and public imports are unchanged.
It adds proof-only imports of `Sheaf.CategoryTheory.DerivedModuleNonzeroClassMap`
and `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
The new module states the remaining intermediate theorem with its cycle proof
in words and source, Stacks Project Tag 064B (projective-source comparison).

## Proved and sorry left

Hole closed: `CategoryTheory.derivedModule_rankOne_nonzero_map` (1 of 1 original
holes). Hole added and still open: `CategoryTheory.derivedModule_nonzero_class_map`,
in `Sheaf.CategoryTheory.DerivedModuleNonzeroClassMap`, node
`new-stage3-derived-module-rank-one-nonzero-map-chain`.
This is a decomposition, not a completed proof: one upper hole closed, one strictly
intermediate hole added, net zero holes closed. The original module has no sorry;
its axiom closure still contains sorryAx from the intermediate theorem.

## No longer needed

No old proof dependency node or module is pruned: the baseline proof_deps is empty.
No existing public import is removed. In the new module, the redundant explicit
Basic import was removed; the upstream homology zero criterion was replaced with
Mathlib's HomologySequence because only the latter is needed for its statement.
The upstream criterion is imported directly, proof-only, by the item that uses it.

## Where the brief, the DAG or earlier work was wrong

The previous report described an older import layout: the current repository item
has only three public imports and no homology-sequence import to remove. Tag 0F5X
asserts generation; Tag 064B supplies the projective-source comparison used by the
cycle proof. The new node's prose originally asserted detection of the specified
class, stronger than its Lean conclusion; its prose now states the precise
existence conclusion. The construction in its docstring still explains detection
as the reason for nonvanishing. The target proof attribution is H3; original
creation and statement attribution remain H4.

## New nodes

`new-stage3-derived-module-rank-one-nonzero-map-chain` is the fixed-degree
cycle-to-derived-map step, with the given nonzero homology class as input. It is
strictly part of the original argument: the item itself proves existence of such
a degree and class. Its source is Tag 064B; the docstring constructs a cycle map
and proves nonvanishing by homology. Searches using LeanFinder, valid Loogle
patterns and rg found localization comparisons but no direct replacement;
LeanSearch returned an internal server error, recorded as unavailable.
The additive declaration is recorded in
`coord/changes/derivedModule_nonzero_class_map.md`.

## Second reading by H3

1. Compared the item's complete module and node with the repository using diff.
   The existing declaration signature and docstring are byte-for-byte unchanged;
   public imports are unchanged. No definition or target statement changes. The
   intermediate declaration is new on this baseline, with its own module/node.
   Verdict: pass.
2. Compiled both modules in import order through lcompile.py, without errors or
   warnings. Inspected all declarations: one named theorem has exactly `by sorry`,
   no definitions or forbidden constructs. A scratch copy printed axioms of both
   theorems: only propext, Classical.choice, Quot.sound and sorryAx. Verdict: pass
   as a decomposition; the target is not axiom-clean yet.
3. Checked the intermediate statement and its complete cycle proof in words.
   For a zero ring, zero homology or zero object its nonzero-class premise cannot
   hold. For a single module in degree n the map is evaluation at a nonzero class;
   the positive shift n moves that degree to zero. Negative n and noncommutative
   rings use the same left-linear map s ↦ s • z. ULift preserves the free rank-one
   module at the required universe. Tag 064B gives the comparison for a bounded
   projective source. Mathlib, upstream and Sheaf searches revealed no complete
   existing theorem; injective-target surjectivity is the opposite direction.
   Verdict: true, needed, strictly intermediate, not a restatement.
4. Read the top-down reduction and searched for shorter routes. The homology-zero
   criterion is already proved upstream; only cycle realization remains open.
   Imports are now scoped to their use; the baseline has no old proof_deps to
   prune. Read dag/units/sk-prop-sf-cbc.json: realized.statement and realized.steps
   are empty, and no unit statement or route is changed. Its referenced blueprint
   source file is absent locally; the unit record contains the full statement.
   Verdict: pass on the available unit record.
5. Compared both node records with the Lean proof. The item uses precisely the
   new chain node; both proof_deps are the unions of their proof-step uses. The
   new node has source, proof, searches, provenance, blueprint parent, chapter,
   unit and the matching Lean record. Existing node changes are limited to proof,
   proof_deps and proof_origin. Verdict: pass.

Second-reading repairs: corrected the new node's prose to its exact Lean strength;
made the upstream criterion a direct proof-only import of the item; minimized the
new module's imports; removed the unnecessary file-level linter override by using
`have` for the local Subsingleton proof; corrected the report and change record
against the actual repository baseline; recorded fresh searches. No Lean theorem
signature or existing docstring changed, and no additional holes were introduced.
