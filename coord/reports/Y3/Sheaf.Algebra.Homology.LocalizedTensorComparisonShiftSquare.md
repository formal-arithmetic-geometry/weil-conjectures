## What changed

Repaired the reduction in `Sheaf.Algebra.Homology.LocalizedTensorComparisonShiftSquare`.
Its existing theorem signature and public import are unchanged. The two new proof-only
imports separate model transport from the ordinary tensor comparison square.
`LocalizedTensorComparisonShiftSquareData` now transports a model along a prescribed
isomorphism L ≅ K[-n] and fixes the homology map explicitly. Its statement does not
involve the later tensor map t or its target N. `LocalizedTensorComparisonShiftSquareTransport`
now states only the ordinary complex-map square for the canonical tensor and
scalar-extension shift isomorphisms, with no derived models. The target constructs
its target homology isomorphism explicitly, applies homology-shift naturality,
and composes the two squares. Scoped unused-section-variable lint suppression
preserves the original HasDerivedCategory A hypothesis, which this reduction does not need.

## Proved and sorry left

Original hole closed: `ModuleCat.exists_localizedTensorComparison_shift_square`.
New holes added:
- `ModuleCat.exists_shift_square_data`, node
  `lem-pc-localized-tensor-comparison-shift-square-data`.
- `ModuleCat.localizedTensorComparison_shift_transport`, node
  `lem-pc-localized-tensor-comparison-shift-square-transport`.

This is a decomposition: one original hole is closed and two strictly smaller holes
are added, for a source-level net of -1. The target still depends on these holes;
it is not an axiom-free completed proof. No data-bearing definitions are introduced;
the model witness is eliminated only inside the existential proof and its comparison
is fixed up to the source isomorphism used downstream. The final ledger accounting
belongs to the maintainer.

## No longer needed

None of the old proof-dependency nodes or original imports is pruned. Both original
definition nodes remain used in the canonical constructions and model fields.
The new data module imports only BaseDerivedTensorCohomologyModel publicly;
the two target imports are proof-only. No existing public import is removed.

## Where the brief, the DAG or earlier work was wrong

The earlier transport statement was false. Its hcoh hypotheses were the inverse
identities of isomorphisms, hence automatic. They imposed no compatibility with
the comparison map. At n=0 over the rationals, take degree-zero unit complexes,
the identity coefficient and tensor maps, and the usual identity derived model.
Negating a canonical target isomorphism preserves all inverse identities but negates
the nonzero comparison, contradicting the proposed universal conjugacy. Replaced
this claim rather than accepting its sorry as a valid dependency. The earlier
short docstrings and node proof plans did not specify a construction or justify
compatibility; the revised statements, detailed docstrings and nodes do.
The upstream generic shift-compatibility instance in
WeilConjectures.Mathlib.Algebra.Homology.BifunctorShift supplies ingredients for the
ordinary square, but matching its bifunctor and monoidal presentations was not closed.

## New nodes

`lem-pc-localized-tensor-comparison-shift-square-data` records model transport
through an arbitrary prescribed complex isomorphism to an inverse shift, with a
fixed homology comparison. It is the derived source half of the argument.

`lem-pc-localized-tensor-comparison-shift-square-transport` records only the
ordinary tensor complex-map square for canonical shift maps. It is the ordinary
target half of the argument. Both are new relative to the repository, have their
own modules and verbatim Lean statements, and retain the original chapter and unit.
No existing interface changed, so no change record or forced adaptation is needed.

## Second reading by Y3

1. Compared the target module with the repository version using diff. The existing
   theorem signature is byte-for-byte unchanged, with its original public import
   retained. Only its proof, two proof imports and declaration-scoped options changed.
   The two helper modules and their nodes are new, so their corrected statements
   change no existing interface. Verdict: pass.
2. Checked all modules for forbidden declarations and hollow definitions. Only the
   two named helper theorems retain whole-proof sorry, with matching nodes and detailed
   source/proof docstrings. The target proof has no sorry. Single-file compilation and
   scratch #print axioms checks passed: all three modules compiled without warnings
   (2.0 s, 3.9 s and 19.2 s). Each declaration uses only propext, Classical.choice,
   Quot.sound and the expected sorryAx. Verdict: pass as a decomposition.
3. Rejected the old arbitrary-isomorphism transport claim. The new source transport
   fixes its homology map and the new ordinary square fixes both complex shift maps.
   Checked n=0, zero complexes, t=0, and arbitrary signs of prescribed complex isomorphisms;
   no flatness or K-flatness is introduced. Repeated LeanFinder, Loogle and grep searches
   with derived-counit transport and total-complex comparison queries; inspected the
   upstream generic shift instance. The two remaining steps are true, needed and
   strictly part of the argument, not renamed copies of the target. Verdict: pass.
4. Read the target from the top downward. The proof uses canonical tensor shift and
   Mathlib homology-shift naturality and reduces the derived source and ordinary target
   separately. Imports are scoped to statement or proof needs. No old dependency is
   silently removed. sk-thm-picard-semicon's realized fields are empty in the baseline
   and are unchanged; the original model-transport and tensor-naturality route is kept
   below the unit level. Verdict: pass.
5. Updated the target node's proof, proof_deps and proof_origin to the actual reduction.
   Rewrote each new node's self-contained statement, proof plan, source and verbatim
   lean.statement, with actual repeated search results. Proof-dependency lists are the
   unions of their steps' uses. Verdict: pass.

Second reading changed the false transport interface into a canonical ordinary
complex square, changed the data interface into prescribed model transport,
rewrote the real combining proof, expanded helper proof docstrings, minimized the
new data import and corrected all three node proof records and the progress report.

Validation: deliver3.py --no-push printed OK; review class CODEX because of the new
modules and nodes. The mandatory independent delivery review therefore remains in place.
