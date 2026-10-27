## What changed

Proved `AlgebraicGeometry.flat_relation_invariant_open_complement` in
`Sheaf.AlgebraicGeometry.FlatRelationInvariantOpenComplement`, with its signature unchanged.
The proof follows Stacks Project `groupoids.tex`, Tag 0APB,
`lemma-second-observation`: construct the actual vanishing-ideal subscheme of
`s⁻¹(Hᶜ)`, identify its image under `t`, use the existing quasi-compact-image
specialization theorem, lift generalizations along both flat maps, and take complements.
The original common section and invariance hypotheses prove the two initial set claims.
No object is chosen from an unproved existence statement.

Updated the existing node's second proof step and proof dependencies to describe the
Mathlib quasi-compactness instances actually used. No public imports, definitions,
signatures, or other modules changed. The unit route is unchanged.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.flat_relation_invariant_open_complement`
(node `lem-a1-flat-relation-invariant-open-complement`). All nine conjuncts are proved.
Zero holes remain in the delivered module; zero holes added; zero split off.
The final single-file server compile succeeded in 3.9 seconds without warnings.

## No longer needed

Removed these redundant private proof imports:
- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Mathlib.Topology.Compactness.Compact`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`

The explicit affine-open compactness argument is replaced by existing instances:
`QuasiCompact I.subschemeι`, `QuasiCompact t` from affineness, and composition.
Thus the item no longer explicitly needs the planned proof dependencies
`lem-weil-pbc-affine-scheme-qcqs`, `lem-weil-pbc-closed-in-quasi-compact`, or
`def-weil-closed-immersion`; `pqf-def-affine-morphism` remains a statement dependency.
No library module is withdrawn, and no dependency still used by an upstream theorem
is removed. The generic affine-morphism permanence leaf now records the instance used.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement needed correction. The quasi-compactness verification in
step 2 was already available through Mathlib instances. The assumptions that H is
quasi-compact and s is affine are unnecessary for this proof but remain unchanged.
Empty schemes, H empty or full, and K empty require no special cases in the proof.
Searches using leanfinder, loogle, launcher grep, and repository rg found no existing
whole-theorem match. The existing source-library closure-specialization result and
Mathlib `Flat.generalizingMap` supply the non-elementary steps directly.

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
