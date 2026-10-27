## What changed

Completed AlgebraicGeometry.etale_fibre_product_pair_refinement with its original
signature. Constructed the canonical graph and both graph sections, proved their
open/closed immersion properties with the declared Mathlib leaves, deleted their
closed complements, and proved the Cartesian squares using open inverse images and
vertical pullback pasting. The common open is the intersection of the two opens.
Proved the canonical residue-field maps are isomorphisms from surjectivity on stalks
and injectivity of field homomorphisms. Five proved private helpers keep the proof
readable. No definitions, instances, attributes or other module bodies changed.

Pruned imports as recorded in coord/changes/D3-etale-fibre-product-pair-imports.md.
The unchanged sole direct importer CoherentFormalGenerationFlatness compiled against
the changed module in 13.4 seconds, and its sandbox copy was then removed. The item
compiled in 4.3 seconds. The axiom audit printed exactly propext, Classical.choice,
Quot.sound. Final delivery reruns compilation after removing the audit command and
fixing a minor unnecessary-simpa warning.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.etale_fibre_product_pair_refinement
(lem-trf-etale-fibre-product-pair-refinement).
One of one holes proved; zero holes added, zero split off, zero sorry left in the
item or elsewhere in this delivery. All five private helpers are completely proved.

## No longer needed

Removed imports:
- WeilConjectures.AlgebraicGeometry.BaseChangeConventions: neither the statement
  nor the proof uses its module-base-change, geometric-fibre or section constructions.
- Mathlib.AlgebraicGeometry.Morphisms.Proper: only separatedness is needed, now
  imported directly and publicly from Morphisms.Separated.
- Mathlib.AlgebraicGeometry.ResidueField and Mathlib.AlgebraicGeometry.Scheme:
  available through the retained statement imports.
- Mathlib.AlgebraicGeometry.OpenImmersion and
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: available through
  the retained statement imports.

No DAG proof dependency or unit is bypassed: all listed dependencies are Mathlib
leaves used by the proof. No module withdrawal or declaration deletion is requested.
The explicit F1 isomorphism with X times_S M2 is unnecessary: successive pullback
base-change instances and projection identities suffice. This prunes only that
unused construction, not the fibre-product node.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable dependency was found. The DAG plan was correct.
The node proof text now records the actual Lean construction and quotient-residue
calculation. The original public BaseChangeConventions import was unrelated to the
statement and needlessly introduced source-library dependencies. Edge cases remain
valid: empty X, nonreduced X, and the one-etale case require no special assumptions.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
