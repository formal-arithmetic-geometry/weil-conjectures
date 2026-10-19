## What changed

Proved `FieldTheory.algebraic_separable_extension_is_filtered_colimit_smooth` in
`Sheaf.FieldTheory.AlgebraicSeparableSmooth`, without changing its signature or visibility.
The indexing category is `Finset L`. Its object at `s` is `Algebra.adjoin K (s : Set L)`;
inclusions define the arrows, and union gives upper bounds. Singleton stages cover `L`.
For an arbitrary cocone, `Subalgebra.iSupLift` constructs the induced algebra map.
Naturality through the union stage supplies compatibility even when an inclusion of
subalgebras does not come from an inclusion of their chosen generating subsets.
The lift equations and singleton stages prove the colimit universal property.
Algebraicity makes every stage a field and finite-dimensional; separability descends
along the inclusion. The existing finite-separable-etale theorem and Mathlib's smoothness
instance give the four required properties.

Updated the existing node's proof, proof dependencies and proof origin to match.
The blueprint unit has no realized statement or proof steps that this route bypasses.
The route retains the source's filtered union of finite separable subextensions.
All new imports are proof-only; the existing public imports are unchanged.

Validation: the final packet is checked by `deliver3.py`, including compilation and
its declaration axiom probe. The resumed single-file remote compile passed (42.8 seconds).
Earlier single-file and `#print axioms` checks on this construction passed with only `propext`, `Classical.choice`, and `Quot.sound`.
Private helpers name the diagram, cocone, induced algebra map and colimit proof;
proved helper lemmas give monotonicity, coverage and the lift equation. The proof
works with independent universes for `K` and `L`, without finite-dimensionality of
`L`, and includes the empty finite subset (the base field) and `L = K`.

Searches: Lean Finder returned intermediate-field supremum and algebraicity facts,
without an exact categorical presentation. Loogle found the finite-type algebraic
field finiteness lemma, and the remote grep found no exact subalgebra-colimit hit.
Local source search found the ring-level finite-subset colimit in
`WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits`; that construction
assumes equal universes for base and extension, so the proof instead uses Mathlib's
universe-polymorphic `Subalgebra.iSupLift` directly in `CommAlgCat`.

## Proved and sorry left

Closed 1 of 1 original holes:
`FieldTheory.algebraic_separable_extension_is_filtered_colimit_smooth`
(node `lem-kun-algebraic-separable-smooth`).
Added 0 holes; split off 0 statements. No `sorry` remains in the delivery.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`.
Its node `lem-weil-pbc-etale-smooth-zero-dimensional-fibres` is no longer a proof
dependency of this item: Mathlib already supplies smoothness for etale algebras,
so the scheme-level theorem, fibre dimension, and its extra imports are unnecessary
for this affine argument. This does not claim that the module is unused elsewhere.
All other declared node dependencies remain. No new dependency modules or nodes
are needed. The unrelated ring-level colimit and CommAlgCat colimit infrastructure
modules found in the source search are not imported.

## Where the brief, the DAG or earlier work was wrong

The statement is correct. The planned scheme-level etale-to-smooth bridge was
unnecessary for the algebra-level conclusion. No definition, statement, target,
or consumer needed repair. No new nodes. The conservative scope-command check
requires `coord/changes/M8-algebraic-separable-smooth-proof-scope.md`, which records
the added helper variables and the unchanged interface for all thirteen consumers.

The launcher restarted this same item after provider HTTP 429 errors. The original
attempt was `1792395263`; the intermediate resumed attempt was `1792421622`; the current attempt is
`1792425599`. The sandbox's
reference clock was reset between attempts by the launcher. No budget file was
edited by the worker, and no new holes are proposed. The retained proof and
metadata were reconciled before the final delivery.

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
