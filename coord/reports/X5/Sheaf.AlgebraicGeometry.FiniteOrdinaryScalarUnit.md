## What changed

Proved `AlgebraicGeometry.Etale.finite_ordinary_scalar_unit`, preserving its
statement and public imports. Added private proved helpers constructing the
sheafification comparison, checking its sections and its stalk restrictions,
identifying its stalk with the finite product comparison, and proving the
scalar-unit equation. No definition or public interface changes.

The proof uses Mathlib's actual `Sheaf.composeAndSheafify` and `Sheaf.adjunction`,
the published finite stalk formula, and geometric-stalk conservativity. It ends
by composing an isomorphism on representing objects with the scalar adjunction.
The node's proof and proof dependencies now describe this implementation.

Searches: Lean Finder returned module-sheaf pushforwards and related ordinary
module lemmas, but no finite scalar-unit theorem; Loogle query
`"extendScalars", "Sheaf"` returned no hits; Mathlib grep
`lowerStar.*extendScalars|extendScalars.*lowerStar|PreservesColimits.*lowerStar`
returned no hits. Source searches found no shorter result. Sources read were
Stacks `etale-cohomology.tex`, Tag 03QP,
`proposition-finite-higher-direct-image-zero`, and `sites-modules.tex`, Tag 03EL,
`lemma-tensor-product-pullback`.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.Etale.finite_ordinary_scalar_unit`
(node `lem-asd-finite-ordinary-scalar-unit`). Added zero holes. No `sorry` remains
in the delivered Lean module; every private helper is proved. This is a proof,
not a decomposition.

The finite-product argument includes the empty fibre. The scalar adjunction
and additivity require neither flatness nor nonzero coefficient rings. No
hypotheses were added, and the given ordinary Hom bijections are used to prove
the actual transpose invertible.

Validation: the final remote single-file compile passed cleanly in 13.0 seconds
(exit code 0, no warnings). Source checks confirmed the unchanged public theorem
signature and public imports, zero holes, no forbidden declarations, lines of
at most 100 characters, and matching DAG proof dependencies. The delivery tool
runs the remaining preflight and axiom-probe checks.

## No longer needed

The declared proof dependency `lem-pod-etale-stalk-tensor-scalar`, module
`Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar`, is unnecessary for this proof.
The required comparison and its normalization follow directly from Mathlib's
`Point.presheafFiberCompIso`, invertibility on stalks of `toSheafify`
(the inverse underlying `Point.presheafToSheafCompSheafFiberIso`), and their
coprojection equations. This avoids importing the broader tensor/coherence API.

The declared proof dependency `def-sf-etale-sheaf-scalar-extension`, module
`WeilConjectures.SixFunctors.ProEtale.ScalarExtension`, is also unnecessary:
its two relevant definitions are the existing Mathlib functor
`Sheaf.composeAndSheafify` and adjunction `Sheaf.adjunction`, used directly via
private abbreviations. The import-direction check shows that importing that
published source module would close an import cycle through this item.

Neither dependency was imported in the original item, so no existing import
was removed. These nodes and modules are pruned only from this item's proof
dependencies; other consumers may still require them. No module is withdrawn.
The finite stalk formula, conservativity, and the unit route are retained.

## Where the brief, the DAG or earlier work was wrong

The recorded ordinary scalar-extension dependency cannot be imported here:
`tools/import_direction.py may` reports that
`WeilConjectures.SixFunctors.ProEtale.ScalarExtension` already reaches this item.
Using Mathlib's underlying construction and adjunction resolves the cycle
without adapting or changing the source library. The remaining planned
mathematics is valid and is now implemented completely. There are no new
nodes, changed signatures, or forced consumer adaptations.

## Second reading by X5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
