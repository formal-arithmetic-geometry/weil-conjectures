## What changed

Filled the two remaining theorem bodies in
`WeilConjectures.ConstructibleSheaf.Noetherian`.

`AlgebraicGeometry.Scheme.IsConstructibleSheaf.exists_stratification_isIrreducible`
uses the proved `exists_irreducible_refinement_topological` and the existing
module-valued refinement-preservation theorem. Added one private proof import,
`WeilConjectures.AlgebraicGeometry.IrreducibleStratificationRefinement`.

`AlgebraicGeometry.Etale.exists_finset_mono_pi_lift` follows the finite irreducible
lisse partition argument in blueprint node
`lem-weil-pbc-constructible-noetherian-finite-selection` (Stacks 09Z6).
It selects indices from the finite set of nonzero generic stalk elements,
uses product projections to prove generic injectivity, applies the existing
module-valued generic-stalk criterion on every stratum, and concludes by
geometric-stalk cancellation and extensionality. No stalk/product comparison
is assumed. The empty scheme and zero stalks allow the finite choice set to
be empty.

Updated the proof fields of the two corresponding blueprint nodes to record
these native module-valued realizations as well as their retained abelian
counterparts. No signatures, public imports, definitions, or unit routes changed.

## Proved and sorry left

Closed two existing holes:

- `AlgebraicGeometry.Scheme.IsConstructibleSheaf.exists_stratification_isIrreducible`
  (`lem-weil-pbc-irreducible-lisse-strata`).
- `AlgebraicGeometry.Etale.exists_finset_mono_pi_lift`
  (`lem-weil-pbc-constructible-noetherian-finite-selection`).

No holes added, no lemmas split off, and no `sorry` remains in the item module.
Validation: the complete item module compiled through `lcompile.py` in 19.1 seconds
with no errors or warnings. Final compile and axiom probes run in `deliver3.py`.

## No longer needed

No existing imports, declarations, nodes, or modules are removed. The abelian
finite-stalk-test and finite-selection modules remain available for their own
consumers; the native module-valued proof does not import them or introduce
additional module-to-set or module-to-abelian comparison dependencies.

## Where the brief, the DAG or earlier work was wrong

The node Lean attachments name the existing abelian counterparts rather than
the module-valued declarations assigned here. Those counterparts are preserved;
the node proof descriptions now also explain the native module proof.
No false statement or required interface repair was found. The compile server
once returned no answer after 210 seconds; a later retry succeeded. During proof
development, writing the comparison components as `(e.app F).hom` and
`(e.app F).inv` avoided an unsuitable universe path in monomorphism instance search.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
