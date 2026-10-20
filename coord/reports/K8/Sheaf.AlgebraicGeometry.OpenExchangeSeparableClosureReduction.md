## What changed

Proved `AlgebraicGeometry.Etale.isIso_openProductExchange_of_separableClosure` without
changing either public declaration or any public import. The proof implements the
node's five-step field-extension, exchange-pasting, and conservativity argument.

Private, fully proved helpers transport elementwise torsion through stalk isomorphisms,
compute the cohomology of a sheaf in degree zero, transfer field-extension exchange to
other Cartesian models, and compare the two paths around the scalar-extension cube.
The product and open-pullback comparison morphisms are actual pullback lifts. Their
Cartesian properties follow from pasting and cancellation of Cartesian squares.
No arbitrary objects are selected from existence statements.

Finite type supplies local Noetherianity and quasi-separatedness; quasi-compactness of
`j` follows by cancellation against `X.hom`. Both properties pass to its pullback `h`.
The existing field-extension exchange theorem supplies both comparison isomorphisms.
The existing unbounded/bounded-below comparison transfers the given hypothesis, and
separable-closure conservativity descends the resulting isomorphism. The coefficient
argument uses a separate annihilator for each stalk element, with no uniform bound.

Final server compilation after import cleanup: 27.3 seconds, exit code 0, no warnings.
All Lean lines have at most 100 characters. No public signatures, definitions, or
source-library modules were changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.isIso_openProductExchange_of_separableClosure`
(blueprint node `lem-kun-0f1h-sep-reduction`).

Added 0 holes; split off 0 statements. There are no remaining `sorry`s in the item
module or in any other file of this delivery. The proof uses the already stated
separable-closure conservativity and unbounded-exchange comparison results; their
existing holes are outside this delivery.

## No longer needed

Removed these unused direct proof imports:

- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`
- `Sheaf.AlgebraicGeometry.GeometricStalkAsPullback`
- `Sheaf.AlgebraicGeometry.DerivedInverseImageComposition`
- `Sheaf.Paper.ExchangeIdentityPasting`

The first four are redundant module-coefficient infrastructure. The three wrapper
modules are unnecessary direct imports: the proof uses the source library's
`upperStarCompSheafFiberIso`, `upperStarCompDerivedPlus`, and
`derivedBaseChangeMapPlus_paste_horiz` APIs for exactly the stalk, composition, and
pasting steps of the existing plan. All mathematical steps and the unit route are
preserved. No DAG node or module is withdrawn; no claim is made that a module still
used transitively elsewhere is globally pruned.

## Where the brief, the DAG or earlier work was wrong

No statement error or missing dependency was found. The generic field-extension
and pasting declarations suffice. The only additional work is fully proved glue
between the chosen fibre-product models and between bounded-below and unbounded
functors. The theorem's open-immersion and finite-type assumptions remain unchanged.

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
