## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.rationalRestrictionGlue` from the
existing local restriction, constant-model locality and compactification preservation
declarations. The public statement and both restriction-functor definitions are unchanged.
All added helpers are private and proved, and all new imports are private proof imports.

The finite-cover proof detects vanishing through the underlying abelian sheaves and
chooses common cohomological bounds from the finite ranges of local bounds. It uses
`finiteConstantStratified_zariski_locality` to assemble the cohomology stratifications
on affine opens and then globally, including the empty cover. The local restriction
theorem and exceptional-adjoint existence theorem supply local constructibility of the specified right adjoint. Pullback of
stratifications and finite constant models transports it to the open ranges of the charts.

The compactification preservation theorem and Dctf=Dbc give preservation by the specified
left adjoint. Mathlib's fully faithful restriction gives the required adjunction with
exactly the original Hom equivalence. The node records the actual proof dependencies.
The unit's affine-local, finite-cover and restricted-adjunction steps are retained.
The affine-local assembly avoids the expensive definitional expansion of the top-open
isomorphism; explicitly typed pullback comparison objects keep its API small.
No definition repair or consumer adaptation is needed.

Validation: the complete module compiles cleanly through `lcompile.py` in 19.5 seconds,
with no errors or warnings. The theorem signature and both public definition bodies
were compared against the current source and are unchanged; no line exceeds 100 characters.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.ProEtale.CondensedRing.rationalRestrictionGlue`
(node `det-thm-restriction-glue`). Zero holes added, zero split off, and zero holes
remain in the item module. Existing imported theorem obligations remain their own items.
This is a proof from those declarations, not a claim that the target closure is axiom-free.

## No longer needed

Removed private imports `Sheaf.Paper.CoefficientHeart`,
`Sheaf.Paper.CartesianCoefficients`,
`Sheaf.Paper.CoefficientHeartCommonStratification`,
`WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`,
`Mathlib.AlgebraicGeometry.Morphisms.Immersion`,
`Sheaf.Compactification.BoundaryRefinement`,
`Sheaf.Paper.CondensedConstantConstructibility`,
`WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`, and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
Necessary definitions remain available through retained public imports and proof dependencies.

Direct proof dependencies `sk-lem-coefficient-heart`,
`sk-prop-sfb-cartesian-coefficients`,
`lem-weil-pbc-proper-fp-permanence`,
`lem-weil-pbc-reduced-induced-closed-subscheme`, and
`det-lem-coefficient-heart-common-stratification` are replaced by the existing
constant-model Zariski locality, exact cohomology comparison, finite quasi-compact
abelian-sheaf detection and the Dctf=Dbc theorem.
The four obsolete tool approvals for the coefficient heart, common stratification,
reduced closed subscheme and cartesian coefficients are removed from this node.
These nodes remain reachable elsewhere in the item’s import closure: comparing the
current source imports with this packet removes zero whole modules and adds only
`Sheaf.Paper.FiniteConstantStratifiedZariskiLocality`, which is already proved.
No module or declaration is withdrawn.
`sk-def-sfb-dc-setting` remains a statement dependency, with its compactification
construction used through `def-sfb-compactification-over-field`.

## Where the brief, the DAG or earlier work was wrong

The existing plan is mathematically usable, but the proved constant-model Zariski
locality API now avoids repeating its lisse-heart refinement argument.
The local restriction declaration requires explicit projection and closed-immersion
adjunctions before its constructibility clause applies; the existing existence theorem
supplies them. The rework table lists an earlier quarantine; the live source is present
and its public declarations, Lean attachment and mathematical setting are preserved.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
