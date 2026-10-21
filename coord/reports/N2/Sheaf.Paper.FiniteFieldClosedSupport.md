## What changed

Proved `AlgebraicGeometry.Scheme.finiteFieldClosedSupport_bounded_constructible` in
`Sheaf.Paper.FiniteFieldClosedSupport`, with its statement and public imports unchanged.
The adopted source library already proves the fixed-module version of the closed-support
argument in `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible`.
The delivery proves the necessary bridges instead of repeating that argument:

- Finite homological support is equivalent to vanishing outside an integer interval.
- Finite-ring derived origin and the etale constructibility comparison identify intrinsic
  bounded constructibility with the fixed-module etale-origin predicate.
- The normalized constant direct images agree. Their derived comparison and uniqueness of
  right adjoints identify the two closed exceptional inverse images under realization.
- Apply the source theorem with `ULift A` and annihilator `ℓ`, then transport its conclusion.

All helpers are private and proved. No existing definition, declaration signature, target,
source-library file or consumer is changed. Updated the node proof, proof dependencies and
proof origin to describe this route. The existing fixed-module theorem is a previously
formalized version of this same mathematical result; it adds no new unproved node or statement.
The restricted-functor unit and its route remain unchanged.

Repair of the return at `ef166fe54`: reapplied the retained proof to the current shared
module after the upstream synchronization. Checked that the current theorem signature and
all four public imports are byte-identical to the retained version. The synchronization's
duplicate private closed-immersion imports are removed by the proof-import replacement.
Refreshed the node from the current shared copy, preserving its newer reviewed re-split,
Lean attachment, review records, statement and all other metadata. Only `proof`, `proof_deps`,
`proof_origin` and removal of obsolete top-level `tool_uses` entries differ from that copy.

Validation: the repaired proof compiled cleanly through `lcompile.py` in 4.4 seconds.
The scalar check derives
`(ℓ : k) ≠ 0` from primality and `p ≠ ℓ`, and `(ℓ : ULift A) = 0` from characteristic.
The finite-support bridge covers the empty support using ordered min/max bounds. The proof
also covers empty schemes, the identity closed immersion and zero complexes without any
nonemptiness or separatedness assumption. No field cohomological-dimension bound is used.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.finiteFieldClosedSupport_bounded_constructible`
(node `lem-sfb-finite-field-closed-support`).

Remaining holes in the item: none. Added holes: none. Split off: none.
This is a proof from existing declarations, not a decomposition. The existing imported
comparison/source declarations still have transitive `sorryAx` dependencies; an exploratory
`#print axioms` confirmed that this is not yet an axiom-free proof of the entire target closure.
No such diagnostic commands remain in the delivered module.

## No longer needed

Removed these direct proof imports from the current shared module:

- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion`
- `Sheaf.AlgebraicGeometry.ProEtalePullbackLocallyConstant`
- `Sheaf.AlgebraicGeometry.ProEtaleClosedSupportTriangle`
- `Sheaf.AlgebraicGeometry.ProEtaleModulePullbackComposition`
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Mathlib.AlgebraicGeometry.Morphisms.Immersion`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`

The current shared module contained the closed-immersion import twice; both copies are removed.

Removed these old direct proof dependencies from the current item node:

- `def-weil-finite-type-morphism`
- `lem-exc-proetale-closed-exact`
- `lem-exc-proetale-closed-fully-faithful`
- `lem-exc-proetale-support-triangle`
- `lem-sfb-finite-field-proetale-direct-image`
- `lem-sfb-finite-type-composition-base-change`
- `lem-sfb-intrinsic-finite-derived-pullback`
- `lem-weil-pbc-immersion-base-change-lft`

The fixed-module source theorem already contains the support-triangle, pullback and counit
argument. Those constructions need not be imported or reproved in the intrinsic module.
Their removal here does not withdraw any declaration or assert that their modules have no
other target-reachable users. No upstream declaration is removed, and no globally pruned
module is claimed.

Removed these obsolete top-level `tool_uses` approvals, preserving the order of the rest:

- `lem-exc-proetale-closed-exact`
- `lem-exc-proetale-closed-fully-faithful`
- `lem-exc-proetale-pullback-locally-constant`
- `lem-exc-proetale-support-triangle`
- `lem-sfb-finite-type-composition-base-change`
- `lem-weil-pbc-exact-functor-complex-cohomology`
- `lem-weil-pbc-immersion-base-change-lft`
- `lem-weil-pbc-site-pullback-abelian-exact`
- `prop-weil-pbc-proetale-constant-ring-map`
- `lem-pur-proetale-module-pullback-composition`
- `lem-pur-scheme-constructible-preimage`

## Where the brief, the DAG or earlier work was wrong

The current reviewed five-step plan is mathematically valid. It incorporates the earlier
six-step plan's two pullback steps in `lem-sfb-intrinsic-finite-derived-pullback`.
The return required applying the proof to the current source after the upstream sync;
this packet does so and preserves the newer DAG review metadata. Its observation that the closest source
theorem uses etale-origin constructibility is correct, but the already proved finite-ring
derived-origin theorem now bridges precisely this difference. Thus the existing source proof
can be reused after explicitly comparing constructibility and the ambient right adjoints.
There is no statement dispute, definition repair, forced adaptation or new node.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
