## What changed

Filled twelve theorem proofs in `lean/Sheaf/Paper/PbcAutomorphismTransport.lean`.
The coefficient isomorphism reuses the already proved, projection-normalized
`completedCoefficient_isIso` from `CompletedTowerDirectImage`. The site equivalence
and its ring identification give the module equivalence. The ordinary derived
comparison follows from uniqueness of left-derived pairs, including its equation
on every complex.

The normalized strict-tower/reflector comparison makes the completed comparison
invertible after applying the existing preservation statement. Inverse transport,
derived composition and the identity comparison prove the integral equivalence.
The preservation theorem was moved earlier so that the completed comparison can use it.

Constant scalar compatibility is checked on finite projections and direct-image
sections, proving linearity. The coefficient-change square gives the unique right
comparison with identity section maps. Right Kan extension uniqueness gives the
ambient scalar comparison with its prescribed equation on every complex; the proof
does not assume that scalar counits are invertible on arbitrary complexes.
Fullness restricts this comparison to the integral category. Clearing one scalar
denominator extends the normalized integral comparison to all rational morphisms.

Added proved private helpers and these proof imports:

- `WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor`
- `Mathlib.RingTheory.Localization.BaseChange`
- `WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.LeftDerivedEquivalence`
- `all Sheaf.Paper.CompletedTowerDirectImage`
- `Sheaf.Paper.PbcActualRingedExchange`
- `Sheaf.Paper.PbcActualStrictPullback`

Validation: the complete module compiled cleanly through `lcompile.py` in 39.4 seconds.
A textual audit found no changes to the original public signatures, and the module
contains exactly one remaining `sorry`.

Updated only the existing node's proof, proof dependencies and proof origin. Public
statements, data definition bodies, public imports and the unit route are unchanged.
Local proof settings and the preservation theorem's reordering are documented in
`coord/changes/pbc-automorphism-proof-commands.md`; no downstream adaptation is needed.

## Proved and sorry left

Closed 12 of the original 13 holes. No holes were added or split off.

- `AlgebraicGeometry.Scheme.pbcIsoCoefficientMap_isIso`
- `AlgebraicGeometry.Scheme.pbcIsoModulePullback_isEquivalence`
- `AlgebraicGeometry.Scheme.pbcIsoModulePullback_eq_completed`
- `AlgebraicGeometry.Scheme.pbcIsoOrdinaryDerivedComparison_exists`
- `AlgebraicGeometry.Scheme.pbcIsoCompletedComparison_isIso`
- `AlgebraicGeometry.Scheme.pbcIsoIntegralPullback_isEquivalence`
- `AlgebraicGeometry.Scheme.pbcIsoIntegralPullback_linear`
- `AlgebraicGeometry.Scheme.pbcIsoScalarRightComparison_exists`
- `AlgebraicGeometry.Scheme.pbcIsoAmbientScalarComparison_exists`
- `AlgebraicGeometry.Scheme.pbcIsoIntegralScalarComparison_exists`
- `AlgebraicGeometry.Scheme.pbcIsoRationalization`
- `AlgebraicGeometry.Scheme.pbcIsoRationalScalarComparison_exists`

The original theorem `AlgebraicGeometry.Scheme.pbcIsoAmbientPullback_preserves`
remains `sorry`, with its statement and complete source/proof docstring unchanged.
It belongs to `def-wf-automorphism-completed-transport`. Its remaining argument
transports intrinsic completeness, the common local bounded reduction models, and
the compatible etale-origin witnesses along the scheme isomorphism. The filled
completed comparison and integral equivalence use this existing stated theorem.

## No longer needed

None. No original public import, module, node, unit realization or adopted source
declaration is withdrawn. The original node had no proof dependencies to prune.
The coefficient proof reuses the existing stronger profinite-coefficient result.
The ambient scalar proof uses universal derived pairs directly, so it does not
import the resolving-class scalar-pullback comparison with its K-flat-only equation.

## Where the brief, the DAG or earlier work was wrong

The node had an empty proof and proof-dependency list despite thirteen theorem
holes. Its existing Lean docstrings supplied the plans; the node now records the
implemented routes and the remaining geometric preservation argument.

The original ambient scalar docstring proposed invertibility of the scalar
counits on every complex. The implemented argument needs only their universal
property, and proves the required equation without an additional exactness lemma.
No mathematical statement was disputed, weakened or otherwise changed.

## Second reading by M5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
