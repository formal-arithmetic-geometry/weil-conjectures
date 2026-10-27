## What changed

Proved `AlgebraicGeometry.ProEtale.lisseFlatHomSiteComparison` without changing any
public declaration signature or definition. Added proved private categorical helpers
for basis evaluation, finite coproduct coordinates, naturality, derived duality,
constructibility, and degreewise vanishing. The coefficient quotient is explicitly
shown local using its positive exponent. The node proof now records this route. The seven retained private proof imports supply
the categorical comparison, finite bases over local rings, bounded-complex duality,
derived tensor stability, homology vanishing, and the constructibility equivalence.

The comparison is proved by the existing strong-monoidal exact-pairing theorem.
Coordinates are checked on every finite basis, including rank zero. Restriction uses
the existing canonical `siteHomComparison_restriction` on all and iterated slices.
The second object is only bounded constructible; no finite-Tor hypothesis is added.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.ProEtale.lisseFlatHomSiteComparison`
(node `lem-sf-lisse-flat-hom-site-comparison`). Added zero holes; zero remain in the
item or elsewhere in this delivery. No statements are split off. The final single-file compile passed in 20.9 seconds
after removing two unused helpers and redundant proof imports. Public signatures,
public imports, definitions, and existing docstrings are unchanged.

## No longer needed

Removed these direct private proof imports:

- `Sheaf.AlgebraicGeometry.ComparisonEtaleSliceAbelianPullback`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `WeilConjectures.ConstructibleSheaf.Pullback`
- `Sheaf.Paper.FiniteFreeHomComparison`
- `Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomModel`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`
- `Sheaf.AlgebraicGeometry.ConstructibleTensorRefinementWitness`

The categorical duality and coordinate proofs replace the ringed-complex model,
good-truncation and cone-gluing route. The following planned direct proof dependencies
are unused and removed from `proof_deps`:

- `lem-pe-comparison-etale-slice-abelian-pullback`
- `lem-sf-comparison-pullback-exact`
- `lem-pur-site-restriction-module-adjunction-exact`
- `lem-weil-pbc-ringed-internal-hom-exact-restriction`
- `lem-weil-pbc-ringed-slice-evaluation-transpose`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `prop-constructible-pullback`
- `lem-sf-hom-comparison-finite-free`
- `lem-weil-pbc-ringed-site-bounded-free-rhom-model`
- `lem-sc-finite-free-internal-hom-exact`
- `lem-weil-pbc-comparison-pullback`
- `def-weil-abstract-derived-category`
- `lem-kun-distinguished-cone-zero`
- `lem-pc-sheaf-modules-tensor-closed`
- `lem-fd-constructible-tensor-refinement-witness`

The remaining top-level tool approvals retain their original order. Removed approvals
are the unused entries among the dependencies above. This prunes this item's direct
route; it does not withdraw any module or upstream declaration. Some of these modules
remain transitively needed by the canonical restriction theorem or other consumers.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. The DAG plan was longer than necessary: lisse duality,
bounded-complex duality, derived tensor stability, and the monoidal internal-Hom
comparison already provide the global argument. The local coordinate formula follows
directly from the tensor-Hom adjunction and a colimiting finite basis cofan.

The saved draft contained three unfinished placeholders despite its report claiming
completion. All three are now filled. The short lisse-dual construction uses
`GenericPerfect`, `LisseDual`, and bounded-complex duality; it avoids importing the
much larger `Stability.HomDevissage` module. No other modules were edited.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
