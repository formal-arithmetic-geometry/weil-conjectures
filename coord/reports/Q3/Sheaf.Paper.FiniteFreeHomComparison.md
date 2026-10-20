## What changed

Proved `AlgebraicGeometry.ProEtale.isIso_finiteFreeHomComparison` with its exact original
signature. Finite free terms are dualizable, and the existing bounded-complex duality
theorem makes the first derived object dualizable. The proved generic monoidal
internal-Hom comparison theorem then applies to every second argument. This is the
current blueprint's dual-complex argument through already proved library results.

Added private proved finite-coproduct and dualizable-object comparison helpers. Replaced
unused proof-plan imports by the dualizability, constant-sheaf monoidality, exact-derived
monoidality, and generic internal-Hom-comparison APIs. The evaluation definition also publicly
imports `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic` for its
canonical comparison and evaluation equation.

Optimized `Sheaf.AlgebraicGeometry.EvaluationHomSiteComparison`: cache the canonical derived
strong monoidal structure as `siteComparisonDerivedMonoidal`, construct the tensor
comparison directly from its prescribed oplax tensorator, and prove
`siteComparisonTensorIso_hom_app` exposing its canonical oplax tensorator. The
new theorem `siteComparisonDerivedMonoidal_δ` proves the transported tensor formula,
which expands to the original four-factor construction. The strong structure is selected
from the proved `siteComparisonDerivedMonoidal_exists`, whose statement prescribes every
tensor component used by the comparison. Its inverse tensorator is uniquely determined.
The integral-residue module is now imported only for that existence proof, keeping its
unrelated instances out of consumer elaboration. `siteComparisonEvaluationHom` keeps its original signature and uses the canonical
`Functor.LaxMonoidal.ihomComparison` for that structure. The proved equation
`siteComparisonEvaluationHom_eq_curry` verifies the original evaluation specification:
curry the inverse tensor comparison followed by pulled-back evaluation.
The definition change records are `coord/changes/Q3-siteComparisonTensorIso.md` and
`coord/changes/Q3-siteComparisonEvaluationHom.md`.
The consumer audit includes `Sheaf.Paper.BoundaryQTransport`,
`Sheaf.Paper.ConstructibleHomComparison`, `Sheaf.Paper.FiniteFreeCoefficientExtension`
(held by T5), `Sheaf.SixFunctors.FiniteDualitySiteComparison`, and
`Sheaf.SixFunctors.FiniteMappingAdjunction`, in addition to the item. These restored
sources use the maps in statements and composite definitions; no proof unfolds the
changed bodies. Their interfaces and mathematical comparison maps are preserved.
No other holder is adapted.
Updated both corresponding DAG records to the implemented proof and construction.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.isIso_finiteFreeHomComparison`
(node `lem-sf-hom-comparison-finite-free`).
Added 0 holes; split off 0 statements. Both delivered Lean modules contain zero `sorry`.
Both edited modules compiled together through `lcompile.py --all`.
The unchanged consumers `FiniteDualitySiteComparison`, `BoundaryQTransport`, and
`ConstructibleHomComparison` also compiled against this packet.
`FiniteMappingAdjunction` compiled against it in 27.2 seconds. The unchanged
`FiniteFreeCoefficientExtension` exceeded 60 seconds both against the packet and
against the published library in the final consumer check (an earlier published-library
run passed in 41.9 seconds). A diagnostic copy with
`backward.isDefEq.respectTransparency true` compiled in 38.0 seconds; it is not delivered,
since the original also times out without this packet and is held by T5. No original
consumer declaration, proof or signature has been edited.
`#print axioms` for the proved theorem and its evaluation specification reports only
`propext`, `Classical.choice`, and `Quot.sound`.
The coefficient-finiteness instance is unchanged and proved. The main argument is
first proved for a coefficient category with the stated monoidal and Grothendieck
structures, then specialized to the specified quotient-module category. Local irreducibility annotations on the coefficient
constructions prevent unnecessary expansion of the DVR witnesses; they alter no data.

## No longer needed

Removed direct imports from the item (some remain transitively available as statement
infrastructure; this does not request withdrawing their declarations):

- `WeilConjectures.AlgebraicGeometry.DerivedCategories`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`
- `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`
- `Sheaf.Paper.ComparisonPullbackExact`
- `WeilConjectures.SixFunctors.Etale.Derived.Hom`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom`
- `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`
- `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf`
- `WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex`
- `WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Mathlib.CategoryTheory.Adjunction.Additive`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous`
- `WeilConjectures.SixFunctors.ProEtale.Comparison.Flat`
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal`
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory`
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`
- `Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomModel`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Free`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`
- `WeilConjectures.Algebra.Homology.HomComplex`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`

The old proof dependency nodes below are unnecessary to this proof route. Their
statement-level citations are preserved, and their other consumers are not altered:

- `lem-sf-comparison-pullback-exact`
- `def-pur-sheaf-hom`
- `lem-pc-sheaf-modules-tensor-closed`
- `lem-weil-pbc-ringed-topoi-module-pullback-tensor`
- `def-pur-hom-complex`
- `def-pc-tensor-complex-sheaves`
- `lem-weil-pbc-ringed-site-bounded-free-rhom-model`
- `def-pur-derived-internal-hom`
- `def-weil-size-convention`

The underived ringed-site internal Hom, generic ringed-site tensor comparison,
Hom-complex construction, and bounded-free RHom-model modules are bypassed by the
already proved bounded dualizability theorem and the monoidal comparison theorem.
No explicit Hom-complex model or new sign calculation is needed. The exactness and
flat-preservation instances are supplied by the adopted comparison-site implementation,
so the separately stated `Sheaf.Paper.ComparisonPullbackExact` theorem is not used.
No module is withdrawn; pruning here means removed dependencies of this item.
Removed the item's obsolete `tool_uses` approvals for
`lem-sf-comparison-pullback-exact`,
`lem-weil-pbc-ringed-site-bounded-free-rhom-model`,
`lem-weil-pbc-ringed-topoi-module-pullback-tensor`, and
`lem-pc-sheaf-modules-tensor-closed`.

## Where the brief, the DAG or earlier work was wrong

The old expanded Hom-complex plan was longer than necessary given the proved
`DerivedCategory.isDualizable_Q_obj` and
`Functor.Monoidal.isIso_ihomComparison_app_of_exactPairing`. The current blueprint's
finite-dual route is retained. Bounds and constructibility on N are not used by this
stronger generic proof; no theorem hypothesis is removed.

Lean was eagerly unfolding the constructed comparison while elaborating the specialized
statement, as well as when identifying the original four-factor tensor comparison with the
transported monoidal tensorator. The named monoidal structures and comparison definitions are now irreducible, with
proved component and evaluation equations. This avoids repeatedly unfolding that
construction while preserving explicit access through the API. Its component formula exposes the canonical transported tensorator; expanding
`Functor.Monoidal.transport_δ` gives the old four factors. The change records request
independent review of this representation repair. Initial preflight found five missing
consumer entries in those records; all five are now listed, including their uses and
the current holder of `FiniteFreeCoefficientExtension`.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
