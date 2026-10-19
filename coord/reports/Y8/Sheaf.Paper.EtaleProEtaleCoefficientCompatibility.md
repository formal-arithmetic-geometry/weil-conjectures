## What changed

Proved three of the six existing theorems in
`Sheaf.Paper.EtaleProEtaleCoefficientCompatibility` without changing any public signature or definition.
The naturality proof transposes the open inverse under the open adjunction and then composes with
naturality of the proper scalar mate. The counit proof uses the existing main site/coefficient square,
naturality on the bounded-below subcategory, and cancellation of the specified comparisons.
The refinement proof identifies the existing normalized etale compactScalarMap with our map by
`compactScalarOpen_normalization`, uses `etaleCompactScalarCoherence` for its etale square, and
transports that square through the two actual main site/coefficient squares.
All added helper theorems are private and proved. Added the proof-only import
`Sheaf.Paper.EtaleCompactScalarCoherence`. Updated the node proof and proof dependencies accordingly.

## Proved and sorry left

Closed (three original holes):
- `AlgebraicGeometry.ProEtale.CoefficientCompatibility.etaleProEtaleCoefficientCompatibility_refinement`.
- `AlgebraicGeometry.ProEtale.CoefficientCompatibility.etaleProEtaleCoefficientCompatibility_counit`.
- `AlgebraicGeometry.ProEtale.CoefficientCompatibility.etaleProEtaleCoefficientCompatibility_naturality`.

Remaining (three original holes, all in node `lem-sp-et-proet-coefficient-compatibility`):
- `AlgebraicGeometry.ProEtale.CoefficientCompatibility.etaleProEtaleCoefficientCompatibility`:
  the boundedness, invertibility and normalized intrinsic/fixed-module site square (Steps 1--4).
- `AlgebraicGeometry.ProEtale.CoefficientCompatibility.etaleProEtaleCoefficientCompatibility_composition`:
  proper/open composition and its pro-etale transport (Steps 5, 6, 8 and 9).
- `AlgebraicGeometry.ProEtale.CoefficientCompatibility.etaleProEtaleCoefficientCompatibility_sum`:
  the normalized acyclic-flat sheet calculation (Step 10).

Added holes: none. Split-offs: none. This is three holes closed, not a decomposition.
The refinement and counit proofs intentionally depend on the still-stated main theorem;
their combination arguments are complete Lean proofs.

## No longer needed

The following direct proof imports were redundant: each remains transitively available from the
existing public imports or the scalar-coherence proof import, as checked by the import graph and
compilation:
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`.
- `Sheaf.AlgebraicGeometry.CompactifiableOverField`.
- `Sheaf.AlgebraicGeometry.DerivedCategories`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`.
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`.
- `Mathlib.Algebra.DirectSum.Module`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`.
- `Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower`.
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`.
- `Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`.
- `Sheaf.AlgebraicGeometry.EtaleFlatConstructibleModel`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`.
- `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`.
- `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`.
- `WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic`.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`.
- `Sheaf.Paper.ProperOpenCoefficientMate`.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
- `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`.
- `Sheaf.CategoryTheory.RingedSliceExtensionTensor`.
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`.
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`.

No DAG node or module is claimed globally pruned: the three remaining theorem plans retain their
stated dependencies. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was needed. The existing normalized scalar-coherence module
already supplies the etale refinement argument and its open-map normalization, so repeating its
proper/open calculation would duplicate work. Its node `lem-pur-etale-compact-scalar-coherence`
(unit `sk-prop-an`) is used as a generic normalized scalar/refinement tool in this unit; it does not
replace the smooth-purity or six-operation unit route. The maintainer may record this cross-unit
tool use; this delivery does not add or edit the maintainer's tool_uses approvals.

Validation: the entire edited module compiled through lcompile.py after all three proofs;
final import cleanup and the required delivery preflight are checked again before pushing.

## Second reading by Y8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
