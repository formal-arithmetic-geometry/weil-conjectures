# AlgebraicGeometry.Proj.gradedQuotientTwistComparison

## Reason

The explicit fraction proof does not need the relative-Proj API, the global-sections
Proj construction, or the independent-universe cochain tensor monoidal instances.
Replace their unused public imports with the focused graded-map module that provides
`GradedRingHom.irrelevant_le_map_of_surjective` for the statement. All declarations retain their signatures and the
section-product definition is unchanged. The sole direct importer imports the item
privately and already imports relative Proj separately; no adaptation is needed.
No target statement or definition used by a target is changed.

## Old

```lean
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.UnitToTwist
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.TensorObj
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
```

## New

```lean
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.UnitToTwist
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.TensorObj
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.StandardProjCoherentSectionFiniteness | unclaimed | Direct private importer. Its own public imports provide its statement dependencies; it imports relative Proj itself. No adaptation. |
| Sheaf.AlgebraicGeometry.ProjectivePolarizationSectionAlgebra | unclaimed | Transitive importer through a private proof import. No exposed dependency on the removed imports. No adaptation. |

## Status

landed 20261023T123758-L-1250532 2026-10-23 (merge of deliver/J9/Sheaf.AlgebraicGeometry.GradedProjQuotientTwistComparison)
