# AlgebraicGeometry.ProEtale.QuotientSectionTensor.TensorNormalized

## Reason

The assigned rework restores the quarantined module. The global build failed
while synthesizing `DerivedCategory.Q.LaxMonoidal` in `TensorNormalized`, at
20,000 typeclass heartbeats. Its large internal-module structures are already
available as named caches in `IntegralResidueDerivedMonoidal`. Select these
locally, as the existing section-derived normalization module does. In
`TensorNormalized`, bind the two existing `Mod.laxMonoidalQ` instances explicitly
rather than searching for them at each tensorator. No data, statement, public
import, or global attribute is changed.

## Old

```lean
def TensorNormalized (T : Scheme.{u})
    (b : Functor.uncurry.obj (CondensedRing.derivedTensor Λ T) ⋙
        D a T ≅
      ((D a T).prod (D a T)) ⋙
        Functor.uncurry.obj (CondensedRing.derivedTensor Λ' T)) : Prop :=
  ∀ P Q : CochainComplex (Modules Λ T) ℤ,
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q →
    (∀ i : ℤ, ObjectProperty.flat (P.X i)) →
    (∀ i : ℤ, ObjectProperty.flat (Q.X i)) →
      b.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          (compute a T P ⊗ₘ compute a T Q) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Q
            (((extension a T).mapHomologicalComplex (.up ℤ)).obj P)
            (((extension a T).mapHomologicalComplex (.up ℤ)).obj Q) =
        (D a T).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
          compute a T (P ⊗ Q) ≫
          DerivedCategory.Q.map (totalScalar a T P Q)
```


The archived file has no private import of `IntegralResidueDerivedMonoidal`, no
local registration of its projection caches, and this options block:

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
```

## New

```lean
def TensorNormalized (T : Scheme.{u})
    (b : Functor.uncurry.obj (CondensedRing.derivedTensor Λ T) ⋙
        D a T ≅
      ((D a T).prod (D a T)) ⋙
        Functor.uncurry.obj (CondensedRing.derivedTensor Λ' T)) : Prop :=
  letI : (DerivedCategory.Q (C := Modules Λ T)).LaxMonoidal := Mod.laxMonoidalQ
  letI : (DerivedCategory.Q (C := Modules Λ' T)).LaxMonoidal := Mod.laxMonoidalQ
  ∀ P Q : CochainComplex (Modules Λ T) ℤ,
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q →
    (∀ i : ℤ, ObjectProperty.flat (P.X i)) →
    (∀ i : ℤ, ObjectProperty.flat (Q.X i)) →
      b.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          (compute a T P ⊗ₘ compute a T Q) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Q
            (((extension a T).mapHomologicalComplex (.up ℤ)).obj P)
            (((extension a T).mapHomologicalComplex (.up ℤ)).obj Q) =
        (D a T).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
          compute a T (P ⊗ Q) ≫
          DerivedCategory.Q.map (totalScalar a T P Q)
```


Add the private import:

```lean
import Sheaf.Paper.IntegralResidueDerivedMonoidal
```

Locally select existing canonical instances:

```lean
attribute [local instance] AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory
```

The original elaboration options, theorem statement, and theorem proof hole
stay verbatim. The named caches
and the explicit localization instances are definitions of the existing
instances, not new monoidal structures. `TensorNormalized` changes only by
binding these existing instances locally before its unchanged formula.

## Users

`tools/downstream.py Sheaf.Paper.QuotientSectionTensorNormalization
--allow-missing --uses TensorNormalized ComparisonSpec` lists zero current
Lean consumers because this module is quarantined. Searching both `lean/` and
`quarantine/` finds the preserved direct consumer below. It remains needed and
is not withdrawn or adapted in this delivery.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.QuotientPullbackTensorCoherence | unclaimed (no current claim record) | Quarantined direct consumer; compiled unchanged against the repair in 59.6 seconds, no warnings; temporary source copy removed. |

Validation: final unprofiled single-file compile passed in 31.0 seconds with
no warnings. The preserved direct consumer compiled unchanged in 59.6 seconds.
No heartbeat or time limit was raised; no transparency option was relaxed.

## Status

landed 20261026T130249-L-3444708 2026-10-26 (merge of deliver/A3/Sheaf.Paper.QuotientSectionTensorNormalization)
