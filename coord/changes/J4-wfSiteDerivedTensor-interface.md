# SheafOfModules.wfSiteDerivedTensor

## Reason

The original nested existential choice repeatedly elaborates the total-tensor instances
and its homotopy-localization data. Retain the same normalized derived tensor as the
first component of an existence theorem, together with its full comparison data.
`wfSiteTotalTensor` gives the total complex a named functor interface. Its comparison
with the existing signed total tensor is the identity isomorphism.

No coefficient object, localization, K-flat condition, or comparison normalization
changes. The first-argument computation and unique normalized comparison are proved.
Targets using this definition require their semantic review to be reopened, as required
by the project contract; their statements and mathematical meaning are preserved.
Zero objects, the zero coefficient ring, and empty generating tuples add no hypothesis.
No source-library declaration is changed.

## Old

```lean
def wfSiteDerivedTensor {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasSheafify J AddCommGrpCat.{max u v}]
    (R : Sheaf J CommRingCat.{max u v})
    [HasDerivedCategory.{w} (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))] :
    DerivedCategory (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ×
    DerivedCategory (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ⥤
    DerivedCategory (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) :=
  (wf_site_derived_tensor_descent.{u, v, w, 0, 0} J R).choose_spec.2.2.1.choose_spec.2.choose
```

## New

```lean
def wfSiteDerivedTensor {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasSheafify J AddCommGrpCat.{max u v}]
    (R : Sheaf J CommRingCat.{max u v})
    [HasDerivedCategory.{w} (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))] :
    DerivedCategory (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ×
    DerivedCategory (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ⥤
    DerivedCategory (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) :=
  (wfSiteDerivedTensor_exists J R).choose
```

The public `wfSiteDerivedTensor_exists` reorders the original descent witnesses.
`wfSiteTotalTensor` names the existing uncurried total complex; `wfSiteTotalTensor_iso`
proves its comparison with that expression. All additional helpers are proved.

## Users

`tools/downstream.py Sheaf.Paper.WeilTensorProduct --uses
SheafOfModules.wfSiteDerivedTensor` lists the following direct declaration users.
Their tensor statements keep the same mathematical meaning. None uses the old raw
choice projections. No forced adaptation is required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.DerivedTensorTruncationWindow | unclaimed | Same normalized tensor and first-variable comparison. |
| Sheaf.Algebra.Homology.RingedSiteTorFlatModel | unclaimed | Same normalized tensor and first-variable comparison. |
| Sheaf.Algebra.Homology.SitePerfectLowerModel | unclaimed | Same normalized tensor and first-variable comparison. |
| Sheaf.Algebra.Homology.SitePerfectOpcyclesRetract | unclaimed | Same normalized tensor and first-variable comparison. |
| Sheaf.Algebra.Homology.SitePerfectTorWindow | unclaimed | Same normalized tensor and first-variable comparison. |
| Sheaf.CategoryTheory.SiteTorIntervalRestriction | unclaimed | Same normalized tensor and first-variable comparison. |
| Sheaf.Paper.OrientedNearbyCycles | unclaimed | Same normalized tensor and first-variable comparison. |
| Sheaf.Paper.WeilTensorProduct | J4 | Same normalized tensor and first-variable comparison. |

## Status

landed 20261020T221221-L-4159364 2026-10-20 (merge of deliver/J4/Sheaf.Paper.WeilTensorProduct)
