# Sheaf.Paper.SupportedCup

## Reason

Complete the normalized coefficient existence/uniqueness, ordinary comparison, flatness, and derived comparison
proofs. Profiling identified expensive unfolding of localization and monoidal instance data.
The two named references cupHasDerivedCategory and cupMonoidal now have reducible transparency
instead of instance_reducible transparency; their data remain inferInstance. Keep
cupDerivedCoefficientMap irreducible so its localization comparison stays folded during
elaboration. Its formula is unchanged and explicit unfolding remains available. Write
supportedCup's formerly implicit C, L, M and N arguments explicitly, using the same objects.
These changes preserve the coefficient arrow and cup-product formula. Explicit categorical
associativity rewrites in the comparison proofs avoid checking reassociation by unfolding
concrete sheaf morphisms. The complete module compiled with artifacts in 34.7 seconds.

Use transparency-respecting elaboration globally, with scoped exceptions for the
constant-sheaf and lower-star unit identifications. No target statement changes.

## Old

The module used set_option backward.isDefEq.respectTransparency false globally.
The relevant definitions were:

```lean
@[instance_reducible]
noncomputable def cupHasDerivedCategory (P : WeilConjectures.PurityFiniteSetting.{u})
    (X : Scheme.{u}) : HasDerivedCategory.{u + 1}
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) :=
  inferInstance

@[instance_reducible]
noncomputable def cupMonoidal (P : WeilConjectures.PurityFiniteSetting.{u}) (X : Scheme.{u}) :
    MonoidalCategory (CupDerivedCategory P X) := inferInstance

noncomputable def cupDerivedCoefficientMap {C : Type c} [Category.{v} C] [Abelian C]
    [hD : HasDerivedCategory.{w} C]
    [HasColimitsOfSize.{0, 0} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C]
    [hDM : MonoidalCategory (DerivedCategory C)] [(DerivedCategory.Q (C := C)).LaxMonoidal]
    {L M N : C} (μ : L ⊗ M ⟶ N) :
    (DerivedCategory.singleFunctor C 0).obj L ⊗
        (DerivedCategory.singleFunctor C 0).obj M ⟶
      (DerivedCategory.singleFunctor C 0).obj N :=
  cupSingleTensorMap L M ≫ (DerivedCategory.singleFunctor C 0).map μ

noncomputable def supportedCup (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z W X : Scheme.{u}} [X.Over (Spec (CommRingCat.of P.field.k))]
    (i : Z ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (F G : CupPlus P X)
    (a b : ℤ) (α : cupSupportedHom P i F.obj a) (β : cupSupportedHom P j G.obj b) :
    cupSupportedHom P (cupIntersection i j)
      (cupTensorObject P X F.obj G.obj) (a + b) :=
  cupComposite (hM := cupMonoidal P X) (F := F.obj) (G := G.obj)
    (cupDerivedCoefficientMap (hD := cupHasDerivedCategory P X)
      (hDM := cupMonoidal P X) (cupCoefficientMap P i j))
    (cupDerivedCoefficientMap_isIso P i j) a b α β
```

The proofs of cupCoefficientMap_existsUnique, cupCoefficientMap_isIso, cupCoefficient_flat,
and cupDerivedCoefficientMap_isIso were by sorry.

## New

The module uses set_option backward.isDefEq.respectTransparency true globally, with scoped
exceptions on the restriction construction and selected private helper proofs.
The definitions now read:

```lean
@[reducible]
noncomputable def cupHasDerivedCategory (P : WeilConjectures.PurityFiniteSetting.{u})
    (X : Scheme.{u}) : HasDerivedCategory.{u + 1}
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) :=
  inferInstance

@[reducible]
noncomputable def cupMonoidal (P : WeilConjectures.PurityFiniteSetting.{u}) (X : Scheme.{u}) :
    MonoidalCategory (CupDerivedCategory P X) := inferInstance

@[irreducible]
noncomputable def cupDerivedCoefficientMap {C : Type c} [Category.{v} C] [Abelian C]
    [hD : HasDerivedCategory.{w} C]
    [HasColimitsOfSize.{0, 0} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C]
    [hDM : MonoidalCategory (DerivedCategory C)] [(DerivedCategory.Q (C := C)).LaxMonoidal]
    {L M N : C} (μ : L ⊗ M ⟶ N) :
    (DerivedCategory.singleFunctor C 0).obj L ⊗
        (DerivedCategory.singleFunctor C 0).obj M ⟶
      (DerivedCategory.singleFunctor C 0).obj N :=
  cupSingleTensorMap L M ≫ (DerivedCategory.singleFunctor C 0).map μ

noncomputable def supportedCup (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z W X : Scheme.{u}} [X.Over (Spec (CommRingCat.of P.field.k))]
    (i : Z ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (F G : CupPlus P X)
    (a b : ℤ) (α : cupSupportedHom P i F.obj a) (β : cupSupportedHom P j G.obj b) :
    cupSupportedHom P (cupIntersection i j)
      (cupTensorObject P X F.obj G.obj) (a + b) :=
  cupComposite (C := CupDerivedCategory P X) (hM := cupMonoidal P X)
    (L := (cupSingle P X).obj
      ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z)))
    (M := (cupSingle P X).obj
      ((lowerStar (ModuleCat.{u + 1} P.Coefficient) j).obj (P.constant W)))
    (N := (cupSingle P X).obj
      ((lowerStar (ModuleCat.{u + 1} P.Coefficient) (cupIntersection i j)).obj
        (P.constant (pullback i j))))
    (F := F.obj) (G := G.obj)
    (cupDerivedCoefficientMap (hD := cupHasDerivedCategory P X)
      (hDM := cupMonoidal P X) (cupCoefficientMap P i j))
    (cupDerivedCoefficientMap_isIso P i j) a b α β
```

All public signatures and coefficient data are unchanged. The four theorems have complete
proofs using proved private helpers and proof-only imports. The derived proof transports the
monoidal and Q-lax-monoidal structures together as a dependent pair, preserving their equality
to the canonical structures without expanding their large data. No downstream statement
changes meaning. No sorry remains in this module. The ordinary comparison is proved from the
existing stated etale closedConstantTensor theorem by canonical monoidal transport and the
proved uniqueness characterization; that imported theorem is unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.SupportedCup | E7 | four proofs completed; elaboration repaired |
| Sheaf.Paper.PurityFrameClass | unclaimed | consumer; source unchanged |
| Sheaf.Paper.SupportedCupFunctoriality | unclaimed | comparison consumer; source unchanged |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | comparison consumer; source unchanged |

The users were found with tools/downstream.py --uses for cupHasDerivedCategory, cupMonoidal,
cupDerivedCoefficientMap and supportedCup. PurityFrameClass compiled unchanged against the
revised definitions in 52.5 seconds. SupportedCupFunctoriality and SupportedExteriorClasses
exceeded the 60-second compile limit both against the published module and against the revised
module. These baseline failures do not demonstrate a forced adaptation; neither consumer is
changed in this packet. The broader downstream closure has 23 modules. The maintainer's global
build remains the final check of the consumers.

## Status

landed 20261020T211701-L-3488314 2026-10-20 (merge of deliver/E7/Sheaf.Paper.SupportedCup)
