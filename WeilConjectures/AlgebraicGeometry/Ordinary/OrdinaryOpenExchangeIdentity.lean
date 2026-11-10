/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedOrdinaryComparisons
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryOpenModuleIdentity
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Identity normalization for ordinary open exchange

Source: Stacks Project, Tags 03DI, 07A7 and 099N; the identity part of
proof step 7 of `thm-cbc-complete-proetale`.
-/

-- Only imports remain after declaration-level pruning.

private theorem identityCounit
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (F G : C ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (h : F = G) (L : DerivedCategory C ⥤ DerivedCategory C)
    (ε : ∀ P : CochainComplex C ℤ, L.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (hp : ∀ P : CochainComplex C ℤ,
      (F.mapHomologicalComplex (.up ℤ)).obj P =
        (G.mapHomologicalComplex (.up ℤ)).obj P)
    (e : L ≅ G.mapDerivedCategory)
    (he : Functor.ExactDerivedCounitNormalization F G L ε hp e)
    (n : G ≅ 𝟭 C) (P : CochainComplex C ℤ) :
    (e ≪≫ Functor.mapDerivedCategoryNatIso n ≪≫
        Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Q.obj P) =
      ε P ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (eqToIso h ≪≫ n).hom (.up ℤ)).app P) := by
  cases h
  have hn := he P
  simp only [eqToIso_refl, Iso.refl_hom, CategoryTheory.Functor.map_id, Category.comp_id] at hn
  simp only [Iso.trans_hom, NatTrans.comp_app, idFactors]
  rw [Functor.mapDerivedCategoryNatIso_fac, ← Category.assoc, hn]
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp]
