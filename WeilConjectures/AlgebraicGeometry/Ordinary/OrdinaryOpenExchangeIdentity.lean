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

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t
open CategoryTheory CategoryTheory.Limits

private theorem idFactors
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Q.obj P) =
      (𝟭 C).mapDerivedCategoryFactors.hom.app P := by
  have h := Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj C
    ((HomotopyCategory.quotient C (.up ℤ)).obj P)
  rw [Functor.mapDerivedCategoryFactorsh_hom_app] at h
  have h₁ : ((𝟭 C).mapHomotopyCategoryFactors (.up ℤ)).inv.app P = 𝟙 _ := rfl
  have h₂ : (DerivedCategory.quotientCompQhIso C).hom.app P = 𝟙 _ := rfl
  have h₃ : (DerivedCategory.quotientCompQhIso C).inv.app
      (((𝟭 C).mapHomologicalComplex (.up ℤ)).obj P) = 𝟙 _ := rfl
  rw [h₁, h₂, h₃] at h
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id, Category.comp_id] at h
  exact h

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

private theorem exchangeNormalization
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ C) (G : D ⥤ D) (J : C ⥤ D)
    [F.Additive] [G.Additive] [J.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    (LF : DerivedCategory C ⥤ DerivedCategory C)
    (LG : DerivedCategory D ⥤ DerivedCategory D)
    (ε : ∀ P : CochainComplex C ℤ, LF.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (δ : ∀ P : CochainComplex D ℤ, LG.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj P))
    (e : LF ≅ 𝟭 _) (f : LG ≅ 𝟭 _) (n : F ≅ 𝟭 _) (m : G ≅ 𝟭 _)
    (he : ∀ P, e.hom.app (DerivedCategory.Q.obj P) = ε P ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex n.hom (.up ℤ)).app P))
    (hf : ∀ P, f.hom.app (DerivedCategory.Q.obj P) = δ P ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex m.hom (.up ℤ)).app P))
    (b : F ⋙ J ⟶ J ⋙ G)
    (hb : ∀ M, b.app M ≫ m.hom.app (J.obj M) = J.map (n.hom.app M))
    (Good : CochainComplex C ℤ → Prop) :
    Functor.DerivedExchangeCounitNormalization F G J J LF LG ε δ b Good
      (Functor.whiskerRight e.hom J.mapDerivedCategory ≫
        Functor.whiskerLeft J.mapDerivedCategory f.inv) := by
  intro P _
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  have hc : (NatTrans.mapHomologicalComplex b (.up ℤ)).app P ≫
      (NatTrans.mapHomologicalComplex m.hom (.up ℤ)).app
        ((J.mapHomologicalComplex (.up ℤ)).obj P) =
      (J.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex n.hom (.up ℤ)).app P) := by
    ext q
    exact hb (P.X q)
  have : IsIso ((NatTrans.mapHomologicalComplex m.hom (.up ℤ)).app
      ((J.mapHomologicalComplex (.up ℤ)).obj P)) := by
    change IsIso ((NatIso.mapHomologicalComplex m (.up ℤ)).hom.app _)
    infer_instance
  apply (cancel_mono (DerivedCategory.Q.map
    ((NatTrans.mapHomologicalComplex m.hom (.up ℤ)).app
      ((J.mapHomologicalComplex (.up ℤ)).obj P)))).1
  simp only [Category.assoc]
  rw [← hf]
  have hn := f.inv.naturality (J.mapDerivedCategoryFactors.hom.app P)
  dsimp only [Functor.id_map] at hn
  rw [← reassoc_of% hn]
  simp only [Iso.inv_hom_id_app]
  rw [← Functor.map_comp, hc,
    ← J.mapDerivedCategoryFactors_hom_naturality, ← Functor.map_comp_assoc, ← he]
  change J.mapDerivedCategory.map (e.hom.app (DerivedCategory.Q.obj P)) ≫
      J.mapDerivedCategoryFactors.hom.app P ≫ 𝟙 _ =
    J.mapDerivedCategory.map (e.hom.app (DerivedCategory.Q.obj P)) ≫
      J.mapDerivedCategoryFactors.hom.app P
  rw [Category.comp_id]

private theorem transportIdentity
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ C} {G G' : D ⥤ D} (J : C ⥤ D)
    (e : F ≅ F') (f : G ≅ G') (n : F' ≅ 𝟭 C) (m : G' ≅ 𝟭 D)
    (b : F ⋙ J ⟶ J ⋙ G) [IsIso b]
    (hb : b = Functor.whiskerRight (e ≪≫ n).hom J ≫
      Functor.whiskerLeft J (f ≪≫ m).inv) (K : C) :
    (Functor.whiskerLeft J f.inv ≫ inv b ≫ Functor.whiskerRight e.hom J).app K ≫
        J.map (n.hom.app K) = m.hom.app (J.obj K) := by
  let eU := e ≪≫ n
  let eT := f ≪≫ m
  have hi : (inv b).app K ≫ J.map (eU.hom.app K) = eT.hom.app (J.obj K) := by
    apply (cancel_epi (b.app K)).1
    rw [← Category.assoc, ← NatTrans.comp_app, IsIso.hom_inv_id]
    simp only [NatTrans.id_app, Category.id_comp]
    rw [hb]
    change J.map (eU.hom.app K) =
      (J.map (eU.hom.app K) ≫ eT.inv.app (J.obj K)) ≫ eT.hom.app (J.obj K)
    rw [Category.assoc, Iso.inv_hom_id_app]
    exact (Category.comp_id _).symm
  apply (cancel_epi (f.hom.app (J.obj K))).1
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  simpa only [eU, eT, Iso.trans_hom, NatTrans.comp_app, Functor.map_comp,
    Category.assoc] using hi

namespace AlgebraicGeometry.Scheme


private theorem oldPullIdentity
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (T : Scheme.{t}) (P : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) :
    (cbcDatumOrdinaryTransport d (𝟙 T) ≪≫ d.pullId T).hom.app
        (DerivedCategory.Q.obj P) =
      completedOrdinaryPullbackComplexCounit (𝟙 T) d P ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (cbcModulePullId d T).hom (.up ℤ)).app P) := by
  exact identityCounit _ _ (cbcDatumModulePull_eq d (𝟙 T))
    (completedOrdinaryPullback (𝟙 T) d) (completedOrdinaryPullbackComplexCounit (𝟙 T) d)
    (cbcDatumModulePullComplex_eq d (𝟙 T)) (cbcDatumOrdinaryTransport d (𝟙 T))
    (cbcDatumOrdinaryTransport_exists d (𝟙 T)).exists.choose_spec
    ((proEtaleRingModuleAdjunction (𝟙 T) (d.completedRing T) (d.completedRing T)
      (d.integralRingIso (𝟙 T))).leftAdjointIdIso (d.modulePushId T)) P

attribute [local irreducible] cbcDatumOrdinaryTransport AdicCoefficientDatum.pullId
  cbcModulePullId cbcOpenShriek cbcUnderivedInverseExchange cbcDerivedInverseExchange

private theorem derivedInverseIdentity
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j]
    (sq : OpenImmersionSquare (𝟙 U) j j (𝟙 T)) :
    cbcDerivedInverseExchange d sq =
      Functor.whiskerRight
          (cbcDatumOrdinaryTransport d (𝟙 U) ≪≫ d.pullId U).hom
          (cbcDerivedOpenShriek d j inferInstance) ≫
        Functor.whiskerLeft (cbcDerivedOpenShriek d j inferInstance)
          (cbcDatumOrdinaryTransport d (𝟙 T) ≪≫ d.pullId T).inv := by
  apply cbcDerivedInverseExchange_eq d sq
  exact exchangeNormalization (completedModulePullback (𝟙 U) d)
    (completedModulePullback (𝟙 T) d) (cbcOpenShriek d j inferInstance)
    (completedOrdinaryPullback (𝟙 U) d) (completedOrdinaryPullback (𝟙 T) d)
    (completedOrdinaryPullbackComplexCounit (𝟙 U) d)
    (completedOrdinaryPullbackComplexCounit (𝟙 T) d)
    (cbcDatumOrdinaryTransport d (𝟙 U) ≪≫ d.pullId U)
    (cbcDatumOrdinaryTransport d (𝟙 T) ≪≫ d.pullId T)
    (cbcModulePullId d U) (cbcModulePullId d T)
    (oldPullIdentity d U) (oldPullIdentity d T)
    (cbcUnderivedInverseExchange d sq) (cbcUnderivedInverseExchange_identity d j sq)
    (CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion U d))

attribute [local irreducible] cbcOrdinaryExchange
  cbcDatumOrdinaryExchange

/-- The ordinary open mate for identity base change respects the ordinary pullback units.
Source: Stacks 03DI and 07A7; blueprint identity-base-change step
(blueprint: lem-cbc-ordinary-open-exchange-identity).
Proof: the sectionwise right exchange for the identity square is restriction along
its canonical pullback comparison. Under the direct-image identity comparisons it
is identity on every section. Transpose across the two normalized open adjunctions:
the triangle equations identify the inverse exchange with the identity pullback
comparison on extension by zero. Apply the termwise exact derived functors and the
universal pullback counits on K-flat representatives. Their normalization identifies
the transported inverse with the inverse ordinary pullback identity on the ambient
scheme followed by extension of the identity comparison on the open. Invert this
equation and cancel the adjacent identity comparisons. Every derived object has a
K-flat representative, so the resulting equation holds for arbitrary K. The section
calculation includes an empty open and the zero object, without a boundedness or
quasi-compactness assumption. -/
theorem cbcDatumOrdinaryExchange_identity
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j]
    (sq : OpenImmersionSquare (𝟙 U) j j (𝟙 T)) (K : d.derived U) :
    (cbcDatumOrdinaryExchange d sq).app K ≫
        (cbcDerivedOpenShriek d j inferInstance).map ((d.pullId U).hom.app K) =
      (d.pullId T).hom.app ((cbcDerivedOpenShriek d j inferInstance).obj K) := by
  unfold cbcDatumOrdinaryExchange cbcOrdinaryExchange
  exact transportIdentity (cbcDerivedOpenShriek d j inferInstance)
    (cbcDatumOrdinaryTransport d (𝟙 U)) (cbcDatumOrdinaryTransport d (𝟙 T))
    (d.pullId U) (d.pullId T) (cbcDerivedInverseExchange d sq)
    (derivedInverseIdentity d j sq) K

end AlgebraicGeometry.Scheme
