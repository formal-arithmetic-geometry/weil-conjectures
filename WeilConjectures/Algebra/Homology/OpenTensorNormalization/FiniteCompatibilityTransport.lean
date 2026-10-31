/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
import all WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekBaseChangeMate
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.FiniteBaseChangeRestrictionCoherence
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.FiniteTensorRestrictionCoherence

/-!
# Compatibility of finite open normalization comparisons

This is the mate-identification part of the finite specialization.
(blueprint: lem-sf-finite-compatibility-transport)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization

private theorem exactSquare_of_pin
    {A : Type (u + 1)} [CommRing A] {X Y : Scheme.{u}}
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    {k : (Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ S.obj}
    (eR : FiniteRealization A X R i) (eS : FiniteRealization A Y S k)
    (F : FiniteModules A X ⥤ FiniteModules A Y) (G : Mod R ⥤ Mod S)
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (c : F ⋙ eS.equivalence.functor ≅ eR.equivalence.functor ⋙ G)
    (d : F.mapDerivedCategory ⋙ eS.derived ≅ eR.derived ⋙ G.mapDerivedCategory)
    (h : FiniteExactPin eR eS F G c d) :
    d = Functor.mapDerivedCategorySquareIso c := by
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (FiniteModules A X) (.up ℤ))
  intro P
  apply (cancel_mono (G.mapDerivedCategory.map
    (eR.equivalence.functor.mapDerivedCategoryFactors.hom.app P) ≫
      G.mapDerivedCategoryFactors.hom.app
        ((eR.equivalence.functor.mapHomologicalComplex (.up ℤ)).obj P))).1
  rw [h]
  have hc := CategoryTheory.square_fac c P
  apply (cancel_epi (eS.equivalence.functor.mapDerivedCategoryFactors.inv.app
    ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      eS.derived.map (F.mapDerivedCategoryFactors.inv.app P))).1
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  have hi : (Functor.mapHomologicalComplexCompIso (Iso.refl
      (F ⋙ eS.equivalence.functor)) (.up ℤ)).hom.app P ≫
      (NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app P ≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl
        (eR.equivalence.functor ⋙ G)) (.up ℤ)).inv.app P =
      (NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app P := by
    apply HomologicalComplex.Hom.ext
    funext n
    change 𝟙 _ ≫ c.hom.app (P.X n) ≫ 𝟙 _ = c.hom.app (P.X n)
    simp only [Category.id_comp, Category.comp_id]
  rw [hi] at hc
  change _ = _
  simp only [FiniteRealization.derived]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
  exact hc.symm

private theorem exact_square_symm
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    {L : C ⥤ D} {G : D ⥤ F} {H : C ⥤ E} {R : E ⥤ F}
    [L.Additive] [G.Additive] [H.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (e : L ⋙ G ≅ H ⋙ R) :
    (Functor.mapDerivedCategorySquareIso e.symm).hom =
      (Functor.mapDerivedCategorySquareIso e).inv := by
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    Iso.trans_inv, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm, Category.assoc]

private theorem exact_square_unit
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    {G : C ⥤ E} {H : D ⥤ F}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive]
    [G.Additive] [H.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (a : L ⊣ R) (b : L' ⊣ R')
    (s : L ⋙ H ≅ G ⋙ L') (r : R ⋙ G ≅ H ⋙ R')
    (hs : ∀ M, G.map (a.unit.app M) ≫ r.hom.app (L.obj M) ≫
      R'.map (s.hom.app M) = b.unit.app (G.obj M))
    (M : DerivedCategory C) :
    G.mapDerivedCategory.map ((exactLocalizationDerivedAdjunction a).unit.app M) ≫
      (Functor.mapDerivedCategorySquareIso r).hom.app (L.mapDerivedCategory.obj M) ≫
      R'.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso s).hom.app M) =
        (exactLocalizationDerivedAdjunction b).unit.app (G.mapDerivedCategory.obj M) := by
  suffices h :
      Functor.whiskerRight (exactLocalizationDerivedAdjunction a).unit
          G.mapDerivedCategory ≫
        Functor.whiskerLeft L.mapDerivedCategory
          (Functor.mapDerivedCategorySquareIso r).hom ≫
        Functor.whiskerRight (Functor.mapDerivedCategorySquareIso s).hom
          R'.mapDerivedCategory =
      Functor.whiskerLeft G.mapDerivedCategory (exactLocalizationDerivedAdjunction b).unit
      from NatTrans.congr_app h M
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ))
  intro P
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  have hmate : ∀ X, b.unit.app (G.obj X) ≫ R'.map (s.inv.app X) =
      G.map (a.unit.app X) ≫ r.hom.app (L.obj X) := by
    intro X
    rw [← hs X]
    simp only [Category.assoc, ← R'.map_comp, Iso.hom_inv_id_app]
    erw [R'.map_id, Category.comp_id]
  have h := CategoryTheory.mate_unit_Q a b r s.symm hmate P
  rw [exact_square_symm] at h
  apply (cancel_mono (R'.mapDerivedCategory.map
    ((Functor.mapDerivedCategorySquareIso s).inv.app (DerivedCategory.Q.obj P)))).1
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  erw [R'.mapDerivedCategory.map_id, Category.comp_id]
  exact h.symm

private theorem finite_open_unit
    {A : Type (u + 1)} [CommRing A] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    {k : (Functor.const U.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ (restrictRing .ordinary j R).obj}
    (eX : FiniteRealization A X R i) (eU : FiniteRealization A U (restrictRing .ordinary j R) k)
    (o : OpenExtension .ordinary j R)
    (ds : finiteShriek A j ⋙ eX.derived ≅ eU.derived ⋙ openExtensionDerived o)
    (dr : finitePull A j ⋙ eU.derived ≅
      eX.derived ⋙ (restrictionModel (m := .ordinary) j R).functor)
    (p : FiniteOpenPin j R eX eU o ds dr) (M : FiniteD A U) :
    eU.derived.map ((exactLocalizationDerivedAdjunction
        (ProEtale.openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j)).unit.app M) ≫
      dr.hom.app ((finiteShriek A j).obj M) ≫
      (restrict .ordinary j R).mapDerivedCategory.map (ds.hom.app M) =
    (exactDerivedAdjunction o.adjunction).unit.app (eU.derived.obj M) := by
  let : eU.equivalence.functor.Additive := eU.additive
  let : eX.equivalence.functor.Additive := eX.additive
  let : o.ordinary.Additive := o.additive
  let : PreservesFiniteLimits o.ordinary := o.limits
  let : PreservesFiniteColimits o.ordinary := o.colimits
  let : (restrict .ordinary j R).Additive := (restriction_exact .ordinary j R).1
  let : PreservesFiniteLimits (restrict .ordinary j R) :=
    (restriction_exact .ordinary j R).2.1
  let : PreservesFiniteColimits (restrict .ordinary j R) :=
    (restriction_exact .ordinary j R).2.2
  have hs := exactSquare_of_pin eU eX _ _ p.shriek ds p.models.1
  have hr := exactSquare_of_pin eX eU _ _ p.star dr p.models.2
  have h := exact_square_unit
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
    o.adjunction p.shriek p.star p.unit M
  simpa only [← hs, ← hr, FiniteRealization.derived, finiteShriek,
    openExtensionDerived, exactDerivedAdjunction, Adjunction.mapExactDerivedCategory,
    exactLocalizationDerivedAdjunction] using h

private theorem factorsh_hom
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex C ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj K) =
      F.mapDerivedCategoryFactors.hom.app K := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  have h₁ : (DerivedCategory.quotientCompQhIso C).hom.app K = 𝟙 _ := rfl
  have h₂ : (DerivedCategory.quotientCompQhIso D).inv.app
      ((F.mapHomologicalComplex (.up ℤ)).obj K) = 𝟙 _ := rfl
  have h₃ : (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app K = 𝟙 _ := rfl
  simp only [h₁, h₂, h₃, F.mapDerivedCategory.map_id, Category.id_comp]
  erw [DerivedCategory.Qh.map_id, Category.comp_id, Category.comp_id]

private theorem finite_adjunction_exact
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) j =
      exactLocalizationDerivedAdjunction
        (ProEtale.openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j) := by
  let : IsNoetherianRing A := isNoetherian_of_finite A A
  let L := ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j
  let R := ProEtale.upperStar (ModuleCat.{u + 1} A) j
  let a := ProEtale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j
  apply Adjunction.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (FiniteModules A U) (.up ℤ))
  intro K
  apply (cancel_mono (R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
    R.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K))).mp
  have h := a.mapDerivedCategoryAdjunction_unit_app_fac
    ((HomotopyCategory.quotient _ _).obj K)
  erw [factorsh_hom L K,
    factorsh_hom R ((L.mapHomologicalComplex (.up ℤ)).obj K),
    Adjunction.mapHomotopyCategory_unit_app_quotient] at h
  refine h.trans ?_
  change DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) = _
  rw [CategoryTheory.exact_unit_app]
  simp only [Category.assoc]
  change DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) =
    DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
      R.mapDerivedCategoryFactors.inv.app _ ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.inv.app K) ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
      R.mapDerivedCategoryFactors.hom.app _
  simp only [← R.mapDerivedCategory.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [R.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app,
    Category.comp_id]

private theorem hom_transport
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {Lb : E ⥤ F} {Rb : F ⥤ E}
    (a : L ⊣ R) (b : Lb ⊣ Rb) (EU : C ⥤ E) (EX : D ⥤ F)
    (s : L ⋙ EX ≅ EU ⋙ Lb) (r : R ⋙ EU ≅ EX ⋙ Rb)
    (hu : ∀ M, EU.map (a.unit.app M) ≫ r.hom.app (L.obj M) ≫
      Rb.map (s.hom.app M) = b.unit.app (EU.obj M))
    {M : C} {N : D} (f : L.obj M ⟶ N) :
    b.homEquiv _ _ (s.inv.app M ≫ EX.map f) =
      EU.map (a.homEquiv _ _ f) ≫ r.hom.app N := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, ← hu M]
  simp only [Functor.map_comp, Category.assoc, ← Rb.map_comp_assoc,
    Iso.hom_inv_id_app]
  erw [Rb.map_id, Category.id_comp]
  have hn := r.hom.naturality f
  change EU.map (R.map f) ≫ r.hom.app N =
    r.hom.app (L.obj M) ≫ Rb.map (EX.map f) at hn
  rw [← hn]

private theorem beta_transport
    {A B C D Ab Bb Cb Db : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category Ab] [Category Bb] [Category Cb] [Category Db]
    {J : A ⥤ B} {U : B ⥤ A} {J' : C ⥤ D} {U' : D ⥤ C}
    {Jb : Ab ⥤ Bb} {Ub : Bb ⥤ Ab} {Jb' : Cb ⥤ Db} {Ub' : Db ⥤ Cb}
    (adj : J ⊣ U) (adj' : J' ⊣ U') (adjb : Jb ⊣ Ub) (adjb' : Jb' ⊣ Ub')
    (EA : A ⥤ Ab) (EB : B ⥤ Bb) (EC : C ⥤ Cb) (ED : D ⥤ Db)
    (u : U ⋙ EA ≅ EB ⋙ Ub) (u' : U' ⋙ EC ≅ ED ⋙ Ub')
    (j : J ⋙ EB ≅ EA ⋙ Jb) (j' : J' ⋙ ED ≅ EC ⋙ Jb')
    (hu : ∀ X, EA.map (adj.unit.app X) ≫ u.hom.app (J.obj X) ≫
      Ub.map (j.hom.app X) = adjb.unit.app (EA.obj X))
    (hu' : ∀ X, EC.map (adj'.unit.app X) ≫ u'.hom.app (J'.obj X) ≫
      Ub'.map (j'.hom.app X) = adjb'.unit.app (EC.obj X))
    (P : A ⥤ C) (Q : B ⥤ D) (Pb : Ab ⥤ Cb) (Qb : Bb ⥤ Db)
    (p : P ⋙ EC ≅ EA ⋙ Pb) (q : Q ⋙ ED ≅ EB ⋙ Qb)
    (b : U ⋙ P ⟶ Q ⋙ U') (bb : Ub ⋙ Pb ⟶ Qb ⋙ Ub')
    (hb : ∀ Y,
      p.hom.app (U.obj Y) ≫ Pb.map (u.hom.app Y) ≫ bb.app (EB.obj Y) =
        EC.map (b.app Y) ≫ u'.hom.app (Q.obj Y) ≫ Ub'.map (q.hom.app Y))
    (β : J ⋙ Q ≅ P ⋙ J') (βb : Jb ⋙ Qb ≅ Pb ⋙ Jb')
    (hβ : ∀ X, adj'.homEquiv _ _ (β.inv.app X) =
      P.map (adj.unit.app X) ≫ b.app (J.obj X))
    (hβb : ∀ X, adjb'.homEquiv _ _ (βb.inv.app X) =
      Pb.map (adjb.unit.app X) ≫ bb.app (Jb.obj X)) (X : A) :
    ED.map (β.hom.app X) ≫ j'.hom.app (P.obj X) ≫ Jb'.map (p.hom.app X) =
      q.hom.app (J.obj X) ≫ Qb.map (j.hom.app X) ≫ βb.hom.app (EA.obj X) := by
  have ht :
      j'.inv.app (P.obj X) ≫ ED.map (β.inv.app X) ≫ q.hom.app (J.obj X) =
        Jb'.map (p.hom.app X) ≫ βb.inv.app (EA.obj X) ≫ Qb.map (j.inv.app X) := by
    apply (adjb'.homEquiv _ _).injective
    rw [← Category.assoc, adjb'.homEquiv_naturality_right]
    rw [hom_transport adj' adjb' EC ED j' u' hu', hβ, EC.map_comp]
    simp only [Category.assoc]
    simp only [Functor.comp_obj]
    rw [← hb (J.obj X)]
    have hp := p.hom.naturality (adj.unit.app X)
    change EC.map (P.map (adj.unit.app X)) ≫ p.hom.app (U.obj (J.obj X)) =
      p.hom.app X ≫ Pb.map (EA.map (adj.unit.app X)) at hp
    rw [← Category.assoc, ← Category.assoc, hp]
    simp only [Category.assoc]
    have hn := bb.naturality (j.inv.app X)
    change Pb.map (Ub.map (j.inv.app X)) ≫ bb.app (EB.obj (J.obj X)) =
      bb.app (Jb.obj (EA.obj X)) ≫ Ub'.map (Qb.map (j.inv.app X)) at hn
    have hunit : EA.map (adj.unit.app X) ≫ u.hom.app (J.obj X) =
        adjb.unit.app (EA.obj X) ≫ Ub.map (j.inv.app X) := by
      rw [← hu X]
      simp only [Category.assoc, ← Ub.map_comp, Iso.hom_inv_id_app]
      erw [Ub.map_id, Category.comp_id]
    rw [← Pb.map_comp_assoc, hunit, Pb.map_comp]
    simp only [Category.assoc]
    rw [hn]
    rw [adjb'.homEquiv_naturality_left, adjb'.homEquiv_naturality_right]
    simp only [Functor.comp_obj]
    have hh := hβb (EA.obj X)
    dsimp only [Functor.comp_obj] at hh
    rw [hh]
    simp [Category.assoc]
  have heq : ED.map (β.inv.app X) ≫ q.hom.app (J.obj X) ≫ Qb.map (j.hom.app X) =
      j'.hom.app (P.obj X) ≫ Jb'.map (p.hom.app X) ≫ βb.inv.app (EA.obj X) := by
    apply (cancel_epi (j'.inv.app (P.obj X))).1
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    calc
      _ = (j'.inv.app (P.obj X) ≫ ED.map (β.inv.app X) ≫
          q.hom.app (J.obj X)) ≫ Qb.map (j.hom.app X) := by
        simp only [Category.assoc]
      _ = _ := by rw [ht]; simp [← Qb.map_comp, Category.assoc]
  apply (cancel_epi (ED.map (β.inv.app X))).1
  simp only [← Category.assoc, ← ED.map_comp, Iso.inv_hom_id_app,
    ED.map_id, Category.id_comp]
  simpa [Category.assoc] using
    (congrArg (fun f ↦ f ≫ βb.hom.app (EA.obj X)) heq).symm

private theorem gamma_transport
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {Lb : E ⥤ F} {Rb : F ⥤ E}
    (a : L ⊣ R) (b : Lb ⊣ Rb) (EU : C ⥤ E) (EX : D ⥤ F)
    (s : L ⋙ EX ≅ EU ⋙ Lb) (r : R ⋙ EU ≅ EX ⋙ Rb)
    (hu : ∀ M, EU.map (a.unit.app M) ≫ r.hom.app (L.obj M) ≫
      Rb.map (s.hom.app M) = b.unit.app (EU.obj M))
    (P : D ⥤ C) (Pb : F ⥤ E) (p : P ⋙ EU ≅ EX ⋙ Pb)
    (TU : C × C ⥤ C) (TX : D × D ⥤ D)
    (TUb : E × E ⥤ E) (TXb : F × F ⥤ F)
    (ψU : TU ⋙ EU ≅ EU.prod EU ⋙ TUb) (ψX : TX ⋙ EX ≅ EX.prod EX ⋙ TXb)
    (δ : ∀ M N, TU.obj (R.obj M, P.obj N) ⟶ R.obj (TX.obj (M, N)))
    (δb : Rb.prod Pb ⋙ TUb ⟶ TXb ⋙ Rb)
    (hδ : ∀ M N, EU.map (δ M N) ≫ r.hom.app (TX.obj (M, N)) ≫
        Rb.map (ψX.hom.app (M, N)) =
      ψU.hom.app (R.obj M, P.obj N) ≫
        TUb.map (CategoryTheory.Prod.mkHom (r.hom.app M) (p.hom.app N)) ≫
        δb.app (EX.obj M, EX.obj N))
    (π : ∀ K N, L.obj (TU.obj (K, P.obj N)) ≅ TX.obj (L.obj K, N))
    (πb : (𝟭 E).prod Pb ⋙ TUb ⋙ Lb ≅ Lb.prod (𝟭 F) ⋙ TXb)
    (hπ : ∀ K N, a.homEquiv _ _ ((π K N).hom) =
      TU.map (CategoryTheory.Prod.mkHom (a.unit.app K) (𝟙 _)) ≫ δ (L.obj K) N)
    (hπb : ∀ K N, b.homEquiv _ _ (πb.hom.app (K, N)) =
      TUb.map (CategoryTheory.Prod.mkHom (b.unit.app K) (𝟙 _)) ≫ δb.app (Lb.obj K, N))
    (K : C) (N : D) :
    EX.map ((π K N).inv) ≫ s.hom.app (TU.obj (K, P.obj N)) ≫
        Lb.map (ψU.hom.app (K, P.obj N)) ≫
        Lb.map (TUb.map (CategoryTheory.Prod.mkHom (𝟙 _) (p.hom.app N))) =
      ψX.hom.app (L.obj K, N) ≫
        TXb.map (CategoryTheory.Prod.mkHom (s.hom.app K) (𝟙 _)) ≫
        πb.inv.app (EU.obj K, EX.obj N) := by
  have ht : s.inv.app (TU.obj (K, P.obj N)) ≫ EX.map ((π K N).hom) ≫
        ψX.hom.app (L.obj K, N) ≫
        TXb.map (CategoryTheory.Prod.mkHom (s.hom.app K) (𝟙 _)) =
      Lb.map (ψU.hom.app (K, P.obj N)) ≫
        Lb.map (TUb.map (CategoryTheory.Prod.mkHom (𝟙 _) (p.hom.app N))) ≫
        πb.hom.app (EU.obj K, EX.obj N) := by
    apply (b.homEquiv _ _).injective
    rw [← Category.assoc, ← Category.assoc, b.homEquiv_naturality_right,
      b.homEquiv_naturality_right, hom_transport a b EU EX s r hu, hπ K N, EU.map_comp]
    simp only [Category.assoc]
    rw [reassoc_of% (hδ (L.obj K) N)]
    have hn := ψU.hom.naturality (CategoryTheory.Prod.mkHom (a.unit.app K) (𝟙 (P.obj N)))
    change EU.map (TU.map (CategoryTheory.Prod.mkHom (a.unit.app K) (𝟙 _))) ≫
        ψU.hom.app (R.obj (L.obj K), P.obj N) =
      ψU.hom.app (K, P.obj N) ≫
        TUb.map (CategoryTheory.Prod.mkHom (EU.map (a.unit.app K)) (EU.map (𝟙 _))) at hn
    rw [← Category.assoc, hn]
    simp only [Category.assoc, EU.map_id]
    have hd := δb.naturality
      (CategoryTheory.Prod.mkHom (s.hom.app K) (𝟙 (EX.obj N)))
    change TUb.map (CategoryTheory.Prod.mkHom (Rb.map (s.hom.app K)) (Pb.map (𝟙 _))) ≫
        δb.app (Lb.obj (EU.obj K), EX.obj N) =
      δb.app (EX.obj (L.obj K), EX.obj N) ≫
        Rb.map (TXb.map (CategoryTheory.Prod.mkHom (s.hom.app K) (𝟙 _))) at hd
    simp only [Pb.map_id] at hd
    rw [← hd]
    rw [b.homEquiv_naturality_left, b.homEquiv_naturality_left]
    have hh := hπb (EU.obj K) (EX.obj N)
    dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj] at hh ⊢
    rw [hh]
    simp only [← TUb.map_comp_assoc]
    congr 1
    congr 1
    apply congrArg TUb.map
    apply CategoryTheory.Prod.hom_ext
    · simpa using hu K
    · simp
  apply (cancel_epi (EX.map ((π K N).hom))).1
  simp only [← Category.assoc, ← EX.map_comp, Iso.hom_inv_id,
    EX.map_id, Category.id_comp]
  apply (cancel_epi (s.inv.app (TU.obj (K, P.obj N)))).1
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  have hh := congrArg (fun f ↦ f ≫ πb.inv.app (EU.obj K, EX.obj N)) ht
  simpa [Category.assoc] using hh.symm

/-- The pinned finite comparisons transport the published base-change and
projection arrows to the normalized arrows.

Proof: conjugate the inverse of the published finite base-change isomorphism
by the pullback and shriek comparisons. Apply the derived open adjunction to
this arrow. On an exact complex representative, the pull pins' mate equations
and the open pins' unit equations identify its transpose with the pullback of
the open unit followed by the inverse theta comparison. To check the square
used here, apply the underlying-sheaf comparisons: right_sections and the
open section equations identify it with the fixed sectionwise right square
in Operations. This is precisely the right-adjoint comparison whose conjugate
defines ordinaryOpenExtensionBaseChangeIso. The comparison on derived flat
representatives is the same one by the pull and open model equations and
Operations.theta_model. Localization therefore gives the same transpose as
a.beta_inverse. Injectivity of the open adjunction Hom equivalence
identifies the inverse arrows. Cancel the isomorphisms to obtain the forward
route equality finiteBetaLeft = finiteBetaRight.

For projection, conjugate the inverse of the finiteGamma arrow by the tensor,
shriek and open-pull comparisons. The published finite projection map is the
open-adjunction transpose of the tensor of the open unit with the identity.
The ordinary open pin's unit equation identifies the units under realization.
On a flat K-flat pair of complexes, the tensor pins' pure-summand equations
identify both tensors on every bidegree generator with the same pure tensor;
the restriction-tensor pure equation in Operations identifies restriction of
this map. The equality extends from pure tensors to the sheafified tensors
by their universal property and to the signed total complexes by their coproduct
universal property. Naturality makes it an equality of chain maps, with the
same sign on the second differential. The tensor model equations and the open
model equations descend this equality to the derived tensor functors, giving
exactly the transpose in a.gamma_inverse. Injectivity of the adjunction
Hom equivalence identifies the inverse maps; cancellation gives
finiteGammaLeft = finiteGammaRight. These are the two conjuncts of
FiniteCompatibility. Neither argument chooses a beta or gamma comparison.

Source: Stacks 03S6 and 0GL1; the defining conjugate in
ProEtaleDerivedExtensionZeroBaseChange and the canonical projection map in
OpenLowerShriekProj fix the orientations used above.
(blueprint: lem-sf-finite-compatibility-transport) -/
theorem finite_compatibility_of_comparisons (A : Type (u + 1)) [CommRing A]
    [Finite A] {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    {t : SiteSquare (finiteInput A gU j' j g sq)}
    (o : Operations (finiteInput A gU j' j g sq) t) (a : Assertion o)
    (e : FiniteComparisons A o) : FiniteCompatibility A o a e := by
  let : IsOpenImmersion j := sq.isOpenImmersion
  let : IsOpenImmersion j' := sq.isOpenImmersion'
  let : IsNoetherianRing A := isNoetherian_of_finite A A
  let r := Functor.isoWhiskerRight
    (ProEtale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctorIsoMapDerivedCategory.symm
    e.realizeU.derived ≪≫ e.openPull
  have hu (M : FiniteD A U) := finite_open_unit j _ e.realizeX e.realizeU
    o.opens.extension e.shriek r e.open_pin M
  have hu' (M : FiniteD A U') := finite_open_unit j' _ e.realizeX' e.realizeU'
    o.opens.extension' e.shriek' e.openPull' e.open'_pin M
  simp only [← finite_adjunction_exact A j] at hu
  simp only [← finite_adjunction_exact A j'] at hu'
  constructor
  · intro M
    have hβ (K : FiniteD A U) :
        (ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) j').homEquiv _ _
          ((ProEtale.ordinaryOpenExtensionBaseChangeIso A gU j' j g
            (square_isPullback sq)).inv.app K) =
        (finitePull A gU).map
            ((ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} A) j).unit.app K) ≫
          (Functor.mapDerivedCategorySquareIso
            (ProEtale.upperStarCompIso (ModuleCat.{u + 1} A) sq.toCommSq.w)).hom.app
            ((finiteShriek A j).obj K) := by
      have he : (ProEtale.ordinaryOpenExtensionBaseChangeIso A gU j' j g
          (square_isPullback sq)).inv =
          (ProEtale.derivedOpenImmersionLowerShriekBaseChangeIso
            (ModuleCat.{u + 1} A) (square_isPullback sq)).hom := by
        have hc : ((conjugateIsoEquiv
            ((ProEtale.openImmersionLowerShriekUpperStarAdjunction
                (ModuleCat.{u + 1} A) j).comp
              (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g))
            ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) gU).comp
              (ProEtale.openImmersionLowerShriekUpperStarAdjunction
                (ModuleCat.{u + 1} A) j'))).symm
            (@asIso _ _ _ _ (ProEtale.baseChangeMap
                (ModuleCat.{u + 1} A) (square_isPullback sq).toCommSq)
              (ProEtale.isIso_baseChangeMap_of_isPullback
                (ModuleCat.{u + 1} A) (square_isPullback sq)))) =
            ProEtale.openImmersionLowerShriekBaseChangeIso
              (ModuleCat.{u + 1} A) (square_isPullback sq) := by
          apply Iso.ext
          rfl
        simp only [ProEtale.ordinaryOpenExtensionBaseChangeIso,
          ProEtale.derivedOpenImmersionLowerShriekBaseChangeIso,
          Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, Category.assoc]
        rw [← Functor.mapDerivedCategoryNatIso_symm, Iso.symm_symm_eq, hc]
      rw [Adjunction.homEquiv_unit, he]
      exact ProEtale.unit_map_derivedOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} A) (square_isPullback sq) K
    exact beta_transport
      (ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) j)
      (ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) j')
      o.opens.adj o.opens.adj'
      e.realizeU.derived e.realizeX.derived e.realizeU'.derived e.realizeX'.derived
      r e.openPull' e.shriek e.shriek' hu hu'
      (finitePull A gU) (finitePull A g) o.gUPull.derived o.gPull.derived
      e.pullU e.pull
      (Functor.mapDerivedCategorySquareIso
        (ProEtale.upperStarCompIso (ModuleCat.{u + 1} A) sq.toCommSq.w)).hom
      o.theta.inv
      (finite_base_change_restriction_coherence A gU j' j g sq o e)
      (ProEtale.ordinaryOpenExtensionBaseChangeIso A gU j' j g (square_isPullback sq))
      a.beta hβ a.beta_inverse M
  · intro M N
    let δ := Functor.uncurry.map
      (ProEtale.mapDerivedCategoryUpperStarDerivedTensorIso
        (ModuleCat.{u + 1} A) j).hom
    let π := Functor.uncurry.mapIso
      (ProEtale.derivedOpenImmersionLowerShriekProjectionIso
        (ModuleCat.{u + 1} A) j)
    have hπ (K : FiniteD A U) (L : FiniteD A X) :
        (ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j).homEquiv _ _ (π.hom.app (K, L)) =
        (finiteTensor A U).map (CategoryTheory.Prod.mkHom
          ((ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) j).unit.app K) (𝟙 _)) ≫
          δ.app ((finiteShriek A j).obj K, L) := by
      rw [Adjunction.homEquiv_unit]
      simpa [δ, π, finiteTensor, finiteShriek, Functor.uncurry,
        ProEtale.derivedOpenImmersionLowerShriekProjectionIso,
        ProEtale.derivedOpenImmersionLowerShriekProjectionMap,
        Adjunction.projectionMapTranspose] using
        Adjunction.unit_app_comp_map_projectionMap_app_app
          (ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) j)
          (ProEtale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor
          (ProEtale.derivedTensor (ModuleCat.{u + 1} A) U)
          (ProEtale.derivedTensor (ModuleCat.{u + 1} A) X)
          (ProEtale.mapDerivedCategoryUpperStarDerivedTensorIso
            (ModuleCat.{u + 1} A) j).hom K L
    exact gamma_transport
      (ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) j) o.opens.adj
      e.realizeU.derived e.realizeX.derived e.shriek r hu
      (ProEtale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor
      o.opens.jStar e.openPull
      (finiteTensor A U) (finiteTensor A X) o.tensorU.functor o.tensorX.functor
      e.tensorU e.tensorX (fun M N ↦ δ.app (M, N)) o.tensorComparison.comparison.inv
      (finite_tensor_restriction_coherence A gU j' j g sq o e)
      (fun K N ↦ π.app (K, N)) a.gamma.symm hπ a.gamma_inverse M N

end SheafOfModules.OpenTensorNormalization
