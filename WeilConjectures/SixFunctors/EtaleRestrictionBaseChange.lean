/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportCoefficientChange
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeExchange
public import WeilConjectures.CategoryTheory.DerivedExactSquareSupplement
import WeilConjectures.SixFunctors.EtaleRestrictionDerivedMate
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarRestrictScalars
import all WeilConjectures.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChangeSupplement

/-! # Scalar restriction and the open base-change mate

Source: Stacks Project, Tags 0F7J and 0GL6.
(blueprint: lem-sf-etale-restriction-open-base-change).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale


private theorem scalar_comp_id
    {C : Type*} [Category C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = f ≫ g ≫ 𝟙 Z := by simp

private theorem scalar_pushforward_comp
    {A₁ A₂ A₃ B₁ B₂ B₃ : Type*}
    [Category A₁] [Category A₂] [Category A₃]
    [Category B₁] [Category B₂] [Category B₃]
    {L₁ : A₂ ⥤ A₁} {R₁ : A₁ ⥤ A₂} {L₂ : A₃ ⥤ A₂} {R₂ : A₂ ⥤ A₃}
    {L : A₃ ⥤ A₁} {R : A₁ ⥤ A₃}
    {M₁ : B₂ ⥤ B₁} {S₁ : B₁ ⥤ B₂} {M₂ : B₃ ⥤ B₂} {S₂ : B₂ ⥤ B₃}
    {M : B₃ ⥤ B₁} {S : B₁ ⥤ B₃}
    {r₁ : B₁ ⥤ A₁} {r₂ : B₂ ⥤ A₂} {r₃ : B₃ ⥤ A₃}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a : L ⊣ R)
    (b₁ : M₁ ⊣ S₁) (b₂ : M₂ ⊣ S₂) (b : M ⊣ S)
    (τ₁ : r₂ ⋙ L₁ ≅ M₁ ⋙ r₁) (σ₁ : r₁ ⋙ R₁ ≅ S₁ ⋙ r₂)
    (τ₂ : r₃ ⋙ L₂ ≅ M₂ ⋙ r₂) (σ₂ : r₂ ⋙ R₂ ≅ S₂ ⋙ r₃)
    (τ : r₃ ⋙ L ≅ M ⋙ r₁) (σ : r₁ ⋙ R ≅ S ⋙ r₃)
    (h₁ : (mateEquiv b₁ a₁ (TwoSquare.mk _ _ _ _ τ₁.hom)).natTrans = σ₁.inv)
    (h₂ : (mateEquiv b₂ a₂ (TwoSquare.mk _ _ _ _ τ₂.hom)).natTrans = σ₂.inv)
    (h : (mateEquiv b a (TwoSquare.mk _ _ _ _ τ.hom)).natTrans = σ.inv)
    (eL : L ≅ L₂ ⋙ L₁) (eM : M ≅ M₂ ⋙ M₁)
    (he : AlgebraicGeometry.Etale.CoeffCompatible τ (pasteTwoSquaresIso τ₂ τ₁) eL.hom eM.hom) :
    AlgebraicGeometry.Etale.CoeffCompatible (pasteTwoSquaresIso σ₁ σ₂) σ
      (conjugateIsoEquiv a (a₂.comp a₁) eL.symm).inv
      (conjugateIsoEquiv b (b₂.comp b₁) eM.symm).inv := by
  intro K
  simpa only [pasteTwoSquaresIso_hom_app, conjugateIsoEquiv_apply_inv,
    Iso.symm_inv, Category.assoc] using
    Adjunction.conjugateEquiv_comp_restrict a₁ a₂ a b₁ b₂ b τ₁ σ₁ τ₂ σ₂ τ σ
      h₁ h₂ h eL.hom eM.hom
      (fun N ↦ by simpa only [pasteTwoSquaresIso_hom_app, Category.assoc] using he N) K

private theorem scalar_rotate_square
    {C D E F C' D' E' F' : Type*}
    [Category C] [Category D] [Category E] [Category F]
    [Category C'] [Category D'] [Category E'] [Category F']
    {r : D ⥤ C} {r' : D' ⥤ C'} {p : F ⥤ E} {p' : F' ⥤ E'}
    {g : C ⥤ E} {g' : C' ⥤ E'} {h : D ⥤ F} {h' : D' ⥤ F'}
    {s : C ⥤ C'} {t : D ⥤ D'} {v : E ⥤ E'} {w : F ⥤ F'}
    (ra : t ⋙ r' ≅ r ⋙ s) (rc : w ⋙ p' ≅ p ⋙ v)
    (lg : s ⋙ g' ≅ g ⋙ v) (lh : t ⋙ h' ≅ h ⋙ w)
    (θA : r' ⋙ g' ≅ h' ⋙ p') (θB : r ⋙ g ≅ h ⋙ p)
    (he : CoeffCompatible (pasteTwoSquaresIso ra lg) (pasteTwoSquaresIso lh rc)
      θA.hom θB.hom) (M : D) :
    g'.map (ra.inv.app M) ≫ θA.hom.app (t.obj M) ≫ p'.map (lh.hom.app M) =
      lg.hom.app (r.obj M) ≫ v.map (θB.hom.app M) ≫ rc.inv.app (h.obj M) := by
  have hh := he M
  simp only [pasteTwoSquaresIso_hom_app, Category.assoc] at hh
  apply (cancel_epi (g'.map (ra.hom.app M))).1
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% hh]
  simp only [Iso.hom_inv_id_app]
  exact scalar_comp_id (θA.hom.app (t.obj M)) (p'.map (lh.hom.app M))

private theorem scalar_cube_of_mates
    {C D E F C' D' E' F' : Type*}
    [Category C] [Category D] [Category E] [Category F]
    [Category C'] [Category D'] [Category E'] [Category F']
    {a : C ⥤ D} {ar : D ⥤ C} {b : C' ⥤ D'} {br : D' ⥤ C'}
    {c : E ⥤ F} {cr : F ⥤ E} {d : E' ⥤ F'} {dr : F' ⥤ E'}
    (aa : a ⊣ ar) (ab : b ⊣ br) (ac : c ⊣ cr) (ad : d ⊣ dr)
    (s : C ⥤ C') (t : D ⥤ D') (v : E ⥤ E') (w : F ⥤ F')
    (g : C ⥤ E) (h : D ⥤ F) (g' : C' ⥤ E') (h' : D' ⥤ F')
    (la : s ⋙ b ⟶ a ⋙ t) (lc : v ⋙ d ⟶ c ⋙ w)
    (lg : s ⋙ g' ⟶ g ⋙ v) (lh : t ⋙ h' ⟶ h ⋙ w)
    (ta : g ⋙ c ⟶ a ⋙ h) (tb : g' ⋙ d ⟶ b ⋙ h')
    (cube : ∀ M : D,
      g'.map ((mateEquiv aa ab (TwoSquare.mk _ _ _ _ la)).natTrans.app M) ≫
          (mateEquiv ab ad (TwoSquare.mk _ _ _ _ tb)).natTrans.app (t.obj M) ≫ dr.map (lh.app M) =
        lg.app (ar.obj M) ≫ v.map ((mateEquiv aa ac (TwoSquare.mk _ _ _ _ ta)).natTrans.app M) ≫
          (mateEquiv ac ad (TwoSquare.mk _ _ _ _ lc)).natTrans.app (h.obj M)) (N : C) :
    tb.app (s.obj N) ≫ h'.map (la.app N) ≫ lh.app (a.obj N) =
      d.map (lg.app N) ≫ lc.app (g.obj N) ≫ w.map (ta.app N) := by
  apply (ad.homEquiv _ _).injective
  have e := congrArg (fun z ↦ g'.map (s.map (aa.unit.app N)) ≫ z) (cube (a.obj N))
  rw [← g'.map_comp_assoc, unit_mateEquiv, g'.map_comp] at e
  have nb := (mateEquiv ab ad (TwoSquare.mk _ _ _ _ tb)).natTrans.naturality (la.app N)
  have ng := lg.naturality (aa.unit.app N)
  have nc := (mateEquiv ac ad (TwoSquare.mk _ _ _ _ lc)).natTrans.naturality (ta.app N)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at nb ng nc e
  rw [Category.assoc, reassoc_of% nb,
    reassoc_of% (unit_mateEquiv ab ad (TwoSquare.mk _ _ _ _ tb) (s.obj N))] at e
  rw [reassoc_of% ng, ← v.map_comp_assoc, unit_mateEquiv, v.map_comp,
    Category.assoc] at e
  dsimp only [TwoSquare.mk, TwoSquare.natTrans, Functor.id_obj] at e
  rw [nc, reassoc_of% (unit_mateEquiv ac ad (TwoSquare.mk _ _ _ _ lc) (g.obj N))] at e
  rw [← ad.unit_naturality_assoc] at e
  simpa only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc] using e

private theorem scalar_baseChange_cube
    {C D E F C' D' E' F' : Type*}
    [Category C] [Category D] [Category E] [Category F]
    [Category C'] [Category D'] [Category E'] [Category F']
    {a : C ⥤ D} {ar : D ⥤ C} {b : C' ⥤ D'} {br : D' ⥤ C'}
    {c : E ⥤ F} {cr : F ⥤ E} {d : E' ⥤ F'} {dr : F' ⥤ E'}
    (aa : a ⊣ ar) (ab : b ⊣ br) (ac : c ⊣ cr) (ad : d ⊣ dr)
    (s : C ⥤ C') (t : D ⥤ D') (v : E ⥤ E') (w : F ⥤ F')
    (g : C ⥤ E) (h : D ⥤ F) (g' : C' ⥤ E') (h' : D' ⥤ F')
    (qa : s ⋙ b ≅ a ⋙ t) (qc : v ⋙ d ≅ c ⋙ w)
    (ra : t ⋙ br ≅ ar ⋙ s) (rc : w ⋙ dr ≅ cr ⋙ v)
    (lg : s ⋙ g' ≅ g ⋙ v) (lh : t ⋙ h' ≅ h ⋙ w)
    (ha : mateEquiv aa ab (TwoSquare.mk _ _ _ _ qa.hom) =
      TwoSquare.mk _ _ _ _ ra.inv)
    (hc : mateEquiv ac ad (TwoSquare.mk _ _ _ _ qc.hom) =
      TwoSquare.mk _ _ _ _ rc.inv)
    (θA : br ⋙ g' ≅ h' ⋙ dr) (θB : ar ⋙ g ≅ h ⋙ cr)
    (he : CoeffCompatible (pasteTwoSquaresIso ra lg) (pasteTwoSquaresIso lh rc)
      θA.hom θB.hom) :
    CoeffCompatible (pasteTwoSquaresIso lg qc) (pasteTwoSquaresIso qa lh)
      ((mateEquiv ab ad).symm (TwoSquare.mk _ _ _ _ θA.hom)).natTrans
      ((mateEquiv aa ac).symm (TwoSquare.mk _ _ _ _ θB.hom)).natTrans := by
  intro N
  simp only [pasteTwoSquaresIso_hom_app, Category.assoc]
  symm
  apply scalar_cube_of_mates aa ab ac ad s t v w g h g' h'
    qa.hom qc.hom lg.hom lh.hom
    ((mateEquiv aa ac).symm (TwoSquare.mk _ _ _ _ θB.hom)).natTrans
    ((mateEquiv ab ad).symm (TwoSquare.mk _ _ _ _ θA.hom)).natTrans ?_ N
  intro M
  rw [ha, hc]
  simpa only [TwoSquare.mk, TwoSquare.natTrans, Equiv.apply_symm_apply] using
    scalar_rotate_square ra rc lg lh θA θB he M

private theorem exact_square_plus_hom
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory F]
    (U : C ⥤ D) (G : D ⥤ F) (L : C ⥤ E) (V : E ⥤ F)
    [U.Additive] [G.Additive] [L.Additive] [V.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits U]
    [CategoryTheory.Limits.PreservesFiniteColimits U]
    [CategoryTheory.Limits.PreservesFiniteLimits G]
    [CategoryTheory.Limits.PreservesFiniteColimits G]
    [CategoryTheory.Limits.PreservesFiniteLimits L]
    [CategoryTheory.Limits.PreservesFiniteColimits L]
    [CategoryTheory.Limits.PreservesFiniteLimits V]
    [CategoryTheory.Limits.PreservesFiniteColimits V]
    (e : U ⋙ G ≅ L ⋙ V) (K : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map
        ((Functor.mapDerivedCategoryPlusSquareIso U G L V e).hom.app K) =
      (Functor.mapDerivedCategorySquareIso e).hom.app K.obj := by
  have hcomp : DerivedCategory.Plus.ι.mapIso
      ((Functor.mapDerivedCategoryPlusCompIso U G).app K) =
      ((Functor.mapDerivedCategoryCompIso U G).app K.obj) := by
    apply Iso.ext
    exact Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app _ _ _
  simp only [Functor.mapDerivedCategoryPlusSquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp]
  have hinv := congrArg Iso.inv hcomp
  change DerivedCategory.Plus.ι.map
      ((Functor.mapDerivedCategoryPlusCompIso U G).inv.app K) =
      (Functor.mapDerivedCategoryCompIso U G).inv.app K.obj at hinv
  rw [hinv]
  simp only [Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app]
  rfl

private theorem exact_unit_plus
    {R : Type (u + 1)} [CommRing R] {X Y : Scheme.{u}}
    {J : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)}
    {P : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)} [J.Additive] [P.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits J]
    [CategoryTheory.Limits.PreservesFiniteColimits J]
    [CategoryTheory.Limits.PreservesFiniteLimits P]
    [CategoryTheory.Limits.PreservesFiniteColimits P]
    (a : J ⊣ P)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    DerivedCategory.Plus.ι.map (a.mapDerivedCategoryPlusAdjunction.unit.app K) =
      a.mapDerivedCategoryAdjunction.unit.app K.obj := by
  rw [Adjunction.mapDerivedCategoryPlusAdjunction,
    Adjunction.map_restrictFullyFaithful_unit_app]
  simp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_hom, Iso.refl_inv,
    NatTrans.id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id]
  rfl

private theorem restriction_open_unit_plus
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
        j).mapDerivedCategoryPlusAdjunction.unit.app
          ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj K) ≫
      (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus.map
        ((coefficientRestrictionOpenPlus φ j).hom.app K) =
      (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.map
        ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B)
          j).mapDerivedCategoryPlusAdjunction.unit.app K) ≫
      (Functor.mapDerivedCategoryPlusSquareIso
        (upperStar (ModuleCat.{u + 1} B) j)
        (Sheaf.restrictScalars X.smallEtaleTopology φ)
        (Sheaf.restrictScalars Z.smallEtaleTopology φ)
        (upperStar (ModuleCat.{u + 1} A) j)
        (upperStarRestrictScalarsIso φ j).symm).hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategoryPlus.obj K) := by
  have := coefficientRestrictionOpenMap_isIso φ j
  let β := asIso (coefficientRestrictionOpenMap φ j)
  let τ := (upperStarRestrictScalarsIso φ j).symm
  have hc (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).unit.app
          ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj M) ≫
        (upperStar (ModuleCat.{u + 1} A) j).map (β.hom.app M) =
      (Sheaf.restrictScalars X.smallEtaleTopology φ).map
          ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j).unit.app M) ≫
        τ.hom.app ((openImmersionLowerShriek (ModuleCat.{u + 1} B) j).obj M) := by
    exact (unit_mateEquiv_symm
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j) τ.hom M).symm
  have hd := Adjunction.mapDerivedCategoryAdjunction_mate
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j) τ β hc K.obj
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Functor.map_comp]
  have he := exact_square_plus_hom
    (Sheaf.restrictScalars X.smallEtaleTopology φ)
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j)
    (openImmersionLowerShriek (ModuleCat.{u + 1} B) j)
    (Sheaf.restrictScalars Z.smallEtaleTopology φ) β K
  have ht := exact_square_plus_hom
    (upperStar (ModuleCat.{u + 1} B) j)
    (Sheaf.restrictScalars X.smallEtaleTopology φ)
    (Sheaf.restrictScalars Z.smallEtaleTopology φ)
    (upperStar (ModuleCat.{u + 1} A) j) τ
    ((openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategoryPlus.obj K)
  change _ ≫ (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.map
      (DerivedCategory.Plus.ι.map
        ((Functor.mapDerivedCategoryPlusSquareIso _ _ _ _ β).hom.app K)) =
    (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategory.map
      (DerivedCategory.Plus.ι.map
        ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B)
          j).mapDerivedCategoryPlusAdjunction.unit.app K)) ≫ _
  simp only [exact_unit_plus]
  rw [he, ht]
  exact hd

private theorem mate_restriction_open_plus
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    mateEquiv
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B)
        j).mapDerivedCategoryPlusAdjunction
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
        j).mapDerivedCategoryPlusAdjunction
      (TwoSquare.mk _ _ _ _ (coefficientRestrictionOpenPlus φ j).hom) =
    TwoSquare.mk _ _ _ _
      (Functor.mapDerivedCategoryPlusSquareIso
        (upperStar (ModuleCat.{u + 1} B) j)
        (Sheaf.restrictScalars X.smallEtaleTopology φ)
        (Sheaf.restrictScalars Z.smallEtaleTopology φ)
        (upperStar (ModuleCat.{u + 1} A) j)
        (upperStarRestrictScalarsIso φ j).symm).hom := by
  apply (mateEquiv
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B)
      j).mapDerivedCategoryPlusAdjunction
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
      j).mapDerivedCategoryPlusAdjunction).symm.injective
  rw [Equiv.symm_apply_apply]
  apply TwoSquare.ext
  intro K
  apply ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
    j).mapDerivedCategoryPlusAdjunction.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  rw [restriction_open_unit_plus]
  exact unit_mateEquiv_symm _ _ _ K

private theorem restriction_pullback_comp_plus
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y Z : Scheme.{u}} (k : X ⟶ Y) (j : Y ⟶ Z)
    (L : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    let q (T S : Scheme.{u}) (h : T ⟶ S) :=
      Functor.mapDerivedCategoryPlusSquareIso
        (Sheaf.restrictScalars S.smallEtaleTopology φ)
        (upperStar (ModuleCat.{u + 1} A) h)
        (upperStar (ModuleCat.{u + 1} B) h)
        (Sheaf.restrictScalars T.smallEtaleTopology φ) (upperStarRestrictScalarsIso φ h)
    (q X Z (k ≫ j)).hom.app L ≫
      (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.map
        ((upperStarCompDerivedPlus (ModuleCat.{u + 1} B) k j).hom.app L) =
    (upperStarCompDerivedPlus (ModuleCat.{u + 1} A) k j).hom.app
        ((Sheaf.restrictScalars Z.smallEtaleTopology φ).mapDerivedCategoryPlus.obj L) ≫
      (upperStar (ModuleCat.{u + 1} A) k).mapDerivedCategoryPlus.map
        ((q Y Z j).hom.app L) ≫
      (q X Y k).hom.app ((upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategoryPlus.obj L) := by
  exact Functor.mapDerivedCategoryPlusSquareIso_comp
    (upperStar (ModuleCat.{u + 1} B) j) (upperStar (ModuleCat.{u + 1} B) k)
    (upperStar (ModuleCat.{u + 1} B) (k ≫ j))
    (upperStar (ModuleCat.{u + 1} A) j) (upperStar (ModuleCat.{u + 1} A) k)
    (upperStar (ModuleCat.{u + 1} A) (k ≫ j))
    (Sheaf.restrictScalars Z.smallEtaleTopology φ)
    (Sheaf.restrictScalars Y.smallEtaleTopology φ)
    (Sheaf.restrictScalars X.smallEtaleTopology φ)
    (upperStarRestrictScalarsIso φ j) (upperStarRestrictScalarsIso φ k)
    (upperStarRestrictScalarsIso φ (k ≫ j))
    (upperStarComp (ModuleCat.{u + 1} B) k j)
    (upperStarComp (ModuleCat.{u + 1} A) k j)
    (fun M ↦ by simpa using congr_app (upperStarRestrictScalarsIso_comp_hom φ k j) M) L

private noncomputable abbrev scalarRestrictionPlus
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    (X : Scheme.{u}) :
    (derivedPlusFormalism (ModuleCat.{u + 1} B)).obj X ⥤
      (derivedPlusFormalism (ModuleCat.{u + 1} A)).obj X :=
  (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus

private noncomputable abbrev scalarPullbackPlus
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarRestrictionPlus φ Y ⋙ (derivedPlusFormalism (ModuleCat.{u + 1} A)).pb f ≅
      (derivedPlusFormalism (ModuleCat.{u + 1} B)).pb f ⋙ scalarRestrictionPlus φ X :=
  Functor.mapDerivedCategoryPlusSquareIso
    (Sheaf.restrictScalars Y.smallEtaleTopology φ) (upperStar (ModuleCat.{u + 1} A) f)
    (upperStar (ModuleCat.{u + 1} B) f) (Sheaf.restrictScalars X.smallEtaleTopology φ)
    (upperStarRestrictScalarsIso φ f)

private noncomputable abbrev scalarPushforwardPlus
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarRestrictionPlus φ X ⋙ (derivedPlusFormalism (ModuleCat.{u + 1} A)).pf f ≅
      (derivedPlusFormalism (ModuleCat.{u + 1} B)).pf f ⋙ scalarRestrictionPlus φ Y :=
  (asIso (rightDerivedLowerStarRestrictScalars φ f)).symm

private noncomputable abbrev scalarOpenPlus
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    scalarRestrictionPlus φ X ⋙ (derivedPlusFormalism (ModuleCat.{u + 1} A)).sh j ≅
      (derivedPlusFormalism (ModuleCat.{u + 1} B)).sh j ⋙ scalarRestrictionPlus φ Y :=
  coefficientRestrictionOpenPlus φ j

private theorem scalarPushforwardPlus_mate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    mateEquiv ((derivedPlusFormalism (ModuleCat.{u + 1} B)).adj f)
      ((derivedPlusFormalism (ModuleCat.{u + 1} A)).adj f)
      (TwoSquare.mk _ _ _ _ (scalarPullbackPlus φ f).hom) =
      TwoSquare.mk _ _ _ _ (scalarPushforwardPlus φ f).inv := by
  apply TwoSquare.ext
  intro K
  exact congr_app (rightDerivedLowerStarRestrictScalars_eq_mate φ f).symm K

private theorem scalarOpenPlus_mate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    mateEquiv ((derivedPlusFormalism (ModuleCat.{u + 1} B)).shAdj j)
      ((derivedPlusFormalism (ModuleCat.{u + 1} A)).shAdj j)
      (TwoSquare.mk _ _ _ _ (scalarOpenPlus φ j).hom) =
      TwoSquare.mk _ _ _ _ (scalarPullbackPlus φ j).inv := by
  dsimp only [derivedPlusFormalism]
  rw [mate_restriction_open_plus, derivedSquare_symm]
  rfl

private theorem scalarPullbackPlus_comp
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (w : f ≫ g = h) :
    CoeffCompatible (scalarPullbackPlus φ h)
      (pasteTwoSquaresIso (scalarPullbackPlus φ g) (scalarPullbackPlus φ f))
      ((derivedPlusFormalism (ModuleCat.{u + 1} A)).pbComp' f g h w).hom
      ((derivedPlusFormalism (ModuleCat.{u + 1} B)).pbComp' f g h w).hom := by
  subst h
  intro K
  simpa only [ExchangeFormalism.pbComp'_rfl, derivedPlusFormalism,
    pasteTwoSquaresIso_hom_app]
    using restriction_pullback_comp_plus φ f g K

private theorem scalarPullbackPlus_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U' U Z' Z : Scheme.{u}} (t : U' ⟶ U) (l : U' ⟶ Z')
    (r : U ⟶ Z) (b : Z' ⟶ Z) (w : t ≫ r = l ≫ b) :
    CoeffCompatible (pasteTwoSquaresIso (scalarPullbackPlus φ r) (scalarPullbackPlus φ t))
      (pasteTwoSquaresIso (scalarPullbackPlus φ b) (scalarPullbackPlus φ l))
      ((derivedPlusFormalism (ModuleCat.{u + 1} A)).sqIso t l r b w).hom
      ((derivedPlusFormalism (ModuleCat.{u + 1} B)).sqIso t l r b w).hom := by
  exact (scalarPullbackPlus_comp φ t r (t ≫ r) rfl).inv.comp
    (scalarPullbackPlus_comp φ l b (t ≫ r) w.symm)

private noncomputable abbrev scalarIdentityPlus
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    (X : Scheme.{u}) :=
  Functor.rightUnitor (scalarRestrictionPlus φ X) ≪≫
    (Functor.leftUnitor (scalarRestrictionPlus φ X)).symm

private theorem scalarPullbackPlus_id
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (X : Scheme.{u}) :
    CoeffCompatible (scalarPullbackPlus φ (𝟙 X)) (scalarIdentityPlus φ X)
      ((derivedPlusFormalism (ModuleCat.{u + 1} A)).pbId X).hom
      ((derivedPlusFormalism (ModuleCat.{u + 1} B)).pbId X).hom := by
  dsimp only [derivedPlusFormalism]
  intro K
  have h := square_identity (Sheaf.restrictScalars X.smallEtaleTopology φ)
    (upperStar (ModuleCat.{u + 1} A) (𝟙 X))
    (upperStar (ModuleCat.{u + 1} B) (𝟙 X))
    (upperStarRestrictScalarsIso φ (𝟙 X))
    (upperStarId (ModuleCat.{u + 1} B) X) (upperStarId (ModuleCat.{u + 1} A) X)
    (fun M ↦ by
      simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app,
        Functor.comp_obj, Functor.id_obj, Category.comp_id] using
          congr_app (upperStarRestrictScalarsIso_id_hom φ X) M) K
  simp only [upperStarIdDerivedPlus, scalarIdentityPlus,
    scalarPullbackPlus, scalarRestrictionPlus, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app, Category.comp_id,
    Category.assoc] at h ⊢
  exact h.trans (scalar_comp_id
    ((Functor.mapDerivedCategoryPlusNatIso (upperStarId (ModuleCat.{u + 1} A) X)).hom.app
      ((scalarRestrictionPlus φ X).obj K))
    ((Functor.mapDerivedCategoryPlusIdIso
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))).hom.app
        ((scalarRestrictionPlus φ X).obj K)))

private theorem scalarPushforwardPlus_comp
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (w : f ≫ g = h) :
    CoeffCompatible
      (pasteTwoSquaresIso (scalarPushforwardPlus φ f) (scalarPushforwardPlus φ g))
      (scalarPushforwardPlus φ h)
      ((derivedPlusFormalism (ModuleCat.{u + 1} A)).pfComp' f g h w).inv
      ((derivedPlusFormalism (ModuleCat.{u + 1} B)).pfComp' f g h w).inv := by
  exact scalar_pushforward_comp
    ((derivedPlusFormalism (ModuleCat.{u + 1} A)).adj f)
    ((derivedPlusFormalism (ModuleCat.{u + 1} A)).adj g)
    ((derivedPlusFormalism (ModuleCat.{u + 1} A)).adj h)
    ((derivedPlusFormalism (ModuleCat.{u + 1} B)).adj f)
    ((derivedPlusFormalism (ModuleCat.{u + 1} B)).adj g)
    ((derivedPlusFormalism (ModuleCat.{u + 1} B)).adj h)
    (scalarPullbackPlus φ f) (scalarPushforwardPlus φ f)
    (scalarPullbackPlus φ g) (scalarPushforwardPlus φ g)
    (scalarPullbackPlus φ h) (scalarPushforwardPlus φ h)
    (congrArg TwoSquare.natTrans (scalarPushforwardPlus_mate φ f))
    (congrArg TwoSquare.natTrans (scalarPushforwardPlus_mate φ g))
    (congrArg TwoSquare.natTrans (scalarPushforwardPlus_mate φ h))
    ((derivedPlusFormalism (ModuleCat.{u + 1} A)).pbComp' f g h w)
    ((derivedPlusFormalism (ModuleCat.{u + 1} B)).pbComp' f g h w)
    (scalarPullbackPlus_comp φ f g h w)

/-- Scalar restriction respects the open base-change mate for a commutative square.
Source: Stacks Project, Tags 0F7J and 0GL6.
(blueprint: lem-sf-etale-restriction-open-base-change).

Proof: localize the scalar inverse-image composition equations to bounded-below
complexes. Their composite and inverse identify the scalar square for the geometric
inverse-image square. The exact localized extension-by-zero adjunction has the
localized scalar pullback square as its mate, by the unit identity. Transpose the
inverse-image cube under those two adjunctions. The generic mate-cube lemma and
cancellation of the scalar pullback isomorphisms give the displayed square.
No cartesianness or invertibility of geometric base change is used. -/
theorem compactSupportRestrictionPlus_openBaseChange
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U' U Z' Z : Scheme.{u}} (t : U' ⟶ U) (l : U' ⟶ Z')
    (r : U ⟶ Z) (b : Z' ⟶ Z) [IsOpenImmersion l] [IsOpenImmersion r]
    (w : t ≫ r = l ≫ b) :
    CoeffCompatible
      (pasteTwoSquaresIso (Functor.mapDerivedCategoryPlusSquareIso
        (Sheaf.restrictScalars U.smallEtaleTopology φ)
        (upperStar (ModuleCat.{u + 1} A) t)
        (upperStar (ModuleCat.{u + 1} B) t)
        (Sheaf.restrictScalars U'.smallEtaleTopology φ)
        (upperStarRestrictScalarsIso φ t)) (coefficientRestrictionOpenPlus φ l))
      (pasteTwoSquaresIso (coefficientRestrictionOpenPlus φ r)
        (Functor.mapDerivedCategoryPlusSquareIso
        (Sheaf.restrictScalars Z.smallEtaleTopology φ)
        (upperStar (ModuleCat.{u + 1} A) b)
        (upperStar (ModuleCat.{u + 1} B) b)
        (Sheaf.restrictScalars Z'.smallEtaleTopology φ)
        (upperStarRestrictScalarsIso φ b)))
      ((derivedPlusFormalism (ModuleCat.{u + 1} A)).baseChange t l r b w).natTrans
      ((derivedPlusFormalism (ModuleCat.{u + 1} B)).baseChange t l r b w).natTrans := by
  let FA := derivedPlusFormalism (ModuleCat.{u + 1} A)
  let FB := derivedPlusFormalism (ModuleCat.{u + 1} B)
  exact scalar_baseChange_cube (FB.shAdj r) (FA.shAdj r) (FB.shAdj l) (FA.shAdj l)
    (scalarRestrictionPlus φ U) (scalarRestrictionPlus φ Z)
    (scalarRestrictionPlus φ U') (scalarRestrictionPlus φ Z')
    (FB.pb t) (FB.pb b) (FA.pb t) (FA.pb b)
    (scalarOpenPlus φ r) (scalarOpenPlus φ l)
    (scalarPullbackPlus φ r) (scalarPullbackPlus φ l)
    (scalarPullbackPlus φ t) (scalarPullbackPlus φ b)
    (scalarOpenPlus_mate φ r) (scalarOpenPlus_mate φ l)
    (FA.sqIso t l r b w) (FB.sqIso t l r b w)
    (scalarPullbackPlus_square φ t l r b w)


end AlgebraicGeometry.Etale
