/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.AbsoluteFrobenius
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompIsoUnit
public import WeilConjectures.SixFunctors.LowerShriek.Formalism.Frobenius
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence
import WeilConjectures.SixFunctors.Etale.Derived.CompactificationRefinementLowerStar
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement

/-!
# The absolute Frobenius in the unbounded compact support formalism

This file identifies the trivializations of the derived pullback, direct image and compactly
supported direct image along the absolute Frobenius with the trivializations of the abstract
compact support formalism of the unbounded étale derived categories
(`AlgebraicGeometry.CompactSupportFormalism.lowerShriekTriv`), and deduces the compatibility of
these trivializations with the composition isomorphisms of the compactly supported direct images
from its abstract form `AlgebraicGeometry.CompactSupportFormalism.lowerShriekCompIso_inv_triv`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

section Generic

variable {C D : Type*} [Category C] [Category D]

/-- The conjugate of a trivialization `τ : L' ≅ 𝟭` of a left adjoint `L' ≅ L` of `R` is the
right adjoint uniqueness isomorphism for the trivialization `L ≅ L' ≅ 𝟭`. -/
lemma CategoryTheory.conjugateIsoEquiv_ofNatIsoLeft_id {L L' : C ⥤ C} {R : C ⥤ C}
    (a : L ⊣ R) (ι : L ≅ L') (τ : L' ≅ 𝟭 C) :
    conjugateIsoEquiv (a.ofNatIsoLeft ι) Adjunction.id τ.symm =
      a.rightAdjointUniq (Adjunction.id.ofNatIsoLeft (ι ≪≫ τ).symm) := by
  apply Iso.ext
  rw [← Iso.inv_eq_inv]
  ext K
  simp [Adjunction.rightAdjointUniq, conjugateIsoEquiv]

/-- The two isomorphisms `D(H) ≅ D(P)` induced by isomorphisms `m₁ : H ≅ P ⋙ I_X`,
`m₂ : H ≅ I_Y ⋙ P` and trivializations `e_X : I_X ≅ 𝟭`, `e_Y : I_Y ≅ 𝟭` of exact functors
agree as soon as the underived isomorphisms `H ≅ P` agree. -/
lemma CategoryTheory.Functor.mapDerivedCategoryTriangleIso_triv [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] (P : C ⥤ D) (IX : D ⥤ D) (IY : C ⥤ C)
    (H : C ⥤ D) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [IX.Additive] [PreservesFiniteLimits IX] [PreservesFiniteColimits IX]
    [IY.Additive] [PreservesFiniteLimits IY] [PreservesFiniteColimits IY]
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (eX : IX ≅ 𝟭 D) (eY : IY ≅ 𝟭 C) (m₁ : H ≅ P ⋙ IX) (m₂ : H ≅ IY ⋙ P)
    (h : m₁ ≪≫ Functor.isoWhiskerLeft P eX ≪≫ P.rightUnitor =
      m₂ ≪≫ Functor.isoWhiskerRight eY P ≪≫ P.leftUnitor) :
    (mapDerivedCategoryTriangleIso m₁).hom ≫
        Functor.whiskerLeft P.mapDerivedCategory
          (mapDerivedCategoryNatIso eX ≪≫ mapDerivedCategoryIdIso D).hom ≫
        (Functor.rightUnitor _).hom =
      (mapDerivedCategoryTriangleIso m₂).hom ≫
        Functor.whiskerRight (mapDerivedCategoryNatIso eY ≪≫ mapDerivedCategoryIdIso C).hom
          P.mapDerivedCategory ≫
        (Functor.leftUnitor _).hom := by
  have hl : (mapDerivedCategoryNatIso P.rightUnitor).hom = 𝟙 _ :=
    mapDerivedCategoryNatIso_refl
  have hr : (mapDerivedCategoryNatIso P.leftUnitor).hom = 𝟙 _ :=
    mapDerivedCategoryNatIso_refl
  have e := congrArg (fun e ↦ (mapDerivedCategoryNatIso e).hom) h
  simp only [mapDerivedCategoryNatIso_trans, hl, hr, Category.comp_id] at e
  simp only [mapDerivedCategoryTriangleIso, Iso.trans_hom, Iso.symm_hom,
    Functor.whiskerLeft_comp, Functor.whiskerRight_comp, Category.assoc]
  rw [← Category.assoc (mapDerivedCategoryCompIso P IX).inv,
    ← mapDerivedCategoryNatIso_isoWhiskerLeft, Category.assoc,
    ← Category.assoc (mapDerivedCategoryCompIso P (𝟭 D)).inv,
    mapDerivedCategoryCompIso_comp_id,
    ← Category.assoc (mapDerivedCategoryCompIso IY P).inv,
    ← mapDerivedCategoryNatIso_isoWhiskerRight, Category.assoc,
    ← Category.assoc (mapDerivedCategoryCompIso (𝟭 C) P).inv,
    mapDerivedCategoryCompIso_id_comp]
  simp only [← Category.assoc]
  rw [e]
  ext K
  simp


/-- The component form of an equation of natural transformations
`c₁⁻¹ ≫ (ρ_X ◫ G) = e ≫ c₂⁻¹ ≫ (G ◫ ρ_Y)` between functors `H ⟶ G`, for `c₁ : L_X ⋙ G ≅ H`,
`c₂ : G ⋙ L_Y ≅ H'`, `e : H ≅ H'` and trivializations `ρ_X : L_X ≅ 𝟭`, `ρ_Y : L_Y ≅ 𝟭`. -/
lemma CategoryTheory.Iso.inv_app_comp_map_hom_app_eq_of_whisker {H H' : C ⥤ D} {LX : C ⥤ C}
    {LY : D ⥤ D} {G : C ⥤ D} (c₁ : LX ⋙ G ≅ H) (c₂ : G ⋙ LY ≅ H') (e : H ≅ H')
    (ρX : LX ≅ 𝟭 C) (ρY : LY ≅ 𝟭 D)
    (h : c₁.inv ≫ Functor.whiskerRight ρX.hom G ≫ (Functor.leftUnitor G).hom =
      e.hom ≫ c₂.inv ≫ Functor.whiskerLeft G ρY.hom ≫ (Functor.rightUnitor G).hom) (K : C) :
    c₁.inv.app K ≫ G.map (ρX.hom.app K) =
      e.hom.app K ≫ c₂.inv.app K ≫ ρY.hom.app (G.obj K) := by
  simpa using NatTrans.congr_app h K
end Generic

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} (hp : p.Prime) (n : ℕ)

/-- The trivialization `D(F_X^*) ≅ 𝟭` of the exact pullback along the absolute Frobenius, induced
by `AlgebraicGeometry.Etale.upperStarIterateFrobeniusIso`. -/
noncomputable def mapDerivedUpperStarIterateFrobeniusTriv {X : Scheme.{u}}
    (hX : (p : Γ(X, ⊤)) = 0) :
    (upperStar (ModuleCat.{u + 1} Λ) (X.iterateFrobenius hp hX n)).mapDerivedCategory ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso
      (upperStarIterateFrobeniusIso (ModuleCat.{u + 1} Λ) hp hX n ≪≫
        upperStarId (ModuleCat.{u + 1} Λ) X) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The trivializations of `mapDerivedUpperStarIterateFrobeniusTriv` are compatible with the
pullback along a morphism of schemes of characteristic `p`, in the unbounded compact support
formalism. -/
private lemma unbounded_pbComp'_iterateFrobenius {X Y : Scheme.{u}} (hX : (p : Γ(X, ⊤)) = 0)
    (hY : (p : Γ(Y, ⊤)) = 0) (j : X ⟶ Y)
    (w : j ≫ Y.iterateFrobenius hp hY n = X.iterateFrobenius hp hX n ≫ j) :
    ((unboundedFormalism Λ).pbComp' (X.iterateFrobenius hp hX n) j
        (X.iterateFrobenius hp hX n ≫ j) rfl).hom ≫
        Functor.whiskerLeft ((unboundedFormalism Λ).pb j)
          (mapDerivedUpperStarIterateFrobeniusTriv Λ hp n hX).hom ≫
        (Functor.rightUnitor _).hom =
      ((unboundedFormalism Λ).pbComp' j (Y.iterateFrobenius hp hY n)
        (X.iterateFrobenius hp hX n ≫ j) w).hom ≫
        Functor.whiskerRight (mapDerivedUpperStarIterateFrobeniusTriv Λ hp n hY).hom
          ((unboundedFormalism Λ).pb j) ≫
        (Functor.leftUnitor _).hom := by
  rw [unbounded_pb_comp', unbounded_pb_comp']
  refine Functor.mapDerivedCategoryTriangleIso_triv _ _ _ _ _ _ _ _ ?_
  have N := upperStarIterateFrobeniusIso_naturality (ModuleCat.{u + 1} Λ) hp hX n hY j
  rw [upperStarComp_id_left, upperStarComp_id_right] at N
  apply Iso.ext
  have N' := congrArg Iso.hom N
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_comp, Functor.whiskerRight_comp,
    Category.assoc] at N' ⊢
  exact N'.symm


/-- The trivialization `L(F_X)^* ≅ L(𝟙)^* ≅ 𝟭` is the trivialization
`mapDerivedUpperStarIterateFrobeniusTriv` through `L(F_X)^* ≅ D(F_X^*)`. -/
lemma leftDerivedUpperStarIterateFrobeniusIso_trans_leftDerivedUpperStarId {X : Scheme.{u}}
    (hX : (p : Γ(X, ⊤)) = 0) :
    leftDerivedUpperStarIterateFrobeniusIso (ModuleCat.{u + 1} Λ) hp hX n ≪≫
        leftDerivedUpperStarId _ X =
      leftDerivedUpperStarIsoMapDerivedCategory _ (X.iterateFrobenius hp hX n) ≪≫
        mapDerivedUpperStarIterateFrobeniusTriv Λ hp n hX := by
  ext1
  simp [leftDerivedUpperStarIterateFrobeniusIso, leftDerivedUpperStarId,
    Functor.leftDerivedFunctorNatIso, leftDerivedUpperStarIsoMapDerivedCategory,
    mapDerivedUpperStarIterateFrobeniusTriv, Functor.mapDerivedCategoryNatIso_trans]

/-- The trivialization `R(F_X)_* ≅ 𝟭` right adjoint to `L(F_X)^* ≅ 𝟭` is the trivialization of the
pushforward along the Frobenius in the unbounded compact support formalism. -/
private lemma rightAdjointUniq_eq_unbounded_pfTriv {X : Scheme.{u}} (hX : (p : Γ(X, ⊤)) = 0) :
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (X.iterateFrobenius hp hX n)).rightAdjointUniq
      (Adjunction.id.ofNatIsoLeft
        (leftDerivedUpperStarIterateFrobeniusIso (ModuleCat.{u + 1} Λ) hp hX n ≪≫
          leftDerivedUpperStarId _ X).symm) =
      (unboundedFormalism Λ).pfTriv (X.iterateFrobenius hp hX n)
        (mapDerivedUpperStarIterateFrobeniusTriv Λ hp n hX) := by
  have hadj : (unboundedFormalism Λ).adj (X.iterateFrobenius hp hX n) =
      mapDerivedUpperStarLowerStarAdjunction _ (X.iterateFrobenius hp hX n) := rfl
  rw [ExchangeFormalism.pfTriv, hadj, mapDerivedUpperStarLowerStarAdjunction_eq,
    conjugateIsoEquiv_ofNatIsoLeft_id,
    leftDerivedUpperStarIterateFrobeniusIso_trans_leftDerivedUpperStarId]

/-- The forget-supports map of the trivial compactification of a proper `g` is the identity
`(𝟙)_! ≅ 𝟭` of the unbounded compact support formalism. -/
private lemma compactificationForgetSupports_ofIsProper {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsProper g] :
    compactificationForgetSupports (ModuleCat.{u + 1} Λ) (Compactification.ofIsProper g) =
      Functor.whiskerRight ((unboundedFormalism Λ).shId X).hom ((unboundedFormalism Λ).pf g) ≫
        (Functor.leftUnitor _).hom := by
  have : IsIso ((unboundedFormalism Λ).shAdj (𝟙 X)).unit :=
    isIso_derivedOpenImmersionLowerShriekUpperStarAdjunction_unit _ (𝟙 X)
  have hS : derivedOpenImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) (𝟙 X) =
      (unboundedFormalism Λ).shToPf (𝟙 X) := rfl
  have hC := rightDerivedLowerStarComp_hom_comp_congr_hom (ModuleCat.{u + 1} Λ) (𝟙 X) g g
    (Category.id_comp g).symm
  have hP := congrArg Iso.inv (unbounded_pf_comp Λ (𝟙 X) g)
  rw [Iso.symm_inv] at hP
  rw [← hP, rightDerivedLowerStarCongr, eqToIso.hom,
    ← ExchangeFormalism.pfComp'_inv_eq _ _ _ _ (Category.id_comp g)] at hC
  calc compactificationForgetSupports (ModuleCat.{u + 1} Λ) (Compactification.ofIsProper g)
      _ = Functor.whiskerRight ((unboundedFormalism Λ).shToPf (𝟙 X))
          ((unboundedFormalism Λ).pf g) ≫
          ((unboundedFormalism Λ).pfComp' (𝟙 X) g g (Category.id_comp g)).inv := by
        rw [hC, hS.symm]
        rfl
      _ = _ := (unboundedFormalism Λ).whiskerRight_shToPf_id_comp_pfComp'_inv g

variable [Finite Λ]

attribute [local instance] unbounded_has_base_change unbounded_has_proper_exchange

/-- The forget-supports maps intertwine the comparison isomorphisms of two compactifications. -/
private lemma rightDerivedLowerShriekOfCompactificationIso_hom_comp_forgetSupports
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c d : Compactification f) :
    (rightDerivedLowerShriekOfCompactificationIso Λ c d).hom ≫
        compactificationForgetSupports (ModuleCat.{u + 1} Λ) d =
      compactificationForgetSupports (ModuleCat.{u + 1} Λ) c := by
  ext M
  exact rightDerivedLowerShriekOfCompactificationIso_hom_app_comp_toLowerStar Λ c d M

/-- The trivialization `R(F_X)_! ≅ R(F_X)_* ≅ 𝟭` is the trivialization of the compactly supported
direct image along the Frobenius in the unbounded compact support formalism. -/
private lemma unbounded_lowerShriekTriv_eq {X : Scheme.{u}} (hX : (p : Γ(X, ⊤)) = 0)
    [IsProper (X.iterateFrobenius hp hX n)] :
    rightDerivedLowerShriekIsoRightDerivedLowerStar _ (X.iterateFrobenius hp hX n) ≪≫
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          (X.iterateFrobenius hp hX n)).rightAdjointUniq
        (Adjunction.id.ofNatIsoLeft
          (leftDerivedUpperStarIterateFrobeniusIso (ModuleCat.{u + 1} Λ) hp hX n ≪≫
            leftDerivedUpperStarId _ X).symm) =
      (unboundedFormalism Λ).lowerShriekTriv (X.iterateFrobenius hp hX n)
        (mapDerivedUpperStarIterateFrobeniusTriv Λ hp n hX) := by
  ext1
  rw [Iso.trans_hom,
    rightDerivedLowerShriekIsoRightDerivedLowerStar_hom_eq_compactificationForgetSupports,
    rightAdjointUniq_eq_unbounded_pfTriv,
    ← rightDerivedLowerShriekOfCompactificationIso_hom_comp_forgetSupports Λ _
      (Compactification.ofIsProper _),
    compactificationForgetSupports_ofIsProper, ← unbounded_shriek_iso]
  simp only [CompactSupportFormalism.lowerShriekTriv, CompactSupportFormalism.shriekOfIsProperTriv,
    Iso.trans_hom, Functor.isoWhiskerRight_hom, Category.assoc]

omit [Finite Λ] in
/-- The congruence isomorphism of the lower shriek is that of the unbounded compact support
formalism. -/
private lemma unbounded_lowerShriekCongr_eq {X Y : Scheme.{u}} {g₁ g₂ : X ⟶ Y}
    [HasCompactification g₁] [HasCompactification g₂] (h : g₁ = g₂) :
    (unboundedFormalism Λ).lowerShriekCongr h = rightDerivedLowerShriekCongrIso Λ h := by
  subst h
  rfl

/-- **The absolute Frobenius commutes with the compactly supported direct image**, for
trivializations `ρ_X`, `ρ_Y` given by their defining formulas. -/
theorem rightDerivedLowerShriekCompIso_iterateFrobenius_of_eq {X Y : Scheme.{u}}
    (hX : (p : Γ(X, ⊤)) = 0) (hY : (p : Γ(Y, ⊤)) = 0) (f : X ⟶ Y) [HasCompactification f]
    [QuasiCompact f] [IsProper (X.iterateFrobenius hp hX n)]
    [IsProper (Y.iterateFrobenius hp hY n)] [HasCompactification (X.iterateFrobenius hp hX n ≫ f)]
    [QuasiCompact (X.iterateFrobenius hp hX n ≫ f)]
    [HasCompactification (f ≫ Y.iterateFrobenius hp hY n)]
    [QuasiCompact (f ≫ Y.iterateFrobenius hp hY n)]
    (ρX : R(X.iterateFrobenius hp hX n)_![ModuleCat.{u + 1} Λ] ≅ 𝟭 _)
    (hρX : ρX = rightDerivedLowerShriekIsoRightDerivedLowerStar _ (X.iterateFrobenius hp hX n) ≪≫
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          (X.iterateFrobenius hp hX n)).rightAdjointUniq
        (Adjunction.id.ofNatIsoLeft
          (leftDerivedUpperStarIterateFrobeniusIso (ModuleCat.{u + 1} Λ) hp hX n ≪≫
            leftDerivedUpperStarId _ X).symm))
    (ρY : R(Y.iterateFrobenius hp hY n)_![ModuleCat.{u + 1} Λ] ≅ 𝟭 _)
    (hρY : ρY = rightDerivedLowerShriekIsoRightDerivedLowerStar _ (Y.iterateFrobenius hp hY n) ≪≫
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          (Y.iterateFrobenius hp hY n)).rightAdjointUniq
        (Adjunction.id.ofNatIsoLeft
          (leftDerivedUpperStarIterateFrobeniusIso (ModuleCat.{u + 1} Λ) hp hY n ≪≫
            leftDerivedUpperStarId _ Y).symm))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekCompIso Λ (X.iterateFrobenius hp hX n) f).hom.app K ≫
        (R(f)_![ModuleCat.{u + 1} Λ]).map (ρX.hom.app K) =
      (rightDerivedLowerShriekCongrIso Λ (comp_iterateFrobenius hp f hY hX n).symm).hom.app K ≫
        (rightDerivedLowerShriekCompIso Λ f (Y.iterateFrobenius hp hY n)).hom.app K ≫
        ρY.hom.app ((R(f)_![ModuleCat.{u + 1} Λ]).obj K) := by
  set c := HasCompactification.compactification f
  have hZ : (p : Γ(c.Z, ⊤)) = 0 := IsOfCharacteristic.of_hom hY c.g
  have := c.isProper
  have hg : c.Z.iterateFrobenius hp hZ n ≫ c.g = c.g ≫ Y.iterateFrobenius hp hY n :=
    (comp_iterateFrobenius hp c.g hY hZ n).symm
  have : IsProper (c.Z.iterateFrobenius hp hZ n ≫ c.g) := by
    rw [hg]
    infer_instance
  have : IsProper (c.Z.iterateFrobenius hp hZ n) := .of_comp _ c.g
  have hsq : IsPullback (X.iterateFrobenius hp hX n) c.i c.i (c.Z.iterateFrobenius hp hZ n) :=
    isPullback_iterateFrobenius hp hZ n c.i
  have h := (unboundedFormalism Λ).lowerShriekCompIso_inv_triv c (X.iterateFrobenius hp hX n)
    (Y.iterateFrobenius hp hY n) (c.Z.iterateFrobenius hp hZ n)
    (comp_iterateFrobenius hp f hY hX n).symm hsq hg
    (mapDerivedUpperStarIterateFrobeniusTriv Λ hp n hX)
    (mapDerivedUpperStarIterateFrobeniusTriv Λ hp n hY)
    (mapDerivedUpperStarIterateFrobeniusTriv Λ hp n hZ)
    (unbounded_pbComp'_iterateFrobenius Λ hp n hX hZ c.i hsq.w.symm)
    (unbounded_pbComp'_iterateFrobenius Λ hp n hZ hY c.g hg.symm)
  rw [unbounded_chosen_comp, unbounded_chosen_comp, ← unbounded_lowerShriekTriv_eq,
    ← unbounded_lowerShriekTriv_eq, ← hρX, ← hρY, unbounded_lowerShriekCongr_eq] at h
  rw [rightDerivedLowerShriekCompIso_eq_symm, rightDerivedLowerShriekCompIso_eq_symm,
    Iso.symm_hom, Iso.symm_hom]
  exact CategoryTheory.Iso.inv_app_comp_map_hom_app_eq_of_whisker _ _ _ _ _ h K
end AlgebraicGeometry.Etale
