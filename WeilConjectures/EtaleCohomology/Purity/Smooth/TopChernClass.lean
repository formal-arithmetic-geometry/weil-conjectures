/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.LocalizedChern
public import WeilConjectures.EtaleCohomology.Purity.Smooth.HomotopyInvariance
public import WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange

/-!
# The top Chern class of a vector bundle

The *top Chern class* (Euler class) `c_r(V) ∈ H^{2r}(T, Λ(r))` of a vector bundle `π : V ⟶ T` of
rank `r` is the localized top Chern class of the zero section with supports forgotten,
`c_r(V) = 0^* th(V)` (`AlgebraicGeometry.VectorBundle.topChernClass`). For a rank-one bundle this
is the first Chern class.

Property (L4) of `thm-pur-localized-top-chern` says that the localized top Chern class of *any*
section `s` becomes `c_r(V)` after forgetting supports
(`AlgebraicGeometry.VectorBundle.forgetSupports_localizedTopChern`); for a line bundle and a
section cutting out a divisor `D` this is the comparison `cl(D) = c₁(𝒪(D))` of
`lem-pur-divisor-class` (b) (`AlgebraicGeometry.VectorBundle.forgetSupports_localizedTopChern_one`).
Both are proved here from homotopy invariance with twisted coefficients, the unit
`Λ_T(m)[2m] ⟶ Rπ_* Lπ^* Λ_T(m)[2m]` being an isomorphism
(`AlgebraicGeometry.VectorBundle.isIso_unit_tateObjectShift`): every class on `V` is then pulled
back from `T`, so its restrictions along the sections `s` and `0` agree
(`AlgebraicGeometry.VectorBundle.classRestriction_section_eq_of_isIso_unit`). Homotopy invariance
is proved for relative affine space
(`AlgebraicGeometry.Etale.isIso_unit_tateObjectShift_affineSpace`)
and glued along the trivialising opens.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

namespace VectorBundle

variable {V T : Scheme.{u}} {r : ℕ} {π : V ⟶ T} (E : VectorBundle r π)
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] [HasInvertibleExponent Λ V]
  {k : Type u} [Field k] (aT : T ⟶ Spec (.of k)) [IsSeparated aT] [LocallyOfFiniteType aT]

/-- The localized top Chern class of a section `s`, with supports forgotten: a class in
`H^{2r}(T, Λ(r)) = Hom(Λ_T, Λ_T(r)[2r])`. -/
noncomputable def localizedTopChernForget (s : T ⟶ V) :
    haveI : HasInvertibleExponent Λ T := .of_hom E.zero
    constantComplex Λ T ⟶ (tateObject Λ T r)⟦2 * (r : ℤ)⟧ :=
  haveI : HasInvertibleExponent Λ T := .of_hom E.zero
  E.localizedTopChern s Λ aT ≫
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) (pullback.snd E.zero s)).counit.app _

/-- Blueprint `thm-pur-localized-top-chern`: the *top Chern class* (Euler class)
`c_r(V) ∈ H^{2r}(T, Λ(r))` of a vector bundle of rank `r`: the localized top Chern class of the
zero section with supports forgotten. For `r = 1` it is the first Chern class `c₁`. -/
noncomputable def topChernClass :
    haveI : HasInvertibleExponent Λ T := .of_hom E.zero
    constantComplex Λ T ⟶ (tateObject Λ T r)⟦2 * (r : ℤ)⟧ :=
  E.localizedTopChernForget Λ aT E.zero

/-- The restriction `g^* c ∈ H^{2r}(T, Λ(r))` of a class `c ∈ H^{2r}(V, Λ(r))` along
`g : T ⟶ V`. -/
noncomputable def classRestriction {T' V' : Scheme.{u}} [HasInvertibleExponent Λ T']
    [HasInvertibleExponent Λ V'] (g : T' ⟶ V')
    (c : constantComplex Λ V' ⟶ (tateObject Λ V' r)⟦2 * (r : ℤ)⟧) :
    constantComplex Λ T' ⟶ (tateObject Λ T' r)⟦2 * (r : ℤ)⟧ :=
  (leftDerivedUpperStarConstantComplexIso Λ g).inv ≫ (L((g)^*[ModuleCat.{u + 1} Λ])).map c ≫
    (leftDerivedUpperStarTateShiftIso Λ g r).hom

omit [HasInvertibleExponent Λ V] in
/-- The localized top Chern class of `s` with supports forgotten is the restriction along `s` of
the Thom class with supports forgotten: forgetting supports commutes with the restriction of
supports (`AlgebraicGeometry.Etale.supportedRestriction_comp_counit`). -/
lemma localizedTopChernForget_eq [HasInvertibleExponent Λ V] (s : T ⟶ V) :
    haveI : HasInvertibleExponent Λ T := .of_hom E.zero
    E.localizedTopChernForget Λ aT s = classRestriction Λ s (E.thomClass Λ aT ≫
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) E.zero).counit.app _) := by
  simp only [localizedTopChernForget, localizedTopChern, restrictSupportedClass, classRestriction,
    Category.assoc, supportedRestriction_comp_counit, Functor.map_comp]

omit [Finite Λ] [HasKummerClass.IsNormalized Λ] [HasInvertibleExponent Λ V] in
/-- Restriction of classes is compatible with composition. -/
lemma classRestriction_comp {X Y Z : Scheme.{u}} [HasInvertibleExponent Λ X]
    [HasInvertibleExponent Λ Y] [HasInvertibleExponent Λ Z] (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (h : fg = f ≫ g)
    (c : constantComplex Λ Z ⟶ (tateObject Λ Z r)⟦2 * (r : ℤ)⟧) :
    classRestriction Λ fg c = classRestriction Λ f (classRestriction Λ g c) := by
  simp only [classRestriction, leftDerivedUpperStarConstantComplexIso_comp Λ f g fg h,
    leftDerivedUpperStarTateShiftIso_comp Λ f g fg h, Iso.trans_inv, Iso.trans_hom,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp,
    Category.assoc]
  congr 2
  rw [← NatTrans.naturality_assoc, Iso.inv_hom_id_app_assoc]
  rfl

omit [Finite Λ] [HasKummerClass.IsNormalized Λ] [HasInvertibleExponent Λ V] in
/-- Restriction of classes along the identity is the identity: it is idempotent by
`AlgebraicGeometry.VectorBundle.classRestriction_comp`, and injective since `L(𝟙)^* ≅ 𝟭`. -/
lemma classRestriction_id {X : Scheme.{u}} [HasInvertibleExponent Λ X]
    (c : constantComplex Λ X ⟶ (tateObject Λ X r)⟦2 * (r : ℤ)⟧) :
    classRestriction Λ (𝟙 X) c = c := by
  have h := classRestriction_comp Λ (𝟙 X) (𝟙 X) (𝟙 X) (Category.id_comp _).symm c
  have inj : Function.Injective (classRestriction Λ (r := r) (𝟙 X)) := by
    intro a b hab
    simp only [classRestriction] at hab
    rw [cancel_epi, cancel_mono] at hab
    obtain ⟨e⟩ := nonempty_leftDerivedUpperStar_id_iso Λ X (𝟙 X) rfl
    have : (L((𝟙 X)^*[ModuleCat.{u + 1} Λ])).Faithful := Functor.Faithful.of_iso e.symm
    exact Functor.map_injective _ hab
  exact inj h.symm

omit [Finite Λ] [HasKummerClass.IsNormalized Λ] [HasInvertibleExponent Λ V] in
/-- *Restriction along sections, given homotopy invariance.* Let `π : V ⟶ T` be a morphism with
sections `s, s'`. If the unit `Λ_T(r)[2r] ⟶ Rπ_* Lπ^* Λ_T(r)[2r]` is an isomorphism, every
class `c ∈ H^{2r}(V, Λ(r))` is pulled back from `T`, so `s^* c = (s ≫ π)^* b = s'^* c`. -/
lemma classRestriction_section_eq_of_isIso_unit [HasInvertibleExponent Λ V]
    [HasInvertibleExponent Λ T] {π' : V ⟶ T} (s s' : T ⟶ V) (hs : s ≫ π' = 𝟙 T)
    (hs' : s' ≫ π' = 𝟙 T)
    (hπ : IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π').unit.app
      ((tateObject Λ T r)⟦2 * (r : ℤ)⟧)))
    (c : constantComplex Λ V ⟶ (tateObject Λ V r)⟦2 * (r : ℤ)⟧) :
    classRestriction Λ s c = classRestriction Λ s' c := by
  let adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π'
  -- `c` is pulled back from `T`
  let b : constantComplex Λ T ⟶ (tateObject Λ T r)⟦2 * (r : ℤ)⟧ :=
    adj.homEquiv _ _ ((leftDerivedUpperStarConstantComplexIso Λ π').hom ≫ c ≫
      (leftDerivedUpperStarTateShiftIso Λ π' r).inv) ≫
      inv (adj.unit.app ((tateObject Λ T r)⟦2 * (r : ℤ)⟧))
  have hb : classRestriction Λ π' b = c := by
    have h₁ : (L((π')^*[ModuleCat.{u + 1} Λ])).map b =
        (leftDerivedUpperStarConstantComplexIso Λ π').hom ≫ c ≫
          (leftDerivedUpperStarTateShiftIso Λ π' r).inv := by
      apply (adj.homEquiv _ _).injective
      have hn := adj.unit.naturality b
      simp only [Functor.id_map, Functor.comp_map] at hn
      rw [Adjunction.homEquiv_unit, ← hn]
      simp only [b, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    simp only [classRestriction, h₁, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id]
  rw [← hb, ← classRestriction_comp Λ s π' (𝟙 T) hs.symm,
    ← classRestriction_comp Λ s' π' (𝟙 T) hs'.symm]

omit [HasInvertibleExponent Λ V] in
include E aT in
/-- **Homotopy invariance for vector bundles**, with twisted coefficients: the unit
`Λ_T(m)[2m] ⟶ Rπ_* Lπ^* Λ_T(m)[2m]` is an isomorphism. Isomorphisms are detected on the
trivialising opens `U i`; there the unit restricts to the unit of `π⁻¹(U i) ⟶ U i`
(`AlgebraicGeometry.Etale.isIso_upperStar_map_unit_of_isPullback`, open base change), which
through the chart `π⁻¹(U i) ≅ 𝔸^r_{U i}` is that of relative affine space
(`AlgebraicGeometry.Etale.isIso_unit_tateObjectShift_affineSpace`). -/
theorem isIso_unit_tateObjectShift [HasInvertibleExponent Λ T] (m : ℤ) :
    IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π).unit.app
      ((tateObject Λ T m)⟦2 * m⟧)) := by
  refine isIso_of_isIso_leftDerivedUpperStar_map_of_jointlySurjective Λ (fun i ↦ (E.U i).ι)
    (fun x ↦ ?_) _ fun i ↦ ?_
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (E.iSup_U.ge (Set.mem_univ x))
    exact ⟨i, ⟨x, hi⟩, rfl⟩
  have : HasInvertibleExponent Λ (E.U i) := .of_hom (E.U i).ι
  rw [NatIso.isIso_map_iff (leftDerivedUpperStarIsoMapDerivedCategory _ (E.U i).ι)]
  refine isIso_upperStar_map_unit_of_isPullback Λ (isPullback_morphismRestrict π (E.U i)) _ ?_
  rw [← E.chart_over i]
  refine isIso_unit_app_comp_of_isIso Λ (E.chart i).hom _ _ ?_
  refine isIso_unit_app_of_iso _
    (((leftDerivedUpperStarIsoMapDerivedCategory _ (E.U i).ι).app _).symm ≪≫
      leftDerivedUpperStarTateShiftIso Λ (E.U i).ι m) ?_
  exact isIso_unit_tateObjectShift_affineSpace Λ r (E.U i) ((E.U i).ι ≫ aT) m

include aT in
/-- *Restriction along sections of a vector bundle does not depend on the section*: for two
sections `s, s'` of `π : V ⟶ T`, `s^* c = s'^* c` in `H^{2r}(T, Λ(r))`, by homotopy invariance
(`AlgebraicGeometry.VectorBundle.isIso_unit_tateObjectShift`,
`AlgebraicGeometry.VectorBundle.classRestriction_section_eq_of_isIso_unit`). -/
theorem classRestriction_section_eq (s s' : T ⟶ V) (hs : s ≫ π = 𝟙 T) (hs' : s' ≫ π = 𝟙 T)
    (c : constantComplex Λ V ⟶ (tateObject Λ V r)⟦2 * (r : ℤ)⟧) :
    haveI : HasInvertibleExponent Λ T := .of_hom E.zero
    classRestriction Λ s c = classRestriction Λ s' c :=
  haveI : HasInvertibleExponent Λ T := .of_hom E.zero
  classRestriction_section_eq_of_isIso_unit Λ s s' hs hs' (E.isIso_unit_tateObjectShift Λ aT r) c

/-- Blueprint `thm-pur-localized-top-chern`: Localized top Chern class

*(L4).* After forgetting supports, the localized top Chern class of any section `s` is the top
Chern class: `c_r(V, s) ↦ c_r(V)` in `H^{2r}(T, Λ(r))`. Both are restrictions of the Thom class
with supports forgotten (`AlgebraicGeometry.VectorBundle.localizedTopChernForget_eq`), along `s`
and along the zero section, and restriction along a section does not depend on the section
(`AlgebraicGeometry.VectorBundle.classRestriction_section_eq`, homotopy invariance). -/
theorem forgetSupports_localizedTopChern (s : T ⟶ V) (hs : s ≫ π = 𝟙 T) :
    E.localizedTopChernForget Λ aT s = E.topChernClass Λ aT := by
  rw [topChernClass, localizedTopChernForget_eq, localizedTopChernForget_eq]
  exact E.classRestriction_section_eq Λ aT s E.zero hs E.zero_comp _

/-- Blueprint `lem-pur-divisor-class`: Divisor classes

*(b), the comparison with `c₁(𝒪(D))`.* For a line bundle `L` (a vector bundle of rank one) and a
section `s` with zero scheme `D = Z(s)`, the Kummer class `cl(D) = c₁(L, s)` of the divisor,
supports forgotten, is the first Chern class `c₁(L)`; the comparison does not depend on the
section. This is the case `r = 1` of (L4) of `thm-pur-localized-top-chern`
(`AlgebraicGeometry.VectorBundle.forgetSupports_localizedTopChern`). -/
theorem forgetSupports_localizedTopChern_one {π₁ : V ⟶ T} (L : VectorBundle 1 π₁) (s : T ⟶ V)
    (hs : s ≫ π₁ = 𝟙 T) :
    L.localizedTopChernForget Λ aT s = L.topChernClass Λ aT :=
  L.forgetSupports_localizedTopChern Λ aT s hs

end VectorBundle

end AlgebraicGeometry
