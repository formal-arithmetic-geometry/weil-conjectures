/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Mathlib.AlgebraicGeometry.Cover.Open
import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! Local ingredients for topological invariance of the small pro-etale topos. -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem local_adjunction_isIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {F₁ : A ⥤ C} {U₁ : C ⥤ A} {F₂ : B ⥤ D} {U₂ : D ⥤ B}
    (ai : L₁ ⊣ R₁) (ai' : L₂ ⊣ R₂) (aj : F₁ ⊣ U₁) (aj' : F₂ ⊣ U₂)
    (α : TwoSquare U₂ R₂ R₁ U₁) [IsIso α.natTrans]
    (hb : IsIso (((mateEquiv aj' aj).symm α).natTrans))
    [IsIso ai'.unit] [IsIso ai'.counit] :
    (∀ M, IsIso (F₁.map (ai.unit.app M))) ∧
      (∀ M, IsIso (F₂.map (ai.counit.app M))) := by
  let β := (mateEquiv aj' aj).symm α
  let γ := (mateEquiv ai ai').symm β
  have : IsIso β.natTrans := hb
  have : IsIso γ.natTrans := by
    dsimp [γ, β]
    rw [iterated_mateEquiv_conjugateEquiv_symm ai ai' aj aj']
    change IsIso ((conjugateEquiv (ai.comp aj') (aj.comp ai')).symm α.natTrans)
    infer_instance
  constructor
  · intro M
    have h := unit_mateEquiv_symm ai ai' β M
    change F₁.map (ai.unit.app M) ≫ β.natTrans.app (L₁.obj M) =
      ai'.unit.app (F₁.obj M) ≫ R₂.map (γ.natTrans.app M) at h
    have : IsIso (ai'.unit.app (F₁.obj M) ≫ R₂.map (γ.natTrans.app M)) := inferInstance
    rw [← h] at this
    exact IsIso.of_isIso_comp_right _ (β.app _)
  · intro M
    have h := mateEquiv_counit_symm ai ai' β M
    have : IsIso (L₂.map (β.app M) ≫ ai'.counit.app (F₂.obj M)) := inferInstance
    rw [h] at this
    exact IsIso.of_isIso_comp_left (γ.app _) _

private theorem local_isIso {X Y U : Scheme.{u}} (r : X ⟶ Y) (j : U ⟶ Y)
    [IsOpenImmersion j]
    (h : (proEtaleSheafDirectImage (pullback.snd r j) (Type (u + 1))).IsEquivalence) :
    (∀ F, IsIso ((ProEtale.localizationRestriction (Type (u + 1)) j inferInstance).map
      ((proEtaleSheafAdjunction r (Type (u + 1))).unit.app F))) ∧
    (∀ G, IsIso ((ProEtale.localizationRestriction (Type (u + 1))
      (pullback.fst r j) inferInstance).map
      ((proEtaleSheafAdjunction r (Type (u + 1))).counit.app G))) := by
  let ai := proEtaleSheafAdjunction r (Type (u + 1))
  let ai' := proEtaleSheafAdjunction (pullback.snd r j) (Type (u + 1))
  let aj := ProEtale.localizationRestrictionLowerStarAdjunction (Type (u + 1)) j inferInstance
  let aj' := ProEtale.localizationRestrictionLowerStarAdjunction (Type (u + 1))
    (pullback.fst r j) inferInstance
  let sq := (IsPullback.of_hasPullback r j).flip
  let α := TwoSquare.mk _ _ _ _ (ProEtale.squareLowerStarIso (Type (u + 1)) sq.toCommSq).hom
  let β := (mateEquiv aj' aj).symm α
  have hβ : β.natTrans = ProEtale.localizationRestrictionBaseChangeMap
      (Type (u + 1)) sq.toCommSq := by
    apply (mateEquiv aj' aj).injective
    change (mateEquiv aj' aj) ((mateEquiv aj' aj).symm α) = _
    rw [Equiv.apply_symm_apply]
    exact (ProEtale.mateEquiv_localizationRestrictionBaseChangeMap
      (Type (u + 1)) sq.toCommSq).symm
  have hb : IsIso β.natTrans := by
    rw [hβ]
    exact ProEtale.isIso_localizationRestrictionBaseChangeMap_of_isPullback _ sq
  let : (proEtaleSheafDirectImage (pullback.snd r j) (Type (u + 1))).IsEquivalence := h
  have : (proEtaleSheafInverseImage (pullback.snd r j) (Type (u + 1))).IsEquivalence :=
    ai'.isEquivalence_left_of_isEquivalence_right
  exact local_adjunction_isIso ai ai' aj aj' α hb

/-- Direct-image equivalence can be checked after restriction to an open cover.
Source: Stacks Project, Tag 09AB, final localization argument, and Tag 03CF.
Proof: Identify the pro-etale sites of the opens and their inverse images with the
corresponding slice sites. Slice localization compares each restriction of the global
inverse/direct-image adjunction with the adjunction of the base-changed morphism. These
comparisons respect the specified units and counits, as is seen on sections before
sheafification. By the hypothesis each local direct image is an equivalence, so its
adjunction has invertible unit and counit. Their global components become invertible
after restriction to the given open cover and its pullback. Those families cover the
top of the respective pro-etale sites. The cover-local criterion for isomorphisms of
sheaves therefore makes the global unit and counit invertible. The global adjunction
is consequently an equivalence, in particular its direct image is an equivalence.
The empty cover when the target is empty causes no exception: its pullback source is
empty too, and the cover-local criterion still applies.
(blueprint: lem-trf-proetale-sheaf-equivalence-zariski-local) -/
theorem proEtaleSheafDirectImage_isEquivalence_of_openCover {X Y : Scheme.{u}}
    (r : X ⟶ Y) (U : Y.OpenCover)
    (hU : ∀ i : U.I₀,
      (proEtaleSheafDirectImage (pullback.snd r (U.f i))
        (Type (u + 1))).IsEquivalence) :
    (proEtaleSheafDirectImage r (Type (u + 1))).IsEquivalence := by
  have hu (F : Sheaf (ProEt.topology Y) (Type (u + 1))) :
      IsIso ((proEtaleSheafAdjunction r (Type (u + 1))).unit.app F) := by
    apply ProEtale.isIso_of_isIso_localizationRestriction (Type (u + 1)) _ U.f
    · exact Scheme.zariskiPrecoverage_le_proetalePrecoverage _ U.mem₀
    · intro i
      exact (local_isIso r (U.f i) (hU i)).1 F
  have hc (G : Sheaf (ProEt.topology X) (Type (u + 1))) :
      IsIso ((proEtaleSheafAdjunction r (Type (u + 1))).counit.app G) := by
    let V (i : U.I₀) := pullback r (U.f i)
    let j (i : U.I₀) : V i ⟶ X := pullback.fst r (U.f i)
    have : ∀ i, IsOpenImmersion (j i) := fun i ↦ inferInstance
    have hsurj : ∀ x, ∃ i, x ∈ Set.range (j i).base := by
      intro x
      obtain ⟨y, hy⟩ := U.covers (r.base x)
      obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
      exact ⟨U.idx (r.base x), w, hw⟩
    apply ProEtale.isIso_of_isIso_localizationRestriction (Type (u + 1)) _ j
    · exact Scheme.zariskiPrecoverage_le_proetalePrecoverage _
        ((Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨hsurj, fun i ↦ this i⟩)
    · intro i
      exact (local_isIso r (U.f i) (hU i)).2 G
  have : IsIso (proEtaleSheafAdjunction r (Type (u + 1))).unit :=
    NatIso.isIso_of_isIso_app _
  have : IsIso (proEtaleSheafAdjunction r (Type (u + 1))).counit :=
    NatIso.isIso_of_isIso_app _
  exact (proEtaleSheafAdjunction r (Type (u + 1))).toEquivalence.isEquivalence_inverse

end AlgebraicGeometry.Scheme
