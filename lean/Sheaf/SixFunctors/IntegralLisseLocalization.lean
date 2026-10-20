/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.SixFunctors.IntegralLisseReductionData
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.EpiMono

/-!
# The canonical localization cocone

Source: Bhatt--Scholze, Lemma 6.8.2(2), p. 59.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

private def fractionCoconeIsColimit
    {D : ℕ ⥤ Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}}
    (c : Cocone D) [∀ n, Mono (c.ι.app n)]
    (h : ∀ (V : X.ProEt) (s : c.pt.obj.obj (op V)),
      ∃ R ∈ Scheme.ProEt.topology X V,
        ∀ ⦃W : X.ProEt⦄ (g : W ⟶ V), R g →
          ∃ (n : ℕ) (t : (D.obj n).obj.obj (op W)),
            (c.ι.app n).hom.app (op W) t = c.pt.obj.map g.op s) :
    IsColimit c := by
  have : AB5OfSize.{0, 0} (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) :=
    AB5OfSize_shrink.{0, 0, u + 1, u + 1} _
  let φ := colimit.desc D c
  have hmono : Mono φ := by
    let α : D ⟶ (Functor.const _).obj c.pt := { app n := c.ι.app n }
    have : Mono α := NatTrans.mono_of_mono_app _
    have : Mono (colim.map α) := inferInstance
    let e := (colimit.isColimit ((Functor.const ℕ).obj c.pt)).coconePointUniqueUpToIso
      (isColimitConstCocone ℕ c.pt)
    have : φ = colim.map α ≫ e.hom := by
      refine colimit.hom_ext fun n ↦ ?_
      simp [φ, e, α]
    rw [this]
    infer_instance
  have hepi : Epi φ := by
    have : Sheaf.IsLocallySurjective φ := by
      refine ⟨fun {V} s ↦ ?_⟩
      obtain ⟨R, hR, hRs⟩ := h V s
      refine (Scheme.ProEt.topology X).superset_covering ?_ hR
      intro W g hg
      obtain ⟨n, t, ht⟩ := hRs g hg
      refine ⟨(colimit.ι D n).hom.app (op W) t, ?_⟩
      rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
        ← ObjectProperty.FullSubcategory.comp_hom, colimit.ι_desc]
      exact ht
    exact Sheaf.epi_of_isLocallySurjective _
  have : IsIso ((colimit.isColimit D).desc c) := isIso_of_mono_of_epi φ
  exact IsColimit.ofPointIso (colimit.isColimit D)

/-- The module in which the fractions take their values. -/
abbrev integralLisseLocalizedUnit :=
  (SheafOfModules.restrictScalars
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (lisseIntegerToFieldSized l E X))).obj
    (SheafOfModules.unit ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (lisseFieldSheafSized l E X)))

/-- Adjacent fractions give a cocone for multiplication by the prime. -/
theorem integralLisseFraction_compatible (n : ℕ) :
    integralLisseScalar l E X (SheafOfModules.unit (integralLisseRing l E X))
        (l : Padic.coefficientExtensionIntegers l E) ≫
      integralLisseFraction l E X (n + 1) = integralLisseFraction l E X n := by
  let := spectralNorm.normedField ℚ_[l] E
  have : CharZero E := Algebra.charZero_of_charZero ℚ_[l] E
  have hl : (l : E) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  apply (SheafOfModules.unitHomEquiv _).injective
  apply Subtype.ext
  funext U
  apply ULift.ext
  apply ContinuousMap.ext
  intro y
  change ((l : E) * (1 : E)) * ((l : E)⁻¹ ^ (n + 1)) =
    (1 : E) * ((l : E)⁻¹ ^ n)
  rw [pow_succ]
  field_simp

/-- The fraction cocone has the rational coefficient unit as its actual point. -/
def integralLisseLocalizationCocone :
    Cocone (Functor.ofSequence (fun _ : ℕ ↦
      integralLisseScalar l E X (SheafOfModules.unit (integralLisseRing l E X))
        (l : Padic.coefficientExtensionIntegers l E))) where
  pt := integralLisseLocalizedUnit l E X
  ι := NatTrans.ofSequence (integralLisseFraction l E X) (fun n ↦ by
    simpa using integralLisseFraction_compatible l E X n)

/-- The fractions are colimiting in the sheaf module category.

Source: Bhatt--Scholze, Lemma 6.8.2(2), p. 59.
(blueprint: lem-sfb-integral-lisse-localization-colimit)

Proof: for a continuous field-valued function f, the inverse images of the open
sets l^(-m) A cover its domain. On the m-th member f is represented by the
integral function l^m f at the m-th stage. These local fractions agree after
passing to a common higher stage. A cocone from the multiplication diagram
therefore defines a unique map from the field coefficient unit, by gluing its
values on these representatives. Independence follows because A embeds in E
and l is nonzero, so two equal fractions become equal integral functions at a
common stage. This also proves additivity and integral linearity, checked on
common refinements, and compatibility with restriction. Applying the cocone
identities to integral fractions gives the factorization property. Every section
is locally a fraction, so sheaf uniqueness proves uniqueness of the factorization.
The construction includes empty objects. -/
theorem integralLisseLocalization_isColimit :
    Nonempty (IsColimit (integralLisseLocalizationCocone l E X)) := by
  classical
  let := spectralNorm.normedField ℚ_[l] E
  let := spectralNorm.normedAlgebra ℚ_[l] E
  have : CharZero E := Algebra.charZero_of_charZero ℚ_[l] E
  have hl : (l : E) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  have hnorm : ‖(l : E)‖ < 1 := by
    have h : ‖(l : E)‖ = ‖(l : ℚ_[l])‖ := by
      simpa only [map_natCast] using (norm_algebraMap' E (l : ℚ_[l]))
    rw [h]
    exact Padic.norm_p_lt_one
  let A := Padic.coefficientExtensionIntegers l E
  have hA (a : E) : a ∈ A ↔ ‖a‖ ≤ 1 :=
    (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
      (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec.1 a
  let F := SheafOfModules.toSheaf (integralLisseRing l E X)
  let c := F.mapCocone (integralLisseLocalizationCocone l E X)
  have happ (n : ℕ) (U : X.ProEtᵒᵖ)
      (s : ((SheafOfModules.unit (integralLisseRing l E X)).val.obj U))
      (x : U.unop.left) :
      (((integralLisseFraction l E X n).val.app U) s).down x =
        (s.down x : E) * ((l : E)⁻¹ ^ n) := rfl
  have hmono : ∀ n, Mono (c.ι.app n) := by
    intro n
    apply Sheaf.mono_of_injective
    intro U s t hst
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    have h := congrArg (fun z ↦ z.down x) hst
    change _ * ((l : E)⁻¹ ^ n) = _ * ((l : E)⁻¹ ^ n) at h
    exact mul_right_cancel₀ (pow_ne_zero n (inv_ne_zero hl)) h
  let : ∀ n, Mono (c.ι.app n) := hmono
  have hc : IsColimit c := by
    apply fractionCoconeIsColimit X c
    intro W s
    let f : C(W.left, E) := s.down
    have hn (x : W.left) : ∃ n : ℕ, ‖f x‖ * ‖(l : E)‖ ^ n < 1 := by
      have hb : 0 < ‖f x‖ + 1 := by positivity
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hb) hnorm
      refine ⟨n, ?_⟩
      calc
        ‖f x‖ * ‖(l : E)‖ ^ n ≤ (‖f x‖ + 1) * ‖(l : E)‖ ^ n :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ < (‖f x‖ + 1) * (‖f x‖ + 1)⁻¹ := mul_lt_mul_of_pos_left hn hb
        _ = 1 := mul_inv_cancel₀ hb.ne'
    let n (x : W.left) := (hn x).choose
    let V (x : W.left) : W.left.Opens :=
      ⟨{y | ‖f y‖ * ‖(l : E)‖ ^ n x < 1},
        isOpen_lt (f.continuous.norm.mul continuous_const) continuous_const⟩
    refine ⟨?_, ?_, ?_⟩
    · exact ⨆ n, Presheaf.imageSieve (c.ι.app n).hom s
    · apply Scheme.ProEt.mem_topology_of_openImmersion _ (fun x ↦ (V x).ι)
      · intro x
        exact ⟨x, ⟨⟨x, (hn x).choose_spec⟩, rfl⟩⟩
      · intro x
        let a : C((V x).toScheme, A) :=
          ⟨fun y ↦ ⟨f y.val * (l : E) ^ n x, (hA _).mpr (by
              rw [norm_mul, norm_pow]
              exact y.property.le)⟩,
            ((f.continuous.comp (V x).ι.continuous).mul continuous_const).subtype_mk _⟩
        apply le_iSup (fun n ↦ Presheaf.imageSieve (c.ι.app n).hom s) (n x)
        refine ⟨ULift.up a, ?_⟩
        apply ULift.ext
        apply ContinuousMap.ext
        intro y
        change (f y.val * (l : E) ^ n x) * ((l : E)⁻¹ ^ n x) = f y.val
        rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hl, one_pow, mul_one]
    · intro W' g hg
      simp only [iSup, Sieve.sSup_apply, Set.mem_range] at hg
      obtain ⟨S, ⟨n, rfl⟩, t, ht⟩ := hg
      exact ⟨n, t, ht⟩
  have : ReflectsColimitsOfShape ℕ F := reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact ⟨isColimitOfReflects F hc⟩

end AlgebraicGeometry.ProEtale
