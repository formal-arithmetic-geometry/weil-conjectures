/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.PointOfDerivation
import Sheaf.AlgebraicGeometry.GroupScheme.DiagonalTangentAddition

/-!
# The infinitesimal points of a group scheme are its Lie algebra

The bridge from infinitesimal points to the Lie algebra is a bijection
(`AlgebraicGeometry.GrpObj.toLie_bijective`), turning the group law into the addition
(`AlgebraicGeometry.GrpObj.lieEquiv`).
-/

@[expose] public section

universe u

open CategoryTheory TrivSqZeroExt
open scoped MonObj

namespace AlgebraicGeometry
section InfPoints

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

namespace GrpObj

omit [GrpObj G] in
/-- A derivation `𝒪_G → g_*𝒪_S` is a morphism `g^*Ω¹_{G/S} ⟶ 𝒪_S`. -/
theorem homOfDerivation_bijective (g : S ⟶ G.left) :
    Function.Bijective (homOfDerivation G g) := by
  refine (Equiv.bijective _).comp ((Equiv.bijective _).comp ⟨fun D₁ D₂ h ↦ ?_, fun φ ↦ ?_⟩)
  · rw [← (PresheafOfModules.DifferentialsConstruction.isUniversal' _).fac D₁,
      ← (PresheafOfModules.DifferentialsConstruction.isUniversal' _).fac D₂]
    exact congrArg _ h
  · refine ⟨(PresheafOfModules.DifferentialsConstruction.derivation' _).postcomp φ, ?_⟩
    apply (PresheafOfModules.DifferentialsConstruction.isUniversal' _).postcomp_injective
    rw [PresheafOfModules.Derivation.Universal.fac]

/-- The morphisms `ω_{G/S} ⟶ 𝒪_S` attached to derivations along two morphisms `g₁ = g₂ = e` agree
only if the derivations do. -/
theorem heq_of_pullbackCongr_inv_comp_homOfDerivation_eq {g₁ g₂ : S ⟶ G.left}
    (h₁ : g₁ = unitSection G) (h₂ : g₂ = unitSection G)
    (D₁ : ((Scheme.Modules.pushforward g₁).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom)
    (D₂ : ((Scheme.Modules.pushforward g₂).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom)
    (h : (Scheme.Modules.pullbackCongr h₁).inv.app G.hom.cotangentSheaf ≫
        homOfDerivation G g₁ D₁ =
      (Scheme.Modules.pullbackCongr h₂).inv.app G.hom.cotangentSheaf ≫
        homOfDerivation G g₂ D₂) {V : (TopologicalSpace.Opens G.left)ᵒᵖ}
    (a : Γ(G.left, V.unop)) : D₁.d a ≍ D₂.d a := by
  subst h₁ h₂
  obtain rfl := (homOfDerivation_bijective G _).1 ((cancel_epi _).1 h)
  rfl

/-- The bridge is a bijection: a morphism `ω_{G/S} ⟶ 𝒪_S` is a derivation `d : 𝒪_G → e_*𝒪_S`, and
`a ↦ e^♯(a) + ε d(a)` is a morphism of schemes `S[ε] ⟶ G` over `S` reducing to the identity, since
its stalk maps are local, their reductions modulo `ε` being the local maps `e^♯`. -/
theorem toLie_bijective : Function.Bijective (toLie G) := by
  refine ⟨fun v w h ↦ ?_, fun φ ↦ ?_⟩
  · apply Subtype.ext
    apply Over.OverMorphism.ext
    rw [← pointOfDerivation_infDerivation G v.1, ← pointOfDerivation_infDerivation G w.1]
    exact pointOfDerivation_congr G
      ((ι_comp_left_eq G v.2).trans (ι_comp_left_eq G w.2).symm)
      (heq_of_pullbackCongr_inv_comp_homOfDerivation_eq G _ _ _ _ h)
  · obtain ⟨D, hD⟩ := (homOfDerivation_bijective G (unitSection G)).2
      ((Scheme.Modules.pullbackCongr (rfl : unitSection G = unitSection G)).hom.app
        G.hom.cotangentSheaf ≫ φ)
    -- Keep `v` opaque, which stops the kernel from unfolding it. (`generalize` would do the same,
    -- but it cannot elaborate the `Over.homMk` without an expected type.)
    obtain ⟨v, hvdef⟩ : ∃ v : Scheme.dualNumbersOver S ⟶ G,
        v = Over.homMk (pointOfDerivation G (unitSection G) D)
          (pointOfDerivation_comp_hom G _ D (unitSection_comp_hom G)) := ⟨_, rfl⟩
    have hv : v ∈ infPoints G := by
      subst hvdef
      rw [mem_infPoints]
      apply Over.OverMorphism.ext
      exact (ι_comp_pointOfDerivation G _ D).trans (one_left G).symm
    refine ⟨⟨v, hv⟩, ?_⟩
    rw [toLie, omegaHom_eq_homOfDerivation, pullbackCongr_inv_comp_homOfDerivation G
      (ι_comp_left_eq G hv) rfl _ D (fun a ↦ by
        subst hvdef
        exact heq_of_eq (zero_add _)), hD,
      Iso.inv_hom_id_app_assoc]

/-- The infinitesimal points of `G` are its Lie algebra. (blueprint: `sk-d-tangent`) -/
noncomputable def lieEquiv : infPoints G ≃ Lie G :=
  Equiv.ofBijective _ (toLie_bijective G)

private theorem transportedOmegaHom_congr
    {v w : Scheme.dualNumbersOver S ⟶ G} (e : v = w)
    (hv : S.dualNumbersι ≫ v.left = unitSection G)
    (hw : S.dualNumbersι ≫ w.left = unitSection G) :
    (Scheme.Modules.pullbackCongr hv).inv.app G.hom.cotangentSheaf ≫ omegaHom G v =
      (Scheme.Modules.pullbackCongr hw).inv.app G.hom.cotangentSheaf ≫ omegaHom G w := by
  subst w
  rfl

/-- The bridge turns the group law of the infinitesimal points into the addition of `Lie(G)`. -/
theorem lieEquiv_mul (v w : infPoints G) : lieEquiv G (v * w) = lieEquiv G v + lieEquiv G w := by
  open MonoidalCategory CartesianMonoidalCategory in
  let f := lift (fst _ _ ≫ v.1) (snd _ _ ≫ w.1) ≫ μ[G]
  open MonoidalCategory CartesianMonoidalCategory in
  have hd : lift (𝟙 (Scheme.dualNumbersOver S)) (𝟙 (Scheme.dualNumbersOver S)) ≫ f =
      (v * w).1 := by
    simp only [f, ← Category.assoc, comp_lift, lift_fst, lift_snd, Category.id_comp]
    rfl
  open MonoidalCategory CartesianMonoidalCategory in
  have h₁ : lift (𝟙 (Scheme.dualNumbersOver S))
      (toUnit (Scheme.dualNumbersOver S) ≫ Scheme.dualNumbersιOver S) ≫ f = v.1 := by
    simp only [f, ← Category.assoc, comp_lift, lift_fst, lift_snd]
    simp only [Category.assoc, (mem_infPoints G).mp w.2]
    simp [← Hom.mul_def, MonObj.comp_one]
  open MonoidalCategory CartesianMonoidalCategory in
  have h₂ : lift (toUnit (Scheme.dualNumbersOver S) ≫ Scheme.dualNumbersιOver S)
      (𝟙 (Scheme.dualNumbersOver S)) ≫ f = w.1 := by
    simp only [f, ← Category.assoc, comp_lift, lift_fst, lift_snd]
    simp only [Category.assoc, (mem_infPoints G).mp v.2]
    simp [← Hom.mul_def, MonObj.comp_one]
  have h := omegaHom_diagonal_add G f (unitSection G)
    (by rw [hd]; exact ι_comp_left_eq G (v * w).2)
    (by rw [h₁]; exact ι_comp_left_eq G v.2)
    (by rw [h₂]; exact ι_comp_left_eq G w.2)
  change toLie G (v * w) = toLie G v + toLie G w
  calc
    _ = _ := (transportedOmegaHom_congr G hd _ _).symm
    _ = _ := h
    _ = _ := congrArg₂ (· + ·) (transportedOmegaHom_congr G h₁ _ _)
      (transportedOmegaHom_congr G h₂ _ _)

theorem lieEquiv_one : lieEquiv G 1 = 0 := by
  have h := lieEquiv_mul G (1 : infPoints G) 1
  rw [one_mul] at h
  exact (add_left_cancel (show lieEquiv G 1 + lieEquiv G 1 = lieEquiv G 1 + 0 by
    rw [add_zero]
    exact h.symm))

theorem lieEquiv_symm_add (x y : Lie G) :
    (lieEquiv G).symm (x + y) = (lieEquiv G).symm x * (lieEquiv G).symm y :=
  (lieEquiv G).injective (by simp [lieEquiv_mul])

end GrpObj

end InfPoints

end AlgebraicGeometry
