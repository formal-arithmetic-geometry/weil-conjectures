/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpaceTrace
public import WeilConjectures.EtaleCohomology.Purity.Smooth.VectorBundlePurity
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange

/-!
# The Thom isomorphism for the compactly supported direct image of a vector bundle

Let `π : V ⟶ S` be a vector bundle with zero section `z` (`AlgebraicGeometry.VectorBundle`).

* **The trace is an isomorphism.** The counit `Rπ_! Rπ^! Λ_S ⟶ Λ_S` is an isomorphism
  (`AlgebraicGeometry.VectorBundle.isIso_counit_constantComplex`). It has a section: as
  `z ≫ π = 𝟙`, the counit of the composite adjunction `Rπ_! Rz_! ⊣ Rz^! Rπ^!` is invertible, and
  it factors through it. On every chart `π⁻¹ U ≅ 𝔸^d_U` the source is isomorphic to `Λ_U`
  (`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_twistShift_affineSpace`), and an
  endomorphism of the unit with a one-sided inverse is invertible, endomorphisms of the unit of a
  monoidal category commuting with each other.
* **The rank-one Thom isomorphism** (`thm-pur-rank-one-thom`). For a line bundle, with the Thom
  class `thom(E) : z_* Λ_S ⟶ Λ_V(1)[2]` (the class of the zero divisor), `τ_E = Rπ_! thom(E)` is
  an isomorphism (`AlgebraicGeometry.VectorBundle.isIso_rightDerivedLowerShriek_map_thom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace CategoryTheory.MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- Endomorphisms of the unit of a monoidal category commute (Eckmann–Hilton). -/
lemma endUnit_comm (f g : 𝟙_ C ⟶ 𝟙_ C) : f ≫ g = g ≫ f := by
  have h := whisker_exchange f g
  have hf : f ▷ 𝟙_ C = (ρ_ (𝟙_ C)).hom ≫ f ≫ (ρ_ (𝟙_ C)).inv := by
    rw [← Category.assoc, ← rightUnitor_naturality, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hg : 𝟙_ C ◁ g = (λ_ (𝟙_ C)).hom ≫ g ≫ (λ_ (𝟙_ C)).inv := by
    rw [← Category.assoc, ← leftUnitor_naturality, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [unitors_equal] at hg
  rw [hf, hg] at h
  simp only [Category.assoc, Iso.inv_hom_id_assoc, cancel_epi] at h
  rw [← Category.assoc, ← Category.assoc, cancel_mono] at h
  exact h.symm

/-- A morphism `r : T ⟶ N` with a right inverse `s`, between objects isomorphic to the unit, is an
isomorphism. -/
lemma isIso_of_comp_eq_id_of_iso_unit {N T : C} (e : N ≅ 𝟙_ C) (φ : T ≅ N) (s : N ⟶ T)
    (r : T ⟶ N) (h : s ≫ r = 𝟙 N) : IsIso r := by
  have hxy := endUnit_comm (e.inv ≫ s ≫ φ.hom ≫ e.hom) (e.inv ≫ φ.inv ≫ r ≫ e.hom)
  have h₁ : (e.inv ≫ s ≫ φ.hom ≫ e.hom) ≫ (e.inv ≫ φ.inv ≫ r ≫ e.hom) = 𝟙 _ := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, reassoc_of% h, Iso.inv_hom_id]
  rw [h₁] at hxy
  have h₂ : r ≫ s = 𝟙 T := by
    have := congrArg (fun ψ ↦ φ.hom ≫ e.hom ≫ ψ ≫ e.inv ≫ φ.inv) hxy
    simpa using this.symm
  exact ⟨s, h₂, h⟩

end CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.VectorBundle

open Scheme Etale

variable {V S : Scheme.{u}} {d : ℕ} {π : V ⟶ S} (E : VectorBundle d π)

section Trace

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasInvertibleExponent Λ S]
  [HasCompactification π] [QuasiCompact π]

/-- The counit of the composite adjunction `Rπ_! Rz_! ⊣ Rz^! Rπ^!` is an isomorphism, the left
adjoint being `R(z ≫ π)_! = R(𝟙)_! ≅ 𝟭`. -/
theorem isIso_comp_counit :
    IsIso ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) E.zero).comp
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) π)).counit := by
  have := E.isClosedImmersion_zero
  have : HasCompactification (E.zero ≫ π) := .of_eq E.zero_comp.symm
  obtain ⟨c⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ E.zero π
  obtain ⟨heq⟩ := nonempty_iso_rightDerivedLowerShriek_of_eq Λ E.zero_comp
  obtain ⟨eid⟩ := nonempty_leftDerivedUpperStar_id_iso Λ S (𝟙 S) rfl
  let eL : R(E.zero)_![ModuleCat.{u + 1} Λ] ⋙ R(π)_![ModuleCat.{u + 1} Λ] ≅ 𝟭 _ :=
    c.symm ≪≫ heq ≪≫
      rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) (𝟙 S) ≪≫
      rightDerivedLowerStarIsoLeftDerivedUpperStarInv (ModuleCat.{u + 1} Λ) (Iso.refl S) ≪≫ eid
  let adj := (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) E.zero).comp
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) π)
  let rU := adj.rightAdjointUniq (Adjunction.id.ofNatIsoLeft eL.symm)
  exact adj.isIso_counit_of_iso (Functor.isoWhiskerRight rU _ ≪≫ Functor.leftUnitor _ ≪≫ eL)

end Trace

section Thom

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] [HasInvertibleExponent Λ V] [HasCompactification π]
  [QuasiCompact π] {k : Type u} [Field k] (aS : S ⟶ Spec (.of k)) [IsSeparated aS]
  [LocallyOfFiniteType aS]

attribute [local instance] HasInvertibleExponent.opens

include aS in
/-- Over a chart `U`, the restriction of `Rπ_! Rπ^! Λ_S` is isomorphic to `Λ_U`: by
`ω_π ≅ Λ_V(d)[2d]`, base change to `U` and the chart `π⁻¹ U ≅ 𝔸^d_U`, it is
`Rp_! Λ(d)[2d] ≅ Λ_U` for `p : 𝔸^d_U ⟶ U`. -/
theorem nonempty_iso_leftDerivedUpperStar_rightDerivedLowerShriek_dualizingComplex (i : E.ι) :
    have : HasInvertibleExponent Λ S := .of_hom E.zero
    Nonempty ((L(((E.U i).ι)^*[ModuleCat.{u + 1} Λ])).obj ((R(π)_![ModuleCat.{u + 1} Λ]).obj
        ((R(π)^![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ S))) ≅
      (L(((E.U i).ι)^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ S)) := by
  intro this
  obtain ⟨ω⟩ := E.nonempty_iso_dualizingComplex Λ aS
  have := E.isAffineHom_morphismRestrict i
  have : HasCompactification ((E.chart i).hom ≫ 𝔸(ULift.{u} (Fin d); E.U i) ↘ E.U i) :=
    HasCompactification.comp_of_isOpenImmersion _ (E.chart i).hom
  have : HasCompactification (π ∣_ E.U i) := .of_eq (E.chart_over i)
  have : HasCompactification (E.chart i).hom :=
    (Compactification.ofIsOpenImmersion (E.chart i).hom).hasCompactification
  have hbc := isIso_rightDerivedLowerShriekBaseChangeMap Λ
    (isPullback_morphismRestrict π (E.U i)).flip
  obtain ⟨heq⟩ := nonempty_iso_rightDerivedLowerShriek_of_eq Λ (E.chart_over i).symm
  obtain ⟨c⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ (E.chart i).hom
    (𝔸(ULift.{u} (Fin d); E.U i) ↘ E.U i)
  obtain ⟨t₀⟩ := nonempty_iso_rightDerivedLowerShriek_twistShift_of_iso Λ (E.chart i) d
  obtain ⟨t₁⟩ := nonempty_iso_rightDerivedLowerShriek_twistShift_affineSpace_fin Λ d (E.U i)
  exact ⟨(L(((E.U i).ι)^*[ModuleCat.{u + 1} Λ])).mapIso
      ((R(π)_![ModuleCat.{u + 1} Λ]).mapIso ω) ≪≫
    (asIso (rightDerivedLowerShriekBaseChangeMap Λ
      (isPullback_morphismRestrict π (E.U i)).flip)).app _ ≪≫
    (R(π ∣_ E.U i)_![ModuleCat.{u + 1} Λ]).mapIso
      (leftDerivedUpperStarTateShiftIso Λ (π ⁻¹ᵁ E.U i).ι d ≪≫
        (twistShiftConstantComplexIso Λ _ d).symm) ≪≫
    heq.app _ ≪≫ c.app _ ≪≫ (R(𝔸(ULift.{u} (Fin d); E.U i) ↘ E.U i)_![ModuleCat.{u + 1} Λ]).mapIso t₀ ≪≫
    t₁ ≪≫ (leftDerivedUpperStarConstantComplexIso Λ (E.U i).ι).symm⟩

include aS in
/-- The trace `Rπ_! Rπ^! Λ_S ⟶ Λ_S` of a vector bundle, the counit of `Rπ_! ⊣ Rπ^!`, is an
isomorphism. -/
theorem isIso_counit_constantComplex :
    have : HasInvertibleExponent Λ S := .of_hom E.zero
    IsIso ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) π).counit.app
      (constantComplex Λ S)) := by
  intro this
  have hc := E.isIso_comp_counit Λ
  have hcomp := Adjunction.comp_counit_app
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) E.zero)
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) π) (constantComplex Λ S)
  have hs : (inv (((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) E.zero).comp
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) π)).counit.app
        (constantComplex Λ S)) ≫ (R(π)_![ModuleCat.{u + 1} Λ]).map
          ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) E.zero).counit.app
            ((R(π)^![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ S)))) ≫
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) π).counit.app
        (constantComplex Λ S) = 𝟙 _ := by
    rw [Category.assoc, ← hcomp, IsIso.inv_hom_id]
  refine isIso_of_isIso_leftDerivedUpperStar_map_of_jointlySurjective Λ (fun i ↦ (E.U i).ι)
    (fun s ↦ ?_) _ fun i ↦ ?_
  · have hs : s ∈ iSup E.U := by rw [E.iSup_U]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hs
    exact ⟨i, ⟨s, hi⟩, rfl⟩
  · obtain ⟨φ⟩ := E.nonempty_iso_leftDerivedUpperStar_rightDerivedLowerShriek_dualizingComplex
      Λ aS i
    exact MonoidalCategory.isIso_of_comp_eq_id_of_iso_unit
      (leftDerivedUpperStarConstantComplexIso Λ (E.U i).ι) φ _ _
      (by rw [← Functor.map_comp, hs]; exact CategoryTheory.Functor.map_id _ _)

include aS in
/-- `Rπ_!` of the forget-supports map `Rz_! Λ_S ≅ Rz_! Rz^! Λ_V(d)[2d] ⟶ Λ_V(d)[2d]` of the Thom
class is an isomorphism `Λ_S ≅ Rπ_! Rz_! Λ_S ⟶ Rπ_! Λ_V(d)[2d]`. -/
theorem isIso_rightDerivedLowerShriek_map_thomClass :
    IsIso ((R(π)_![ModuleCat.{u + 1} Λ]).map
      ((R(E.zero)_![ModuleCat.{u + 1} Λ]).map (E.thomClassMap Λ aS) ≫
        (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) E.zero).counit.app
          (thomCoefficients Λ (d := d)))) := by
  have : HasInvertibleExponent Λ S := .of_hom E.zero
  have := E.isIso_thomClassMap Λ aS
  have hA := E.isIso_counit_constantComplex Λ aS
  have hc := E.isIso_comp_counit Λ
  have hc₁ : IsIso (((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) E.zero).comp
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) π)).counit.app
        (constantComplex Λ S)) := inferInstance
  rw [Adjunction.comp_counit_app] at hc₁
  have h₁ := (isIso_comp_right_iff _ _).1 hc₁
  obtain ⟨ω⟩ := E.nonempty_iso_dualizingComplex Λ aS
  have hn := (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) E.zero).counit.naturality
    ω.inv
  have hε : (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) E.zero).counit.app
      (thomCoefficients Λ (d := d)) =
      (R(E.zero)_![ModuleCat.{u + 1} Λ]).map ((R(E.zero)^![ModuleCat.{u + 1} Λ]).map ω.inv) ≫
        (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) E.zero).counit.app
          (dualizingComplex (ModuleCat.{u + 1} Λ) π) ≫ ω.hom := by
    erw [reassoc_of% hn]
    simp
  have h₂ : IsIso ((R(π)_![ModuleCat.{u + 1} Λ]).map
      ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) E.zero).counit.app
        (dualizingComplex (ModuleCat.{u + 1} Λ) π))) := h₁
  rw [hε, Functor.map_comp, Functor.map_comp, Functor.map_comp]
  infer_instance

include aS in
/-- Blueprint `thm-pur-rank-one-thom`: Rank-one Thom isomorphism

Let `π : E ⟶ B` be a vector bundle of rank one (a line bundle) with zero section `z`, over a
scheme separated and locally of finite type over a field on which the exponent of `Λ` is
invertible. Let `thom(E) : z_* Λ_B ⟶ Λ_E(1)[2]` be the class of the zero divisor: the Thom class
of `E` (`AlgebraicGeometry.VectorBundle.thomClass`, restricting on every chart to the Kummer
boundary `∂κ(t)` of the coordinate, the class of `lem-pur-divisor-class`) with supports forgotten,
`Rz_! Λ_B ≅ Rz_! Rz^! Λ_E(1)[2] ⟶ Λ_E(1)[2]`. Then

`τ_E = Rπ_! thom(E) : Λ_B = Rπ_! Rz_! Λ_B ⟶ Rπ_! Λ_E(1)[2]`

is an isomorphism; in particular `Rπ_! Λ_E ≅ Λ_B(-1)[-2]`. Here `Rπ_! Rz_! Λ_B` is identified
with `Λ_B` through `R(z ≫ π)_! = R(𝟙)_!`. The compatibility with base change of the blueprint is
not stated. -/
theorem isIso_rightDerivedLowerShriek_map_thom (E : VectorBundle 1 π) :
    IsIso ((R(π)_![ModuleCat.{u + 1} Λ]).map
      ((R(E.zero)_![ModuleCat.{u + 1} Λ]).map (E.thomClassMap Λ aS) ≫
        (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) E.zero).counit.app
          (thomCoefficients Λ (d := 1)))) :=
  E.isIso_rightDerivedLowerShriek_map_thomClass Λ aS

end Thom

end AlgebraicGeometry.VectorBundle

end
