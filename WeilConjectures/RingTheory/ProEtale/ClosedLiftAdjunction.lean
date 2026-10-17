/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.ProEtale.ClosedLift

/-!
# The universal property of the ind-étale closed lift

For an `A`-algebra `C̄`, the lift `H_A(C̄)` of `Algebra.ClosedLift` is the coreflection of `C̄`
into ind-étale `A`-algebras: for every ind-étale `A`-algebra `D`, composition with
`H_A(C̄) ⟶ C̄` is a bijection `Hom_A(D, H_A(C̄)) ≃ Hom_A(D, C̄)`
(`Algebra.ClosedLift.homEquiv`). When `C̄` is an `A ⧸ I`-algebra the target is
`Hom_{A ⧸ I}(D ⧸ I D, C̄)` (`Algebra.ClosedLift.homEquivReduction`, blueprint
`lem-exc-closed-lift-adjunction`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace Algebra.ClosedLift

variable {A : Type u} [CommRing A] {C : Type u} [CommRing C] [Algebra A C]

/-- Two maps from an étale `A`-algebra to `H_A(C̄)` with the same image in `C̄` agree: both
factor through stages of the filtered colimit, which a further stage equalizes. -/
theorem algHom_ext_of_etale {D : Type u} [CommRing D] [Algebra A D] [Algebra.Etale A D]
    {ψ₁ ψ₂ : D →ₐ[A] ClosedLift A C}
    (h : (toAlgHom A C).comp ψ₁ = (toAlgHom A C).comp ψ₂) : ψ₁ = ψ₂ := by
  have hfp : IsFinitelyPresentable.{u} (CommAlgCat.of A D) :=
    CommAlgCat.finitePresentation_le_isFinitelyPresentable A _
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  obtain ⟨X₁, φ₁, hφ₁⟩ := IsFinitelyPresentable.exists_hom_of_isColimit
    (colimit.isColimit (diagram A C)) (CommAlgCat.ofHom ψ₁)
  obtain ⟨X₂, φ₂, hφ₂⟩ := IsFinitelyPresentable.exists_hom_of_isColimit
    (colimit.isColimit (diagram A C)) (CommAlgCat.ofHom ψ₂)
  have h₁ : ∀ d, ι X₁ (φ₁.hom d) = ψ₁ d := fun d ↦ congrArg (fun g ↦ CommAlgCat.Hom.hom g d) hφ₁
  have h₂ : ∀ d, ι X₂ (φ₂.hom d) = ψ₂ d := fun d ↦ congrArg (fun g ↦ CommAlgCat.Hom.hom g d) hφ₂
  let f := (toAlgHom A C).comp ψ₁
  let e := Index.ofEtaleEquiv D f
  let g₁ : Index.ofEtale D f ⟶ X₁ := ⟨φ₁.hom.comp e.toAlgHom, by
    ext y
    simp only [AlgHom.comp_apply, Index.ofEtale_toC_apply]
    rw [← toAlgHom_ι, h₁]
    rfl⟩
  let g₂ : Index.ofEtale D f ⟶ X₂ := ⟨φ₂.hom.comp e.toAlgHom, by
    ext y
    simp only [AlgHom.comp_apply, Index.ofEtale_toC_apply]
    rw [← toAlgHom_ι, h₂]
    exact (DFunLike.congr_fun h _).symm⟩
  obtain ⟨Z, t₁, t₂, -⟩ := IsFiltered.cocone_objs X₁ X₂
  obtain ⟨Z', q, hq⟩ := IsFiltered.cocone_maps (g₁ ≫ t₁) (g₂ ≫ t₂)
  ext d
  obtain ⟨y, rfl⟩ := e.surjective d
  rw [← h₁, ← h₂, ← ι_hom (t₁ ≫ q), ← ι_hom (t₂ ≫ q)]
  have := congrArg (fun g : Index.ofEtale D f ⟶ Z' ↦ g.hom y) hq
  simpa [g₁, g₂] using congrArg (ι Z') this

/-- Every `A`-algebra map from an étale `A`-algebra `D` to `C̄` lifts to `H_A(C̄)`: `D` is itself
an object of `N_A(C̄)`. -/
theorem exists_algHom_of_etale (D : Type u) [CommRing D] [Algebra A D] [Algebra.Etale A D]
    (f : D →ₐ[A] C) : ∃ ψ : D →ₐ[A] ClosedLift A C, (toAlgHom A C).comp ψ = f :=
  ⟨(ι (Index.ofEtale D f)).comp (Index.ofEtaleEquiv D f).symm.toAlgHom, by
    ext d
    simp [Index.ofEtale_toC_apply]⟩

/-- For an ind-étale `A`-algebra `D`, composition with `H_A(C̄) ⟶ C̄` is a bijection
`Hom_A(D, H_A(C̄)) → Hom_A(D, C̄)`: apply the étale case on the stages of a filtered colimit
presentation of `D`. -/
theorem bijective_comp_toAlgHom (D : Type u) [CommRing D] [Algebra A D] [Algebra.IndEtale A D] :
    Function.Bijective (fun ψ : D →ₐ[A] ClosedLift A C ↦ (toAlgHom A C).comp ψ) := by
  obtain ⟨κ, _, _, P, hP⟩ := Algebra.IndEtale.exists_colimitPresentation (R := A) (S := D)
  have hinj : ∀ ψ₁ ψ₂ : D →ₐ[A] ClosedLift A C,
      (toAlgHom A C).comp ψ₁ = (toAlgHom A C).comp ψ₂ → ψ₁ = ψ₂ := by
    intro ψ₁ ψ₂ h
    have : CommAlgCat.ofHom ψ₁ = CommAlgCat.ofHom ψ₂ := by
      refine P.isColimit.hom_ext fun a ↦ ?_
      have : Algebra.Etale A (P.diag.obj a) := hP a
      ext1
      refine algHom_ext_of_etale ?_
      ext x
      exact DFunLike.congr_fun h ((P.ι.app a).hom x)
    exact congrArg CommAlgCat.Hom.hom this
  refine ⟨fun ψ₁ ψ₂ h ↦ hinj ψ₁ ψ₂ h, fun f ↦ ?_⟩
  have hex : ∀ a, ∃ ψ : P.diag.obj a →ₐ[A] ClosedLift A C,
      (toAlgHom A C).comp ψ = f.comp (P.ι.app a).hom := fun a ↦
    have : Algebra.Etale A (P.diag.obj a) := hP a
    exists_algHom_of_etale _ _
  choose ψ hψ using hex
  let c : Cocone P.diag :=
    { pt := CommAlgCat.of A (ClosedLift A C)
      ι :=
        { app a := CommAlgCat.ofHom (ψ a)
          naturality a b g := by
            have : Algebra.Etale A (P.diag.obj a) := hP a
            ext1
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
              CommAlgCat.hom_comp, CommAlgCat.hom_ofHom]
            refine algHom_ext_of_etale ?_
            rw [← AlgHom.comp_assoc, hψ, hψ, AlgHom.comp_assoc, ← CommAlgCat.hom_comp, P.w] } }
  refine ⟨(P.isColimit.desc c).hom, ?_⟩
  have : CommAlgCat.ofHom ((toAlgHom A C).comp (P.isColimit.desc c).hom) = CommAlgCat.ofHom f := by
    refine P.isColimit.hom_ext fun a ↦ ?_
    ext1
    have h := P.isColimit.fac c a
    simp only [CommAlgCat.hom_comp, CommAlgCat.hom_ofHom]
    rw [← AlgHom.comp_assoc, ← CommAlgCat.hom_comp, h]
    exact hψ a
  exact congrArg CommAlgCat.Hom.hom this

/-- For an ind-étale `A`-algebra `D`, composition with `H_A(C̄) ⟶ C̄` identifies
`Hom_A(D, H_A(C̄))` with `Hom_A(D, C̄)`. -/
noncomputable def homEquiv (D : Type u) [CommRing D] [Algebra A D] [Algebra.IndEtale A D] :
    (D →ₐ[A] ClosedLift A C) ≃ (D →ₐ[A] C) :=
  Equiv.ofBijective _ (bijective_comp_toAlgHom D)

@[simp]
lemma homEquiv_apply (D : Type u) [CommRing D] [Algebra A D] [Algebra.IndEtale A D]
    (ψ : D →ₐ[A] ClosedLift A C) : homEquiv D ψ = (toAlgHom A C).comp ψ :=
  rfl

variable (I : Ideal A) [Algebra (A ⧸ I) C] [IsScalarTower A (A ⧸ I) C]

/-- For an `A ⧸ I`-algebra `C̄`, `A`-algebra maps `D → C̄` are the `A ⧸ I`-algebra maps
`D ⧸ I D → C̄`. -/
noncomputable def quotientHomEquiv (D : Type u) [CommRing D] [Algebra A D] :
    (D →ₐ[A] C) ≃ (D ⧸ I.map (algebraMap A D) →ₐ[A ⧸ I] C) where
  toFun f := (Ideal.Quotient.liftₐ _ f (fun d hd ↦ by
    have : I.map (algebraMap A D) ≤ RingHom.ker (f : D →+* C) := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      simp only [Ideal.mem_comap, RingHom.mem_ker, RingHom.coe_coe, AlgHom.commutes]
      rw [IsScalarTower.algebraMap_apply A (A ⧸ I) C, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
    exact this hd)).extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  invFun g := (g.restrictScalars A).comp (Ideal.Quotient.mkₐ A _)
  left_inv f := by ext; rfl
  right_inv g := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

/-- Blueprint `lem-exc-closed-lift-adjunction` (subsection `sk-prop-sf-open-closed-triangle`): for
every ind-étale `A`-algebra `D`, reduction induces a natural bijection
`Hom_A(D, H_A(C̄)) ≃ Hom_{A ⧸ I}(D ⧸ I D, C̄)`; so `H_A` is right adjoint to reduction on
ind-étale algebras (see also `Algebra.ClosedLift.homEquiv`).

For `D` étale, a map `D ⧸ I D → C̄` makes `D` an object of `N_A(C̄)` and gives its canonical map
to the colimit; any two lifts factor through stages which a further stage equalizes. The general
case follows by passing to the colimit of the étale stages of `D`. -/
noncomputable def homEquivReduction (D : Type u) [CommRing D] [Algebra A D]
    [Algebra.IndEtale A D] :
    (D →ₐ[A] ClosedLift A C) ≃ (D ⧸ I.map (algebraMap A D) →ₐ[A ⧸ I] C) :=
  (homEquiv D).trans (quotientHomEquiv I D)

lemma homEquivReduction_apply_mk (D : Type u) [CommRing D] [Algebra A D]
    [Algebra.IndEtale A D] (ψ : D →ₐ[A] ClosedLift A C) (d : D) :
    homEquivReduction I D ψ (Ideal.Quotient.mk _ d) = toAlgHom A C (ψ d) :=
  rfl

end Algebra.ClosedLift
