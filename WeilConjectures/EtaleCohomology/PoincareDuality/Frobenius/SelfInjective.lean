/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.HomToInjective
public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Perfectness

/-!
# Degreewise Poincaré duality over a self-injective coefficient ring

Let `Λ` be a finite coefficient ring which is self-injective and cogenerates (every nonzero
element of a `Λ`-module is detected by a linear form to `Λ`), e.g. `Λ = ℤ/ℓᵐ`
(`ZModLike.injective_self`, `ZModLike.exists_apply_ne_zero`). Then the degreewise Poincaré
pairings `⟨-, -⟩_i : H^i_c(X, K) × H^{2d-i}(X, K^∨(d)) ⟶ Λ` are nondegenerate on both sides
(`AlgebraicGeometry.Etale.TateOrientation.injective_degreewisePoincarePairing`): over a
self-injective ring the dual `RHom(C, Λ)` of a complex is computed degreewise,
`Hom(C, Λ[0]) = Hom(H⁰(C), Λ)`
(`DerivedCategory.bijective_homologyFunctor_map_singleFunctor_of_injective`).

This is the finite-level duality `A_{E,n}` of blueprint `sk-thm-transport` in the form needed
for the transport to `ℚ̄_ℓ` (`LinearMap.mem_torsion_of_finiteLevel`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace DerivedCategory

variable {R : Type u} [CommRing R] [HasDerivedCategory.{u} (ModuleCat.{u} R)]
  [Module.Injective R R]

/-- **The composition pairing with `R[0]` is nondegenerate over a self-injective
cogenerating ring.** Let `R` be self-injective such that every nonzero element of an `R`-module
is detected by a linear form. Then for every `E ∈ D(R)` the composition pairing
`Hom(R[0], E) × Hom(E, R[0]) ⟶ End(R[0])` is nondegenerate on both sides. -/
theorem nondegenerate_comp_singleFunctor_of_injective
    (hcog : ∀ (M : ModuleCat.{u} R) (x : M), x ≠ 0 → ∃ χ : M →ₗ[R] R, χ x ≠ 0)
    (E : DerivedCategory (ModuleCat.{u} R)) :
    (∀ x : (singleFunctor _ 0).obj (ModuleCat.of R R) ⟶ E, x ≠ 0 →
        ∃ f : E ⟶ (singleFunctor _ 0).obj (ModuleCat.of R R), x ≫ f ≠ 0) ∧
      (∀ f : E ⟶ (singleFunctor _ 0).obj (ModuleCat.of R R), f ≠ 0 →
        ∃ x : (singleFunctor _ 0).obj (ModuleCat.of R R) ⟶ E, x ≫ f ≠ 0) := by
  have : Injective (ModuleCat.of R R) := Module.injective_object_of_injective_module R R
  let U := (singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)
  let ε := (singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).app (ModuleCat.of R R)
  have hH := bijective_homologyFunctor_map_singleFunctor_of_injective E (ModuleCat.of R R)
  have hθ (Y : DerivedCategory (ModuleCat.{u} R)) :
      Function.Bijective (homSingleToHomology (ModuleCat.of R R) 0 Y) := by
    convert (homSingleEquivOfProjective (ModuleCat.of R R) 0 Y).bijective using 1
    exact funext fun φ ↦ (homSingleEquivOfProjective_apply _ _ _ φ).symm
  have hθ0 (Y : DerivedCategory (ModuleCat.{u} R)) :
      homSingleToHomology (ModuleCat.of R R) 0 Y 0 = 0 := by
    simp [homSingleToHomology]
  have hne (Y : DerivedCategory (ModuleCat.{u} R)) (z : U ⟶ Y)
      (hz : (homSingleToHomology (ModuleCat.of R R) 0 Y z).hom 1 ≠ 0) : z ≠ 0 := by
    rintro rfl
    rw [hθ0] at hz
    exact hz rfl
  refine ⟨fun x hx ↦ ?_, fun f hf ↦ ?_⟩
  · have hx' : (homSingleToHomology (ModuleCat.of R R) 0 E x).hom 1 ≠ 0 := by
      intro h
      apply hx
      refine (hθ E).1 ?_
      rw [hθ0]
      exact ModuleCat.hom_ext (LinearMap.ext_ring h)
    obtain ⟨χ, hχ⟩ := hcog _ _ hx'
    obtain ⟨f, hf⟩ := hH.2 (ModuleCat.ofHom χ ≫ ε.inv)
    refine ⟨f, hne U _ ?_⟩
    simp only at hf
    rw [homSingleToHomology_comp, hf]
    have hinj : Function.Injective ε.inv.hom :=
      (ModuleCat.mono_iff_injective ε.inv).1 inferInstance
    intro h0
    apply hχ
    apply hinj
    rw [map_zero]
    exact h0
  · have hHf : (homologyFunctor _ 0).map f ≠ 0 := fun h ↦ hf (hH.1 (by
      simp only [h, Functor.map_zero]))
    obtain ⟨v, hv⟩ : ∃ v, ((homologyFunctor _ 0).map f).hom v ≠ 0 := by
      by_contra! h
      exact hHf (ModuleCat.hom_ext (LinearMap.ext h))
    obtain ⟨x, hx⟩ := (hθ E).2 (ModuleCat.ofHom (LinearMap.toSpanSingleton R _ v))
    refine ⟨x, hne U _ ?_⟩
    rw [homSingleToHomology_comp, hx]
    simpa using hv

end DerivedCategory

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] [Module.Injective Λ Λ] {k : Type u} [Field k]
  [IsSepClosed k]

/-- **The composition pairing with the unit is nondegenerate at the point, over a self-injective
cogenerating ring.** For `k` separably closed and `E` in the point category `D(Spec k_ét, Λ)`,
the composition pairing `Hom(Λ_s, E) × Hom(E, Λ_s) ⟶ End(Λ_s)` is nondegenerate on both sides.
This follows from the case of `D(Λ)` through the equivalence `RΓ(Spec k, -)`. -/
theorem nondegenerate_comp_unit_of_isSepClosed_of_injective
    (hcog : ∀ (M : ModuleCat.{u + 1} Λ) (x : M), x ≠ 0 → ∃ χ : M →ₗ[Λ] Λ, χ x ≠ 0)
    (E : DerivedCategoryModule Λ (Spec (.of k))) :
    (∀ x : 𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶ E, x ≠ 0 →
        ∃ f : E ⟶ 𝟙_ _, x ≫ f ≠ 0) ∧
      (∀ f : E ⟶ 𝟙_ (DerivedCategoryModule Λ (Spec (.of k))), f ≠ 0 →
        ∃ x : 𝟙_ _ ⟶ E, x ≫ f ≠ 0) := by
  let F := rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))
  obtain ⟨h₁, h₂⟩ := DerivedCategory.nondegenerate_comp_singleFunctor_of_injective hcog (F.obj E)
  exact ⟨F.exists_comp_ne_zero_of_fullyFaithful (rightDerivedGlobalSectionsUnitIso Λ k)
      (Iso.refl _) h₁,
    F.exists_comp_ne_zero_of_fullyFaithful' (rightDerivedGlobalSectionsUnitIso Λ k)
      (Iso.refl _) h₂⟩

variable [Finite Λ] [HasTateTwist Λ] {X : Scheme.{u}} {a : X ⟶ Spec (.of k)}
  [HasCompactification a] [HasInvertibleExponent Λ X] {d : ℕ}

namespace TateOrientation

end TateOrientation

end AlgebraicGeometry.Etale
