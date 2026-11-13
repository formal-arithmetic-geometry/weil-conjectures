/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion

/-! # Descent of a specified purity comparison from frame classes
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

private theorem supportedClassMap_zsmul
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (a : ℤ) (γ : constantComplex Λ X ⟶
      (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L)) :
    supportedClassMap Λ i (a • γ) = a • supportedClassMap Λ i γ := by
  simp only [supportedClassMap, rightDerivedLowerShriekTranspose,
    Adjunction.homEquiv_counit, Preadditive.zsmul_comp, Functor.map_zsmul,
    Preadditive.comp_zsmul]

/-- A specified exceptional comparison is the fundamental-class map if its supported
class agrees with the frame class on a Zariski frame through each point of the support. -/
theorem regularImmersion_comparison_of_frameRestriction
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ]
    {X Z : Scheme.{u}} [HasInvertibleExponent Λ X]
    (c : ℕ) (i : Z ⟶ X) [IsRegularImmersion c i]
    {k : Type u} [Field k] [PerfectField k]
    (aX : X ⟶ Spec (.of k)) [Smooth aX]
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z))
    (φ : constantComplex Λ Z ⟶
      (R(i)^![Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧))
    (h : ∀ z : Z, ∃ F : i.EtaleFrame c,
      IsOpenImmersion F.e ∧ z ∈ Set.range F.toZ ∧
        frameRestriction Λ F
          ((supportedClassMapEquiv Λ i ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)).symm φ) =
            frameClass Λ F) :
    φ = fundamentalClassMap Λ c i aX hZ := by
  let E := supportedClassMapEquiv Λ i ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)
  have hclass : E.symm φ = fundamentalClass Λ c i aX hZ := by
    apply eq_of_forall_exists_frameRestriction_eq Λ c i aX hZ
    intro z
    obtain ⟨F, hF, hz, heq⟩ := h z
    exact ⟨F, hF, hz, heq.trans (frameRestriction_fundamentalClass Λ c i aX hZ F).symm⟩
  calc
    φ = E (E.symm φ) := (E.apply_symm_apply φ).symm
    _ = E (fundamentalClass Λ c i aX hZ) := congrArg E hclass
    _ = fundamentalClassMap Λ c i aX hZ := rfl

/-- Equality with a signed fundamental class descends from coordinate frames. -/
theorem regularImmersion_signed_comparison_of_frameRestriction
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ]
    {X Z : Scheme.{u}} [HasInvertibleExponent Λ X]
    (c : ℕ) (i : Z ⟶ X) [IsRegularImmersion c i]
    {k : Type u} [Field k] [PerfectField k]
    (aX : X ⟶ Spec (.of k)) [Smooth aX]
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z))
    (φ : constantComplex Λ Z ⟶
      (R(i)^![Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧))
    (h : ∀ z : Z, ∃ F : i.EtaleFrame c,
      IsOpenImmersion F.e ∧ z ∈ Set.range F.toZ ∧
        frameRestriction Λ F
          ((supportedClassMapEquiv Λ i ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)).symm φ) =
            ((-1 : ℤ) ^ c) • frameClass Λ F) :
    fundamentalClassMap Λ c i aX hZ = ((-1 : ℤ) ^ c) • φ := by
  let E := supportedClassMapEquiv Λ i ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)
  have hclass : E.symm φ = ((-1 : ℤ) ^ c) • fundamentalClass Λ c i aX hZ := by
    apply eq_of_forall_exists_frameRestriction_eq Λ c i aX hZ
    intro z
    obtain ⟨F, hF, hz, heq⟩ := h z
    refine ⟨F, hF, hz, heq.trans ?_⟩
    simp only [frameRestriction, restrictSupportedClass, Functor.map_zsmul,
      Preadditive.comp_zsmul, Preadditive.zsmul_comp]
    rw [← frameRestriction_fundamentalClass Λ c i aX hZ F]
    rfl
  have hphi : φ = ((-1 : ℤ) ^ c) • fundamentalClassMap Λ c i aX hZ := by
    calc
      φ = E (E.symm φ) := (E.apply_symm_apply φ).symm
      _ = E (((-1 : ℤ) ^ c) • fundamentalClass Λ c i aX hZ) := congrArg E hclass
      _ = ((-1 : ℤ) ^ c) • fundamentalClassMap Λ c i aX hZ :=
        supportedClassMap_zsmul Λ i _ _
  rw [hphi, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

end AlgebraicGeometry.Etale
