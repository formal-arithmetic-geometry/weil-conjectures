/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Principal
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-!
# Derived coextension of scalars preserves derived completeness

Let `φ : R →+* R'` be a ring morphism, `ϖ ∈ R` and `ϖ' ∈ R'` nonzerodivisors with
`φ ϖ = u ϖ'ᵉ` for a unit `u` (for instance the uniformizers of the rings of integers of a finite
extension `L/E` of `ℓ`-adic fields). The right derived functor of coextension of scalars
`D(J, R) ⥤ D(J, R')` carries `ϖ`-adically derived complete objects to `ϖ'`-adically derived
complete objects (`DerivedCategory.derivedComplete_rightDerivedFunctor_coextendScalars`).

Derived completeness is right orthogonality to the objects on which the uniformizer acts
invertibly (`DerivedCategory.derivedComplete_iff_rightOrthogonal`), and `R coext` is right
adjoint to the exact restriction of scalars, which carries objects on which `ϖ'` acts
invertibly to objects on which `ϖ` acts invertibly: restriction of scalars is semilinear along
`φ` on derived categories (`DerivedCategory.restrictScalars_map_smul_id`).

This is a step towards the scalar-extension transition functors of the `ℚ̄_ℓ` coefficient stage
(blueprint `def-weil-algebraically-closed-coefficients`).
-/

@[expose] public section

universe u

open CategoryTheory Category Limits

namespace DerivedCategory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R R' : Type (u + 1)} [CommRing R] [CommRing R'] (φ : R →+* R')

instance :
    PreservesLimitsOfSize.{u, u + 1} (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ) :=
  (ModuleCat.restrictCoextendScalarsAdj.{u + 1} φ).rightAdjoint_preservesLimits

instance : (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ).IsRightAdjoint :=
  (ModuleCat.restrictCoextendScalarsAdj.{u + 1} φ).isRightAdjoint

instance : (sheafCompose J (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ)).Additive where
  map_add := by intros; ext : 3; rfl

instance : (Sheaf.restrictScalars J φ).Additive where
  map_add := by intros; ext : 3; rfl

instance : (Sheaf.restrictScalars J φ).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels _

instance : PreservesFiniteLimits (Sheaf.restrictScalars J φ) :=
  Functor.preservesFiniteLimits_of_preservesHomology _

instance : PreservesFiniteColimits (Sheaf.restrictScalars J φ) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

omit [EssentiallySmall.{u + 1} C] in
/-- Restriction of scalars on sheaves is semilinear along `φ`. -/
lemma sheafRestrictScalars_map_smul {F G : Sheaf J (ModuleCat.{u + 1} R')} (r : R) (f : F ⟶ G) :
    (Sheaf.restrictScalars J φ).map (φ r • f) = r • (Sheaf.restrictScalars J φ).map f := by
  ext : 3
  rfl

/-- Restriction of scalars is semilinear along `φ` on derived categories: the image of
`φ r • 𝟙 N` is `r • 𝟙`. -/
lemma restrictScalars_map_smul_id (r : R) (N : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R'))) :
    (Sheaf.restrictScalars J φ).mapDerivedCategory.map (φ r • 𝟙 N) =
      r • 𝟙 ((Sheaf.restrictScalars J φ).mapDerivedCategory.obj N) := by
  set F := (Sheaf.restrictScalars J φ).mapDerivedCategory
  obtain ⟨K, ⟨e⟩⟩ : ∃ K, Nonempty (DerivedCategory.Q.obj K ≅ N) :=
    ⟨_, ⟨DerivedCategory.Q.objObjPreimageIso N⟩⟩
  have hN : φ r • 𝟙 N = e.inv ≫ DerivedCategory.Q.map (φ r • 𝟙 K) ≫ e.hom := by
    simp
  have hK : ((Sheaf.restrictScalars J φ).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (φ r • 𝟙 K) = r • 𝟙 _ := by
    ext n : 1
    simp [sheafRestrictScalars_map_smul]
    rfl
  have hF : F.map (DerivedCategory.Q.map (φ r • 𝟙 K)) = r • 𝟙 _ := by
    have h := (Sheaf.restrictScalars J φ).mapDerivedCategoryFactors.hom.naturality (φ r • 𝟙 K)
    dsimp only [Functor.comp_map] at h
    rw [hK, Functor.map_smul (R := R), CategoryTheory.Functor.map_id, Linear.comp_smul] at h
    rw [← cancel_mono ((Sheaf.restrictScalars J φ).mapDerivedCategoryFactors.hom.app K), h,
      Linear.smul_comp]
    simp
  rw [hN, F.map_comp, F.map_comp, hF]
  simp

/-- Multiplication by a power of an element acting invertibly acts invertibly. -/
lemma isIso_pow_smul_id {D : Type*} [Category D] [Preadditive D] [Linear R' D] {N : D} (ϖ' : R')
    [IsIso (ϖ' • 𝟙 N)] (e : ℕ) : IsIso (ϖ' ^ e • 𝟙 N) := by
  induction e with
  | zero => simpa using (inferInstance : IsIso (𝟙 N))
  | succ e ih =>
    have : ϖ' ^ (e + 1) • 𝟙 N = (ϖ' ^ e • 𝟙 N) ≫ (ϖ' • 𝟙 N) := by
      rw [pow_succ, mul_smul, Linear.smul_comp, Linear.comp_smul, Category.id_comp]
    rw [this]
    infer_instance

variable {J φ}

/-- Restriction of scalars along `φ` carries objects on which `ϖ'` acts invertibly to objects on
which `ϖ` acts invertibly, when `φ ϖ = u ϖ'ᵉ` for a unit `u`. -/
lemma smulInvertible_restrictScalars {ϖ : R} {ϖ' : R'} (u : R'ˣ) (e : ℕ)
    (h : φ ϖ = u * ϖ' ^ e) {N : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R'))}
    (hN : smulInvertible J ϖ' N) :
    smulInvertible J ϖ ((Sheaf.restrictScalars J φ).mapDerivedCategory.obj N) := by
  change IsIso (ϖ • 𝟙 _)
  rw [← restrictScalars_map_smul_id, h]
  have : IsIso (ϖ' • 𝟙 N) := hN
  have := isIso_pow_smul_id (N := N) ϖ' e
  have : IsIso ((u : R') • 𝟙 N) :=
    ⟨⟨((u⁻¹ : R'ˣ) : R') • 𝟙 N, by simp [smul_smul], by simp [smul_smul]⟩⟩
  have : (↑u * ϖ' ^ e) • 𝟙 N = ((u : R') • 𝟙 N) ≫ (ϖ' ^ e • 𝟙 N) := by
    rw [mul_smul, Linear.smul_comp, Linear.comp_smul, Category.id_comp]
  rw [this]
  infer_instance

/-- **Derived coextension of scalars preserves derived completeness.** For `φ : R →+* R'` and
nonzerodivisors `ϖ ∈ R`, `ϖ' ∈ R'` with `φ ϖ = u ϖ'ᵉ`, `u` a unit, the right derived functor of
coextension of scalars carries `(ϖ)`-adically derived complete objects of `D(J, R)` to
`(ϖ')`-adically derived complete objects of `D(J, R')`. -/
theorem derivedComplete_rightDerivedFunctor_coextendScalars {ϖ : R} {ϖ' : R'}
    (hϖ : ϖ ∈ nonZeroDivisors R) (hϖ' : ϖ' ∈ nonZeroDivisors R') {I : Ideal R} {I' : Ideal R'}
    (hI : I = Ideal.span {ϖ}) (hI' : I' = Ideal.span {ϖ'}) (u : R'ˣ) (e : ℕ)
    (h : φ ϖ = u * ϖ' ^ e) {K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))}
    (hK : derivedComplete J I K) :
    derivedComplete J I'
      ((sheafCompose J (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ)).rightDerivedFunctor.obj
        K) := by
  rw [derivedComplete_iff_rightOrthogonal hϖ hI] at hK
  rw [derivedComplete_iff_rightOrthogonal hϖ' hI']
  intro N f hN
  let adj := (Sheaf.restrictCoextendScalarsAdj J φ).mapDerivedCategoryRightDerivedAdjunction
  have h0 := hK ((adj.homEquiv _ _).symm f) (smulInvertible_restrictScalars u e h hN)
  rw [← (adj.homEquiv _ _).apply_symm_apply f, h0]
  simp

end DerivedCategory
