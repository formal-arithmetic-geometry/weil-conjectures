/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.RegularEndConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionNakayama
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstantRegularEnd

/-!
# Complexes with vanishing reduction modulo a regular endomorphism

Let `C` be a closed symmetric monoidal Grothendieck abelian category, `φ : R ⟶ S` a morphism of
commutative algebra objects and `r` an endomorphism of the regular `R`-module such that
`0 ⟶ R --r--> R --φ--> S ⟶ 0` is short exact. If the derived extension of scalars `S ⊗ᴸ_R K`
of `K ∈ D(Mod_R(C))` vanishes, then `r` acts invertibly on `K`, by the reduction triangle
`K --r--> K ⟶ S ⊗ᴸ_R K ⟶ K[1]`. Hence so does every integer `m` acting on the regular module as
`r ≫ ⋯ ≫ r ≫ v` for an automorphism `v`
(`CategoryTheory.Mod.isIso_zsmul_id_of_isZero_leftDerivedFunctor_extendScalars`).

Applied to a uniformizer `ϖ` of `𝒪_E`, writing `ℓ = u ϖ ^ e` with `u` a unit, this shows that
`ℓ` acts invertibly on every `𝒪_{E,X}`-complex whose first derived reduction vanishes
(`AlgebraicGeometry.ProEtale.isIso_zsmul_id_of_isZero_derivedReduction`).
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Obj

attribute [local instance] Bimod.monoidalCategory

namespace CategoryTheory.Mod

variable {C : Type*} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] {φ : R ⟶ S} [IsMonHom φ]

omit [MonoidalPreadditive C] in
/-- The identity of the regular module acts as the identity. -/
@[simp]
lemma regularEndSMul_id (M : Mod C R) : regularEndSMul (𝟙 (𝟙_ (Mod C R))) M = 𝟙 M := by
  simp [regularEndSMul]

/-- The identity of the regular module acts on complexes as the identity. -/
@[simp]
lemma regularEndSMulComplex_id (P : CochainComplex (Mod C R) ℤ) :
    regularEndSMulComplex (𝟙 (𝟙_ (Mod C R))) P = 𝟙 P := by
  ext i : 1
  simp

variable [Abelian.HasFunctorialFlatResolution C]

end CategoryTheory.Mod

namespace Profinite

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- The multiplication by `1` on `𝒪̲_E` is the identity. -/
lemma padicIntegersRingObjMulLeft_one :
    padicIntegersRingObjMulLeft.{u} ℓ E.1 1 = 𝟙 _ := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  ext S x
  exact ULift.ext _ _ (ContinuousMap.ext fun s ↦ one_mul (x.down s))

end Profinite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- The multiplication by `1` on the regular `𝒪_{E,X}`-module is the identity. -/
lemma padicIntegersRegularEndOfAlgebra_one :
    padicIntegersRegularEndOfAlgebra X ℓ E.1 1 = 𝟙 _ :=
  Mod.hom_ext _ _ (by
    rw [padicIntegersRegularEnd_hom, padicIntegersMulLeft,
      Profinite.padicIntegersRingObjMulLeft_one, CategoryTheory.Functor.map_id]
    rfl)

/-- The multiplication by a unit of `𝒪_E` on the regular `𝒪_{E,X}`-module is an isomorphism. -/
instance isIso_padicIntegersRegularEndOfAlgebra_unit (c : (PadicAlgCl.integers ℓ E.1)ˣ) :
    IsIso (padicIntegersRegularEndOfAlgebra X ℓ E.1 c) :=
  ⟨padicIntegersRegularEndOfAlgebra X ℓ E.1 ↑c⁻¹, by
    rw [← padicIntegersRegularEndOfAlgebra_mul, Units.mul_inv,
      padicIntegersRegularEndOfAlgebra_one], by
    rw [← padicIntegersRegularEndOfAlgebra_mul, Units.inv_mul,
      padicIntegersRegularEndOfAlgebra_one]⟩

end AlgebraicGeometry.ProEtale
