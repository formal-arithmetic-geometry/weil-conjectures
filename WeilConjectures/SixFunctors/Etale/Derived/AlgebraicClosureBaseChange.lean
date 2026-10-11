/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.ExtendScalarsLimits
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegers
public import WeilConjectures.SixFunctors.Etale.Derived.AlgebraicClosureStage

/-!
# Base change `− ⊗_{𝒪_E} 𝒪_L` on étale sheaves

For finite extensions `E ⊆ L` of `ℚ_ℓ` inside `ℚ̄_ℓ`, the ring `𝒪_L` is finite free over `𝒪_E`
(`PadicAlgCl.finite_integers`, `PadicAlgCl.free_integers`), so extension of scalars along
`𝒪_E → 𝒪_L` preserves limits (`ModuleCat.preservesLimits_extendScalars`) and induces the base
change functor `K ↦ K ⊗_{𝒪_E} 𝒪_L` on étale sheaves
(`AlgebraicGeometry.Etale.sheafBaseChangeTransition`), the sheaf-level transition functor of
blueprint `def-weil-algebraically-closed-coefficients`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace PadicAlgCl.FiniteSubext

variable {l : ℕ} [Fact l.Prime] {E L : FiniteSubext l} (h : E ≤ L)

/-- `𝒪_L` is a finite module over `𝒪_E`, on the universe `u + 1` copies. -/
instance finite_restrictScalars_integersShrinkMap :
    Module.Finite (Shrink.{u + 1} (integers l E.field))
      ((ModuleCat.restrictScalars (integersShrinkMap.{0, u} l (incl h) (incl_compat h))).obj
        (.of _ (Shrink.{u + 1} (integers l L.field)))) := by
  let : Algebra E.field L.field := (incl h).toAlgebra
  have : IsScalarTower E.field L.field (PadicAlgCl l) :=
    .of_algebraMap_eq fun x ↦ (incl_compat h x).symm
  have : IsScalarTower ℚ_[l] E.field L.field := .of_algebraMap_eq fun _ ↦ rfl
  have : FiniteDimensional E.field L.field := .right ℚ_[l] E.field L.field
  let := integersAlgebra l E.field L.field
  have := finite_integers l E.field L.field
  let := (integersShrinkMap.{0, u} l (incl h) (incl_compat h)).toAlgebra
  exact Module.Finite.of_equiv_equiv (A₁ := integers l E.field) (B₁ := integers l L.field)
    (shrinkRingEquiv l E.field) (shrinkRingEquiv l L.field) (by
      ext x
      simp [RingHom.algebraMap_toAlgebra, integersShrinkMap]
      rfl)

/-- `𝒪_L` is a projective module over `𝒪_E`, on the universe `u + 1` copies. -/
instance projective_restrictScalars_integersShrinkMap :
    Module.Projective (Shrink.{u + 1} (integers l E.field))
      ((ModuleCat.restrictScalars (integersShrinkMap.{0, u} l (incl h) (incl_compat h))).obj
        (.of _ (Shrink.{u + 1} (integers l L.field)))) := by
  let : Algebra E.field L.field := (incl h).toAlgebra
  have : IsScalarTower E.field L.field (PadicAlgCl l) :=
    .of_algebraMap_eq fun x ↦ (incl_compat h x).symm
  have : IsScalarTower ℚ_[l] E.field L.field := .of_algebraMap_eq fun _ ↦ rfl
  have : FiniteDimensional E.field L.field := .right ℚ_[l] E.field L.field
  let := integersAlgebra l E.field L.field
  have := free_integers l E.field L.field
  have := RingHomInvPair.of_ringEquiv (shrinkRingEquiv.{0, u} l E.field)
  have := RingHomInvPair.of_ringEquiv (shrinkRingEquiv.{0, u} l E.field).symm
  exact Module.Projective.of_equiv
    (σ := (shrinkRingEquiv.{0, u} l E.field : integers l E.field →+* _))
    (σ' := ((shrinkRingEquiv.{0, u} l E.field).symm : _ →+* integers l E.field))
    { (shrinkRingEquiv l L.field).toAddEquiv with
      map_smul' a x := by
        change shrinkRingEquiv l L.field (_ * x) = _ * shrinkRingEquiv l L.field x
        simp only [integersShrinkMap, map_mul]
        congr 1
        simp
        rfl }

end PadicAlgCl.FiniteSubext

namespace AlgebraicGeometry.Etale

open PadicAlgCl PadicAlgCl.FiniteSubext

variable {l : ℕ} [Fact l.Prime] (X : Scheme.{u})

/-- The base change functor `K ↦ K ⊗_{𝒪_E} 𝒪_L` on étale sheaves of modules, for finite
extensions `E ⊆ L` of `ℚ_ℓ` inside `ℚ̄_ℓ`: the sheaf-level transition functor of blueprint
`def-weil-algebraically-closed-coefficients`. No completion is needed, `𝒪_L` being finite free
over `𝒪_E`. -/
noncomputable abbrev sheafBaseChangeTransition {E L : FiniteSubext l} (h : E ≤ L) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Shrink.{u + 1} (integers l E.field))) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Shrink.{u + 1} (integers l L.field))) :=
  sheafExtendScalars _ (integersShrinkMap.{0, u} l (incl h) (incl_compat h))

end AlgebraicGeometry.Etale
