/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Nakayama

/-!
# Unramifiedness of finite algebras via the closed fibre

* `Algebra.FormallyUnramified.of_formallyUnramified_quotient_map_of_le_jacobson`: a finite
  `R`-algebra `S` is formally unramified as soon as `S ⧸ IS` is, for `I` in the Jacobson radical
  (Nakayama's lemma applied to `Ω[S⁄R]`).
* `Algebra.FormallyUnramified.isReduced_quotient_map_maximalIdeal`: a formally unramified closed
  fibre of finite type over a local ring is reduced.
* `Algebra.Etale.of_formallyUnramified_quotient_map_maximalIdeal`: a finite flat algebra over a
  discrete valuation ring with formally unramified closed fibre is étale.
-/

@[expose] public section

open TensorProduct IsLocalRing

namespace Algebra.FormallyUnramified

/-- A finite `R`-algebra `S` is formally unramified if `S ⧸ IS` is, for an ideal `I` contained
in the Jacobson radical of `R` (Nakayama's lemma applied to the finite `R`-module `Ω[S⁄R]`). -/
theorem of_formallyUnramified_quotient_map_of_le_jacobson {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [Module.Finite R S] (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥)
    [FormallyUnramified R (S ⧸ I.map (algebraMap R S))] : FormallyUnramified R S := by
  have : FormallyUnramified R (S ⊗[R] (R ⧸ I)) :=
    .of_equiv ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).restrictScalars R)
  have : FormallyUnramified R ((R ⧸ I) ⊗[R] S) :=
    .of_equiv (Algebra.TensorProduct.comm R S (R ⧸ I))
  have : FormallyUnramified (R ⧸ I) ((R ⧸ I) ⊗[R] S) := .of_restrictScalars R _ _
  let _ : Algebra S ((R ⧸ I) ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  have h₁ : Subsingleton ((R ⧸ I) ⊗[R] Ω[S⁄R]) :=
    (KaehlerDifferential.tensorKaehlerEquivBase R (R ⧸ I) S ((R ⧸ I) ⊗[R] S)).subsingleton
  have h₂ : Subsingleton (Ω[S⁄R] ⧸ (I • ⊤ : Submodule R Ω[S⁄R])) :=
    (TensorProduct.quotTensorEquivQuotSMul Ω[S⁄R] I).symm.subsingleton
  have : Module.Finite R Ω[S⁄R] := .trans S _
  constructor
  rw [← Submodule.subsingleton_iff R, ← subsingleton_iff_bot_eq_top]
  refine (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I ⊤ Module.Finite.fg_top ?_ hI).symm
  rw [Submodule.Quotient.subsingleton_iff] at h₂
  exact h₂.ge

end Algebra.FormallyUnramified

set_option backward.inferInstanceAs.wrap.data false in
/-- If `S` is of finite type over a local ring `R` and the closed fibre `S ⧸ 𝔪_R S` is formally
unramified, then the closed fibre is reduced. -/
theorem Algebra.FormallyUnramified.isReduced_quotient_map_maximalIdeal {R S : Type*} [CommRing R]
    [IsLocalRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    [Algebra.FormallyUnramified R (S ⧸ (maximalIdeal R).map (algebraMap R S))] :
    IsReduced (S ⧸ (maximalIdeal R).map (algebraMap R S)) := by
  let mR := (maximalIdeal R).map (algebraMap R S)
  let _ : Algebra (ResidueField R) (S ⧸ mR) := inferInstanceAs <| Algebra (R ⧸ _) _
  have : IsScalarTower R (ResidueField R) (S ⧸ mR) :=
    inferInstanceAs <| IsScalarTower R (R ⧸ _) _
  have : Algebra.FormallyUnramified (ResidueField R) (S ⧸ mR) := .of_restrictScalars R _ _
  have : Algebra.EssFiniteType (ResidueField R) (S ⧸ mR) := .of_comp R _ _
  exact Algebra.FormallyUnramified.isReduced_of_field (ResidueField R) (S ⧸ mR)

/-- A finite flat algebra over a discrete valuation ring whose closed fibre is formally
unramified is étale. -/
theorem Algebra.Etale.of_formallyUnramified_quotient_map_maximalIdeal {R S : Type*} [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    [Module.Flat R S]
    [Algebra.FormallyUnramified R (S ⧸ (maximalIdeal R).map (algebraMap R S))] :
    Algebra.Etale R S := by
  have : Algebra.FormallyUnramified R S :=
    .of_formallyUnramified_quotient_map_of_le_jacobson (maximalIdeal R) (maximalIdeal_le_jacobson _)
  have : Algebra.FinitePresentation R S := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact .of_formallyUnramified_of_flat
