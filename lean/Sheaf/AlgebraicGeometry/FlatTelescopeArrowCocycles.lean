/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Sheaf.AlgebraicGeometry.FlatTelescopeArrowBarData

/-! # Summand cocycles for a simultaneous flat-tower resolution

Source: the geometric construction and retained homotopies of
lem-sc-flat-telescope-arrow-diagram, steps 1--3; Stacks Project Tags 077J and 06YS.
(blueprint: lem-sc-flat-telescope-arrow-cocycles).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex
namespace AlgebraicGeometry

/-- The geometric part of the simultaneous resolution, before assembling a map
out of the source cone. The four equations are equations of cochains on the source
sum, retaining both components of the comparison homotopies. No source-cone
augmentation or equality of maps from that cone is asserted here.

Source: lem-sc-flat-telescope-arrow-diagram, steps 1 and 2 and the retained arrow
homotopies in step 3; Stacks Project Tags 077J and 06YS. The simultaneous comparison
is the parent plan's agent expansion, not a theorem stated verbatim by Stacks.

Proof. Apply the finite-piece bar construction of
`exists_flat_telescope_arrow_bar_data`. It supplies zero shifted restrictions for
both target augmentations and strict agreement of their unshifted restrictions
with the source sum augmentation. Choose all four cochains to be zero. Their
differentials and their composites are zero. Substitution of the two shifted
restriction equalities proves the first and third equations. Apply `Cochain.ofHom`
to the two strict sum identities and reverse the resulting equalities to obtain
the second and fourth equations. The tower, bounds, flatness, quasi-isomorphisms,
and target homotopy isomorphisms are preserved unchanged. No support or lifting
argument is used in this algebraic step.
(blueprint: lem-sc-flat-telescope-arrow-cocycles). -/
theorem exists_flat_telescope_arrow_cocycles (Y : Scheme.{u})
    (P P' : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hP : isFlatTelescope Y P) (hP' : isFlatTelescope Y P') (f : P ⟶ P') :
    let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
    let Q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
    ∃ (E₀ E₁ E₂ : ℕ → CochainComplex A ℤ)
      (t₀ : ∀ n : ℕ, E₀ n ⟶ E₀ (n + 1))
      (t₁ : ∀ n : ℕ, E₁ n ⟶ E₁ (n + 1))
      (t₂ : ∀ n : ℕ, E₂ n ⟶ E₂ (n + 1))
      (a : ∀ n : ℕ, E₀ n ⟶ E₁ n) (b : ∀ n : ℕ, E₀ n ⟶ E₂ n),
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₀ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₀ n).X i)) ∧
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₁ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₁ n).X i)) ∧
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₂ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₂ n).X i)) ∧
      ∃ (_c₁ : flatTelescopeDifferential E₀ t₀ ≫ Limits.Sigma.map a =
          Limits.Sigma.map a ≫ flatTelescopeDifferential E₁ t₁)
        (_c₂ : flatTelescopeDifferential E₀ t₀ ≫ Limits.Sigma.map b =
          Limits.Sigma.map b ≫ flatTelescopeDifferential E₂ t₂)
        (r₁ : CochainComplex.mappingCone (flatTelescopeDifferential E₁ t₁) ⟶ P)
        (r₂ : CochainComplex.mappingCone (flatTelescopeDifferential E₂ t₂) ⟶ P')
        (q : ∀ n : ℕ, E₀ n ⟶ P.truncLE (n : ℤ)),
        IsIso (Q.map r₁) ∧ IsIso (Q.map r₂) ∧
        (∀ n : ℕ, QuasiIso (q n)) ∧
        (∀ n : ℕ, t₀ n ≫ q (n + 1) ≫ P.ιTruncLE ((n + 1 : ℕ) : ℤ) =
          q n ≫ P.ιTruncLE (n : ℤ)) ∧
        let s := Sigma.desc (fun n : ℕ ↦ q n ≫ P.ιTruncLE (n : ℤ))
        ∃ (α₁ : Cochain (∐ E₀) P (-2)) (β₁ : Cochain (∐ E₀) P (-1))
          (α₂ : Cochain (∐ E₀) P' (-2)) (β₂ : Cochain (∐ E₀) P' (-1)),
          (0 : Cochain (∐ E₀) P (-1)) =
            δ (-2) (-1) α₁ +
            (Cochain.ofHom (flatTelescopeDifferential E₀ t₀)).comp β₁ (zero_add _) +
            (Cochain.ofHom (Limits.Sigma.map a)).comp
              ((CochainComplex.mappingCone.inl (flatTelescopeDifferential E₁ t₁)).comp
                (Cochain.ofHom r₁) (add_zero _)) (zero_add _) ∧
          Cochain.ofHom s = δ (-1) 0 β₁ +
            Cochain.ofHom (Limits.Sigma.map a ≫
              CochainComplex.mappingCone.inr (flatTelescopeDifferential E₁ t₁) ≫
              r₁) ∧
          (0 : Cochain (∐ E₀) P' (-1)) =
            δ (-2) (-1) α₂ +
            (Cochain.ofHom (flatTelescopeDifferential E₀ t₀)).comp β₂ (zero_add _) +
            (Cochain.ofHom (Limits.Sigma.map b)).comp
              ((CochainComplex.mappingCone.inl (flatTelescopeDifferential E₂ t₂)).comp
                (Cochain.ofHom r₂) (add_zero _)) (zero_add _) ∧
          Cochain.ofHom (s ≫ f) = δ (-1) 0 β₂ +
            Cochain.ofHom (Limits.Sigma.map b ≫
              CochainComplex.mappingCone.inr (flatTelescopeDifferential E₂ t₂) ≫
              r₂) := by
  obtain ⟨E₀, E₁, E₂, t₀, t₁, t₂, a, b, hb₀, hf₀, hb₁, hf₁, hb₂, hf₂,
    _c₁, _c₂, r₁, r₂, q, hi₁, hi₂, hq, hc, hL₁, hL₂, hs₁, hs₂⟩ :=
    exists_flat_telescope_arrow_bar_data Y P P' hP hP' f
  dsimp only
  refine ⟨E₀, E₁, E₂, t₀, t₁, t₂, a, b, hb₀, hf₀, hb₁, hf₁, hb₂, hf₂,
    _c₁, _c₂, r₁, r₂, q, hi₁, hi₂, hq, hc, ?_⟩
  let s := Sigma.desc (fun n : ℕ ↦ q n ≫ P.ιTruncLE (n : ℤ))
  refine ⟨0, 0, 0, 0, ?_, ?_, ?_, ?_⟩
  · simp only [δ_zero, Cochain.comp_zero, zero_add, hL₁]
  · simpa only [δ_zero, zero_add] using (congrArg Cochain.ofHom hs₁).symm
  · simp only [δ_zero, Cochain.comp_zero, zero_add, hL₂]
  · simpa only [δ_zero, zero_add] using (congrArg Cochain.ofHom hs₂).symm

end AlgebraicGeometry
