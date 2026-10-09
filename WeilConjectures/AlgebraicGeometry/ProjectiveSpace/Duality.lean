/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ExactSequence
public import WeilConjectures.AlgebraicGeometry.Cohomology.DualityPairing
public import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine
public import WeilConjectures.AlgebraicGeometry.Modules.Coherent
public import WeilConjectures.AlgebraicGeometry.Modules.HomTensor
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Koszul
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.Modules.Ext
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Serre duality on the projective line

Let `k` be a field, `ℙ¹_k = ProjectiveLine (Spec k)` and `ω = Ω¹_{ℙ¹_k/k}`. Every coherent
`𝒪_{ℙ¹}`-module `𝒢` has a resolution `0 → ℰ₂ → ℰ₁ → ℰ₀ → 𝒢 → 0` by finite direct sums of twists
`𝒪(d)`, and the two duality isomorphisms
`H¹(ℙ¹, 𝒢)^∨ ≅ Hom(𝒢, ω)` and `H⁰(ℙ¹, 𝒢)^∨ ≅ Ext¹(𝒢, ω)` hold.

## Main statements

- `AlgebraicGeometry.ProjectiveLine.exists_exact_sigma_twist`: resolutions by twists.
- `AlgebraicGeometry.ProjectiveLine.nonempty_dual_H_one_iso`: `H¹(ℙ¹, 𝒢)^∨ ≅ Hom(𝒢, ω)`,
  naturally in coherent `𝒢`.
- `AlgebraicGeometry.ProjectiveLine.nonempty_dual_H_zero_addEquiv_ext`:
  `H⁰(ℙ¹, 𝒢)^∨ ≅ Ext¹(𝒢, ω)`.

## Implementation notes

Coherence is spelled as `AlgebraicGeometry.Scheme.Modules.isCoherent`. The `𝒪_{ℙ¹}`-module
`Hom(𝒢, ω)` of global homomorphisms is written as `H⁰(ℙ¹, Hom(𝒢, ω))`, the global sections of the
internal hom, so that it is a functor to `k`-vector spaces.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

open scoped AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry

open Scheme.Modules

namespace ProjectiveSpace

variable (n : Type u) (S : Scheme.{u})

/-- **The dual of a twist.** `𝒪(a)ᵛ ≅ 𝒪(-a)` on `ℙ(n; S)`: both are tensor inverses of the
invertible module `𝒪(a)`. -/
theorem nonempty_dual_twist_iso (a : ℤ) : Nonempty ((twist n S a)ᵛ ≅ twist n S (-a)) := by
  obtain ⟨e⟩ := nonempty_tensorObj_twist_iso n S (-a) a
  obtain ⟨d⟩ := nonempty_tensorObj_dual_iso_unit (twist n S a)
  let e' : twist n S (-a) ⊗ twist n S a ≅ 𝟙_ _ :=
    e ≪≫ eqToIso (by rw [neg_add_cancel]) ≪≫ (unitIsoTwistZero n S).symm
  exact ⟨(λ_ _).symm ≪≫ whiskerRightIso e'.symm _ ≪≫ α_ _ _ _ ≪≫ whiskerLeftIso _ d ≪≫ ρ_ _⟩

end ProjectiveSpace

namespace ProjectiveLine

variable (k : Type u) [Field k]

/-- **Resolutions by twists on `ℙ¹_k`.** Every coherent `𝒪_{ℙ¹_k}`-module `𝒢` has a resolution
`0 → ℰ₂ → ℰ₁ → ℰ₀ → 𝒢 → 0` in which each `ℰᵢ` is a finite direct sum of twists `𝒪(d)`. Indeed
`𝒢 = M^~` for a finitely generated graded module `M` over `k[x₀, x₁]`, which has a graded free
resolution of length two by the graded Hilbert syzygy theorem; sheafifying it gives the
resolution, since `S(d)^~ = 𝒪(d)`.

(blueprint: `lem-sc-p1-graded-resolution`) -/
theorem exists_exact_sigma_twist (𝒢 : (ProjectiveLine (Spec (.of k))).Modules)
    [SheafOfModules.IsQuasicoherent (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf) 𝒢]
    [SheafOfModules.IsFinitePresentation (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf) 𝒢] :
    let 𝒪 : ℤ → (ProjectiveLine (Spec (.of k))).Modules :=
      ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k))
    ∃ (n₀ n₁ n₂ : ℕ) (d₀ : Fin n₀ → ℤ) (d₁ : Fin n₁ → ℤ) (d₂ : Fin n₂ → ℤ)
      (f₂ : ∐ (fun j ↦ 𝒪 (d₂ j)) ⟶ ∐ (fun j ↦ 𝒪 (d₁ j)))
      (f₁ : ∐ (fun j ↦ 𝒪 (d₁ j)) ⟶ ∐ (fun j ↦ 𝒪 (d₀ j)))
      (f₀ : ∐ (fun j ↦ 𝒪 (d₀ j)) ⟶ 𝒢),
      Mono f₂ ∧ Epi f₀ ∧ (ComposableArrows.mk₃ f₂ f₁ f₀).Exact :=
  sorry

/-- `Hom(𝒪(a), Ω¹_{ℙ¹_k/k}) ≅ 𝒪(-a - 2)`, since `Ω¹_{ℙ¹_k/k} ≅ 𝒪(-2)` is invertible and
`𝒪(a)ᵛ ≅ 𝒪(-a)`. -/
theorem nonempty_homObj_twist_iso (a : ℤ) :
    Nonempty (homObj (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) a)
        (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials ≅
      ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) (-a + -2)) := by
  obtain ⟨eω⟩ := nonempty_relativeDifferentials_iso_twist k
  have : (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials.IsInvertible :=
    IsInvertible.of_iso eω.symm
  obtain ⟨ed⟩ := ProjectiveSpace.nonempty_dual_twist_iso (ULift.{u} (Fin 2)) (Spec (.of k)) a
  obtain ⟨et⟩ := ProjectiveSpace.nonempty_tensorObj_twist_iso (ULift.{u} (Fin 2)) (Spec (.of k))
    (-a) (-2)
  exact ⟨(asIso (dualTensorHom _ _)).symm ≪≫ (ed ⊗ᵢ eω) ≪≫ et⟩

local notation3 "𝒪(" a ")" => ProjectiveSpace.twist (ULift (Fin 2)) (Spec (CommRingCat.of k)) a

local notation3 "ω" =>
  Scheme.Hom.relativeDifferentials (ProjectiveLine (Spec (CommRingCat.of k)) ↘
    Spec (CommRingCat.of k))

lemma finiteDimensional_homogeneousSubmodule (d : ℕ) :
    FiniteDimensional k (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) k d) :=
  Module.Finite.iff_fg.2 (MvPolynomial.homogeneousSubmodule_fg _ _ d)

lemma finrank_homogeneousSubmodule_zero :
    Module.finrank k (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) k 0) = 1 := by
  rw [Module.finrank_eq_nat_card_basis (ProjectiveSpace.homogeneousSubmoduleBasis _ k 0)]
  have : Unique {s : ULift.{u} (Fin 2) →₀ ℕ | s.degree = 0} :=
    ⟨⟨⟨0, by simp⟩⟩, fun s ↦ Subtype.ext ((Finsupp.degree_eq_zero_iff _).1 s.2)⟩
  exact Nat.card_unique

lemma finiteDimensional_H_zero_twist (b : ℤ) : FiniteDimensional k ((𝒪(b)).H 0) := by
  rcases lt_or_ge b 0 with hb | hb
  · have := subsingleton_H_zero_twist_of_neg k b hb
    infer_instance
  · rw [← Int.toNat_of_nonneg hb]
    obtain ⟨e⟩ := nonempty_H_zero_twist_equiv k b.toNat
    have := finiteDimensional_homogeneousSubmodule k b.toNat
    exact e.symm.finiteDimensional

lemma finiteDimensional_H_one_twist (a : ℤ) : FiniteDimensional k ((𝒪(a)).H 1) := by
  rcases lt_or_ge a (-1) with ha | ha
  · obtain ⟨e⟩ := nonempty_H_one_twist_equiv_dual k a (by omega)
    have := finiteDimensional_homogeneousSubmodule k (-a - 2).toNat
    exact e.symm.finiteDimensional
  · have := subsingleton_H_one_twist k a ha
    infer_instance

/-- `H⁰(ℙ¹_k, Hom(𝒪(a), Ω¹)) ≅ H⁰(ℙ¹_k, 𝒪(-a - 2))`. -/
noncomputable def homObjTwistHZeroLinearEquiv (a : ℤ) :
    H (homObj (𝒪(a)) ω) 0 ≃ₗ[k] (𝒪(-a + -2)).H 0 :=
  ((cohomologyFunctor k 0).mapIso (nonempty_homObj_twist_iso k a).some).toLinearEquiv

/-- **The dimension count for the twists.** `H⁰(ℙ¹_k, Hom(𝒪(a), Ω¹))` and `H¹(ℙ¹_k, 𝒪(a))^∨`
have the same dimension, `max(0, -a - 1)`. -/
lemma finrank_H_zero_homObj_twist (a : ℤ) :
    Module.finrank k (H (homObj (𝒪(a)) ω) 0) = Module.finrank k (Module.Dual k ((𝒪(a)).H 1)) := by
  have := finiteDimensional_H_one_twist k a
  rw [(homObjTwistHZeroLinearEquiv k a).finrank_eq, Subspace.dual_finrank_eq]
  rcases lt_or_ge a (-1) with ha | ha
  · obtain ⟨e⟩ := nonempty_H_one_twist_equiv_dual k a (by omega)
    have := finiteDimensional_homogeneousSubmodule k (-a - 2).toNat
    rw [e.finrank_eq, Subspace.dual_finrank_eq]
    have hb : -a + -2 = (((-a - 2).toNat : ℕ) : ℤ) := by omega
    rw [hb]
    obtain ⟨e'⟩ := nonempty_H_zero_twist_equiv k (-a - 2).toNat
    exact e'.finrank_eq
  · have := subsingleton_H_one_twist k a ha
    have := subsingleton_H_zero_twist_of_neg k (-a + -2) (by omega)
    rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton]

/-- **Duality on the projective line, `H¹`.** For coherent `𝒪_{ℙ¹_k}`-modules `𝒢`, there is an
isomorphism `H¹(ℙ¹_k, 𝒢)^∨ ≅ Hom(𝒢, Ω¹_{ℙ¹_k/k})`, natural in `𝒢`. For `𝒢 = 𝒪(d)` both sides
are computed by the Čech complex, `Ω¹_{ℙ¹_k/k} ≅ 𝒪(-2)` and the monomial pairing is perfect; for
general `𝒢` one uses a resolution by twists (`exists_exact_sigma_twist`), the vanishing of
`H²` and of `Ext²` on `ℙ¹_k`, and the four lemma `AddMonoidHom.bijective_of_exact_hexagon`.

(blueprint: `thm-sc-p1-duality`, first isomorphism) -/
theorem nonempty_dual_H_one_iso :
    Nonempty ((Scheme.Modules.isCoherent (ProjectiveLine (Spec (.of k)))).ι.op ⋙
        (Scheme.Modules.cohomologyFunctor k 1).op ⋙ ModuleCat.dualFunctor k ≅
      (Scheme.Modules.isCoherent (ProjectiveLine (Spec (.of k)))).ι.op ⋙
        (SheafOfModules.homFunctor (ProjectiveLine (Spec (.of k))).sheaf).flip.obj
          (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials ⋙
        Scheme.Modules.cohomologyFunctor k 0) :=
  sorry

/-- **Duality on the projective line, `H⁰`.** For a coherent `𝒪_{ℙ¹_k}`-module `𝒢`,
`H⁰(ℙ¹_k, 𝒢)^∨ ≅ Ext¹(𝒢, Ω¹_{ℙ¹_k/k})`. The proof is the one of `nonempty_dual_H_one_iso`, using
`Ext^i(𝒪(d), ω) ≅ H^i(ℙ¹_k, 𝒪(-d) ⊗ ω)` (`Scheme.Modules.nonempty_ext_addEquiv_H`).

(blueprint: `thm-sc-p1-duality`, second isomorphism) -/
theorem nonempty_dual_H_zero_addEquiv_ext [HasExt.{u} (ProjectiveLine (Spec (.of k))).Modules]
    (𝒢 : (ProjectiveLine (Spec (.of k))).Modules)
    [SheafOfModules.IsQuasicoherent (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf) 𝒢]
    [SheafOfModules.IsFinitePresentation (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf) 𝒢] :
    Nonempty (Module.Dual k (𝒢.H 0) ≃+
      Scheme.Modules.Ext 𝒢 (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials
        1) :=
  sorry

end ProjectiveLine

end AlgebraicGeometry
