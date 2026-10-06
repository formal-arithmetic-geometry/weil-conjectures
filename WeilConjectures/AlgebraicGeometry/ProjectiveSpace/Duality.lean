/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ExactSequence
public import WeilConjectures.AlgebraicGeometry.Modules.Coherent
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

open CategoryTheory Limits Opposite

open scoped AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry

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
