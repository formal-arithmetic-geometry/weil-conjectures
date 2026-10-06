/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearProjection
public import WeilConjectures.RingTheory.GradedAlgebra.LinearPair

/-!
# Finite projections of projective curves to the projective line

Let `k` be an infinite field and `X` an integral closed subscheme of a projective space over
`k` of dimension one. Then there is a finite morphism `X ⟶ ℙ¹_k` over `k`.

The proof goes through the homogeneous coordinate ring: `X ≅ Proj S` for a standard graded
`k`-algebra `S` which is a domain; since `Proj S` has dimension one, there are linear forms
`l₀, l₁ ∈ S₁` without common zero on `Proj S`, and the linear projection
`π_{l₀,l₁} : Proj S ⟶ ℙ¹_k` is finite.

## Main statements

- `AlgebraicGeometry.exists_isStandard_iso_proj` — the homogeneous coordinate ring of an
  integral closed subscheme of projective space.
- `AlgebraicGeometry.exists_isFinite_toProjectiveLine` — a projective curve over an infinite
  field admits a finite morphism to `ℙ¹_k`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- **The homogeneous coordinate model**: an integral closed subscheme `X` of `ℙ(n; Spec k)`
is, over `k`, isomorphic to `Proj S` for a standard graded `k`-algebra `S` which is a domain,
namely the quotient of the polynomial ring by the homogeneous ideal of `X`
(blueprint: `lem-pc-projective-coordinate-model`). -/
theorem exists_isStandard_iso_proj {k : Type u} [Field k] {n : Type u} [Finite n]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsIntegral X] (i : X ⟶ ℙ(n; Spec (.of k)))
    [IsClosedImmersion i] [i.IsOver (Spec (.of k))] :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra k S) (𝒜 : ℕ → Submodule k S)
      (_ : GradedAlgebra 𝒜), GradedAlgebra.IsStandard 𝒜 ∧ IsDomain S ∧
        ∃ e : X ≅ Proj 𝒜, e.hom ≫ Proj.toSpecBase 𝒜 = X ↘ Spec (.of k) :=
  sorry

/-- **A projective curve admits a finite morphism to the projective line**: if `k` is an
infinite field and `X` is an integral closed subscheme of `ℙ(n; Spec k)` of dimension one,
then there is a finite morphism `X ⟶ ℙ¹_k` over `k`. Writing `X ≅ Proj S` with `S` a
standard graded domain, it is the linear projection `π_{l₀,l₁}` for linear forms
`l₀, l₁ ∈ S₁` without common zero
(blueprint: `lem-pc-projective-curve-finite-projection`). -/
theorem exists_isFinite_toProjectiveLine {k : Type u} [Field k] [Infinite k] {n : Type u}
    [Finite n] (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsIntegral X]
    (i : X ⟶ ℙ(n; Spec (.of k))) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
    (hdim : topologicalKrullDim X = 1) :
    ∃ π : X ⟶ ProjectiveLine (Spec (.of k)),
      IsFinite π ∧ π ≫ ProjectiveLine (Spec (.of k)) ↘ Spec (.of k) = X ↘ Spec (.of k) := by
  obtain ⟨S, _, _, 𝒜, _, hstd, _, e, he⟩ := exists_isStandard_iso_proj X i
  have hdim' : topologicalKrullDim (ProjectiveSpectrum 𝒜) = 1 :=
    (IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph).symm.trans hdim
  obtain ⟨l₀, h₀, l₁, h₁, hcov⟩ := GradedAlgebra.IsStandard.exists_basicOpen_sup_eq_top hdim'
  have := Proj.isFinite_linearPairProjection h₀ h₁ hcov
  refine ⟨e.hom ≫ Proj.linearPairProjection h₀ h₁ hcov, inferInstance, ?_⟩
  rw [Category.assoc, Proj.linearPairProjection_over, he]

end AlgebraicGeometry
