/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-!
# Serre's theorems on the cohomology of projective schemes

This file states, for the Picard-framework block of the blueprint, the three results of
Serre's *Faisceaux algébriques cohérents* that the rest of the block uses: the computation of
the cohomology of the twisting sheaves on projective space, and Serre's theorems A and B for a
coherent sheaf on a closed subscheme of projective space.

Projective space is the project's relative projective space `ℙ(n; S)`, whose index type `n` is
the index type of the *homogeneous* coordinates, so that `ℙᵈ_k` is `ℙ(n; Spec k)` for a type
`n` with `Nat.card n = d + 1`.

## Implementation notes

There is no twisting sheaf anywhere in Mathlib or in the project, so
`AlgebraicGeometry.ProjectiveSpace.twist` is declared here as an `opaque` constant. Being
`opaque` rather than `sorry`-bodied it genuinely depends on `m`, so the four cohomology statements below say what
they should; but it satisfies no equations, so **none of them can be proved before it is
replaced**. The alternative, quantifying existentially over a family
`𝒪 : ℤ → (ℙ(n; S)).Modules` with `𝒪 0 ≅ 𝒪_X` and the four clauses, would be provable today;
it is not used here because the twist is also needed by Serre's theorems A and B, which are
about an arbitrary closed subscheme and would then have to carry the family as a parameter.

The symmetric power `Sᵐ(V)` of `V = k^{d+1}` is realised as the degree-`m` homogeneous part
`MvPolynomial.homogeneousSubmodule n k m` of the polynomial ring in the homogeneous
coordinates. Mathlib's `SymmetricPower R ι M` forces the index type `ι` to lie in the same
universe as the ring `R`, which does not fit `Sym^m` for a field in an arbitrary universe, and
the homogeneous part is anyway the object Serre's theorem produces.

Mathlib has no `IsCoherent` predicate for sheaves of modules; "coherent" is spelled here as
`SheafOfModules.IsFinitePresentation` together with `SheafOfModules.IsQuasicoherent`, which
agrees with coherence on a noetherian scheme such as a closed subscheme of `ℙᵈ_k`.

## Main definitions

- `AlgebraicGeometry.ProjectiveSpace.twist` — the twisting sheaf `𝒪(m)` on `ℙ(n; S)`
  (placeholder).

## Main statements

- `AlgebraicGeometry.ProjectiveSpace.nonempty_H_zero_twist_equiv`,
  `subsingleton_H_twist_of_ne`, `subsingleton_H_twist_top` and
  `nonempty_H_twist_top_equiv_dual` — the cohomology of `𝒪(m)` on `ℙᵈ_k`.
- `AlgebraicGeometry.Scheme.Modules.exists_subsingleton_H_tensor_twist` — Serre's theorem B.
- `AlgebraicGeometry.Scheme.Modules.exists_generatingSections_tensor_twist` — Serre's
  theorem A.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry.Scheme.Modules

noncomputable section

namespace AlgebraicGeometry

variable (n : Type u) (S : Scheme.{u})

/-- The twisting sheaf `𝒪(m)` on projective space.

Neither Mathlib nor the project has the twisting sheaves of a relative `Proj`, so this is an
`opaque` placeholder: it satisfies no equations, and no statement mentioning it can be proved
before it is replaced. -/
-- TODO(unify): sk-thm-picard-pn
opaque ProjectiveSpace.twist (m : ℤ) : (ℙ(n; S)).Modules := SheafOfModules.unit _

section Pn

/-- **`H⁰` of the twisting sheaves on `ℙᵈ_k`.** With `X = ℙᵈ_k` presented as `ℙ(n; Spec k)`
for an index type `n` of homogeneous coordinates with `Nat.card n = d + 1`, and `Sᵐ(V)` for
`V = k^{d+1}` the degree-`m` homogeneous part of the polynomial ring in those coordinates,
`H⁰(X, 𝒪(m)) = Sᵐ(V)` for `m ≥ 0`.

(blueprint: `sk-thm-picard-pn`) -/
theorem ProjectiveSpace.nonempty_H_zero_twist_equiv (k : Type u) [Field k] [Finite n] (d : ℕ)
    (hn : Nat.card n = d + 1) (m : ℕ) :
    Nonempty ((ProjectiveSpace.twist n (Spec (.of k)) m).H 0 ≃ₗ[k]
      MvPolynomial.homogeneousSubmodule n k m) :=
  sorry

/-- **Vanishing of the cohomology of the twisting sheaves in middle degrees.**
`H^q(ℙᵈ_k, 𝒪(m)) = 0` for every `m` and every `q ∉ {0, d}`.

(blueprint: `sk-thm-picard-pn`) -/
theorem ProjectiveSpace.subsingleton_H_twist_of_ne (k : Type u) [Field k] [Finite n] (d : ℕ)
    (hn : Nat.card n = d + 1) (q : ℕ) (m : ℤ) (hq0 : q ≠ 0) (hqd : q ≠ d) :
    Subsingleton ((ProjectiveSpace.twist n (Spec (.of k)) m).H q) :=
  sorry

/-- **Vanishing of the top cohomology of the twisting sheaves.**
`H^d(ℙᵈ_k, 𝒪(m)) = 0` for `m ≥ -d`.

(blueprint: `sk-thm-picard-pn`) -/
theorem ProjectiveSpace.subsingleton_H_twist_top (k : Type u) [Field k] [Finite n] (d : ℕ)
    (hn : Nat.card n = d + 1) (m : ℤ) (hm : -(d : ℤ) ≤ m) :
    Subsingleton ((ProjectiveSpace.twist n (Spec (.of k)) m).H d) :=
  sorry

/-- **The top cohomology of the twisting sheaves.**
`H^d(ℙᵈ_k, 𝒪(m)) = S^{-m-d-1}(V)^∨` for `m ≤ -d-1`. Taking `m = -d-1` exhibits `𝒪(-d-1)` as
the dualising sheaf of `ℙᵈ_k`.

(blueprint: `sk-thm-picard-pn`) -/
theorem ProjectiveSpace.nonempty_H_twist_top_equiv_dual (k : Type u) [Field k] [Finite n]
    (d : ℕ) (hn : Nat.card n = d + 1) (m : ℤ) (hm : m ≤ -(d : ℤ) - 1) :
    Nonempty ((ProjectiveSpace.twist n (Spec (.of k)) m).H d ≃ₗ[k]
      Module.Dual k (MvPolynomial.homogeneousSubmodule n k (-m - d - 1).toNat)) :=
  sorry

end Pn

variable {n} {X : Scheme.{u}} (k : Type u) [Field k]

/-- The restriction `𝒪_X(m)` to a closed subscheme `i : X ⟶ ℙ(n; Spec k)` of the twisting
sheaf on projective space, i.e. its pullback along `i`. -/
abbrev ProjectiveSpace.twistRestrict (i : X ⟶ ℙ(n; Spec (.of k))) (m : ℤ) :
    X.Modules :=
  (Scheme.Modules.pullback i).obj (ProjectiveSpace.twist n (Spec (.of k)) m)

/-- **Serre's theorem B: vanishing after a twist.** Let `X ⊆ ℙᵈ_k` be a closed subscheme, i.e. a
closed immersion `i : X ⟶ ℙ(n; Spec k)`, and let `ℱ` be a coherent sheaf on `X`. Then
`H^q(X, ℱ ⊗ 𝒪_X(m)) = 0` for all `q > 0` and all `m ≫ 0`, where `𝒪_X(m)` is the pullback along
`i` of the twisting sheaf `𝒪(m)`.

Mathlib has no `IsCoherent` predicate, so "coherent" is spelled as
`SheafOfModules.IsFinitePresentation` together with `SheafOfModules.IsQuasicoherent`; on the
noetherian scheme `X` these two conditions together are coherence.

(blueprint: `sk-thm-picard-serre-b`) -/
theorem Scheme.Modules.exists_subsingleton_H_tensor_twist [Finite n]
    (i : X ⟶ ℙ(n; Spec (.of k))) [IsClosedImmersion i] (F : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) F] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q : ℕ, 0 < q →
      Subsingleton ((F ⊗ ProjectiveSpace.twistRestrict k i m).H q) :=
  sorry

/-- **Serre's theorem A: global generation after a twist.** Let `X ⊆ ℙᵈ_k` be a closed
subscheme, i.e. a closed immersion `i : X ⟶ ℙ(n; Spec k)`, and let `ℱ` be a coherent sheaf on
`X`. Then `ℱ ⊗ 𝒪_X(m)` is generated by its global sections for all `m ≫ 0`.

"Generated by its global sections" is `Nonempty (SheafOfModules.GeneratingSections _)`: the
sections `σ.s : σ.I → M.sections` of a `GeneratingSections` are by construction global
sections of `M`, and `σ.π : free σ.I ⟶ M` being an epimorphism is exactly the statement that
the map from the free module on those global sections is surjective as a map of sheaves.

As for theorem B, "coherent" is `SheafOfModules.IsFinitePresentation` together with
`SheafOfModules.IsQuasicoherent`.

(blueprint: `sk-thm-picard-serre-a`) -/
theorem Scheme.Modules.exists_generatingSections_tensor_twist [Finite n]
    (i : X ⟶ ℙ(n; Spec (.of k))) [IsClosedImmersion i] (F : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) F] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀,
      Nonempty (SheafOfModules.GeneratingSections (F ⊗ ProjectiveSpace.twistRestrict k i m)) :=
  sorry

end AlgebraicGeometry
