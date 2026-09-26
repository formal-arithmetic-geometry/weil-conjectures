/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.Operations
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

@[expose] public section

/-!
# Serre's theorems on the cohomology of projective schemes

This file states, for the Picard-framework block of the blueprint, the three results of
Serre's *Faisceaux algébriques cohérents* that the rest of the block uses: the computation of
the cohomology of the twisting sheaves on projective space, and Serre's theorems A and B for a
coherent sheaf on a closed subscheme of projective space.

Projective space is the project's relative projective space `ℙ(n; S)`, whose index type `n` is
the index type of the *homogeneous* coordinates, so that `ℙᵈ_k` is `ℙ(n; Spec k)` for a type
`n` with `Nat.card n = d + 1`. There is no twisting sheaf anywhere in Mathlib or in the
project, so a placeholder `ProjectiveSpace.twist` is introduced here and used by all three
statements.

## Main definitions

- `AlgebraicGeometry.ProjectiveSpace.twist` — the twisting sheaf `𝒪(m)` on `ℙ(n; S)`
  (placeholder, `sorry`).

## Main statements

- `AlgebraicGeometry.ProjectiveSpace.cohomology_twist` — the cohomology of `𝒪(m)` on `ℙᵈ_k`.
- `AlgebraicGeometry.Scheme.Modules.exists_subsingleton_H_tensor_twist` — Serre's theorem B.
- `AlgebraicGeometry.Scheme.Modules.exists_generatingSections_tensor_twist` — Serre's
  theorem A.

## Implementation notes

The symmetric power `Sᵐ(V)` of `V = k^{d+1}` is realised as the degree-`m` homogeneous part
`MvPolynomial.homogeneousSubmodule n k m` of the polynomial ring in the homogeneous
coordinates. Mathlib's `SymmetricPower R ι M` forces the index type `ι` to lie in the same
universe as the ring `R`, which does not fit `Sym^m` for a field in an arbitrary universe, and
the homogeneous part is anyway the object Serre's theorem produces.

Mathlib has no `IsCoherent` predicate for sheaves of modules; "coherent" is spelled here as
`SheafOfModules.IsFinitePresentation` together with `SheafOfModules.IsQuasicoherent`, which
agrees with coherence on a noetherian scheme such as a closed subscheme of `ℙᵈ_k`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry.Scheme.Modules

noncomputable section

namespace AlgebraicGeometry

variable (n : Type u) (S : Scheme.{u})

-- TODO(unify): sk-thm-picard-pn
/-- The twisting sheaf `𝒪(m)` on projective space. Placeholder: neither Mathlib nor the
project has the twisting sheaves of a relative `Proj`. -/
noncomputable def ProjectiveSpace.twist (m : ℤ) : (ℙ(n; S)).Modules := sorry

/-- Blueprint `sk-thm-picard-pn`: Cohomology of `ℙⁿ`, Serre 1954.

Let `k` be a field and let `X = ℙᵈ_k`, presented as `ℙ(n; Spec k)` for an index type `n` of
homogeneous coordinates with `Nat.card n = d + 1`. Write `𝒪(m)` for the twisting sheaf and
`Sᵐ(V)`, for `V = k^{d+1}`, for the degree-`m` homogeneous part of the polynomial ring in the
homogeneous coordinates. Then

* `H⁰(X, 𝒪(m)) = Sᵐ(V)` for `m ≥ 0`;
* `Hq(X, 𝒪(m)) = 0` for `q ∉ {0, d}`;
* `H^d(X, 𝒪(m)) = 0` for `m ≥ -d`;
* `H^d(X, 𝒪(m)) = S^{-m-d-1}(V)^∨` for `m ≤ -d-1`.

In particular the dualising sheaf is `ω_X = 𝒪(-d-1)`, which is the `m = -d-1` case of the
last clause, and `H^q(X, 𝒪_X) = k · δ_{q,0}`, which is the `m = 0` case of the first three.
Neither consequence is stated separately: there is no dualising sheaf in the project. -/
theorem ProjectiveSpace.cohomology_twist (k : Type u) [Field k] [Finite n] (d : ℕ)
    (hn : Nat.card n = d + 1) :
    (∀ m : ℕ, Nonempty ((ProjectiveSpace.twist n (Spec (.of k)) m).H 0 ≃ₗ[k]
        MvPolynomial.homogeneousSubmodule n k m)) ∧
      (∀ (q : ℕ) (m : ℤ), q ≠ 0 → q ≠ d →
        Subsingleton ((ProjectiveSpace.twist n (Spec (.of k)) m).H q)) ∧
      (∀ m : ℤ, -(d : ℤ) ≤ m →
        Subsingleton ((ProjectiveSpace.twist n (Spec (.of k)) m).H d)) ∧
      (∀ m : ℤ, m ≤ -(d : ℤ) - 1 →
        Nonempty ((ProjectiveSpace.twist n (Spec (.of k)) m).H d ≃ₗ[k]
          Module.Dual k (MvPolynomial.homogeneousSubmodule n k (-m - d - 1).toNat))) :=
  sorry

variable {n} {X : Scheme.{u}} (k : Type u) [Field k]

/-- The restriction `𝒪_X(m)` to a closed subscheme `i : X ⟶ ℙ(n; Spec k)` of the twisting
sheaf on projective space, i.e. its pullback along `i`. -/
noncomputable abbrev ProjectiveSpace.twistRestrict (i : X ⟶ ℙ(n; Spec (.of k))) (m : ℤ) :
    X.Modules :=
  (Scheme.Modules.pullback i).obj (ProjectiveSpace.twist n (Spec (.of k)) m)

open scoped AlgebraicGeometry.Scheme.Modules in
/-- Blueprint `sk-thm-picard-serre-b`: Serre's theorem B: vanishing after a twist.

Let `X ⊆ ℙᵈ_k` be a closed subscheme, i.e. a closed immersion `i : X ⟶ ℙ(n; Spec k)`, and let
`ℱ` be a coherent sheaf on `X`. Then `H^q(X, ℱ ⊗ 𝒪_X(m)) = 0` for all `q > 0` and all
`m ≫ 0`, where `𝒪_X(m)` is the pullback along `i` of the twisting sheaf `𝒪(m)`.

Mathlib has no `IsCoherent` predicate, so "coherent" is spelled as
`SheafOfModules.IsFinitePresentation` together with `SheafOfModules.IsQuasicoherent`; on the
noetherian scheme `X` these two conditions together are coherence. -/
theorem Scheme.Modules.exists_subsingleton_H_tensor_twist [Finite n]
    (i : X ⟶ ℙ(n; Spec (.of k))) [IsClosedImmersion i] (F : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) F] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q : ℕ, 0 < q →
      Subsingleton ((F ⊗ₘ ProjectiveSpace.twistRestrict k i m).H q) :=
  sorry

open scoped AlgebraicGeometry.Scheme.Modules in
/-- Blueprint `sk-thm-picard-serre-a`: Serre's theorem A: global generation after a twist.

Let `X ⊆ ℙᵈ_k` be a closed subscheme, i.e. a closed immersion `i : X ⟶ ℙ(n; Spec k)`, and let
`ℱ` be a coherent sheaf on `X`. Then `ℱ ⊗ 𝒪_X(m)` is generated by its global sections for all
`m ≫ 0`.

"Generated by its global sections" is `Nonempty (SheafOfModules.GeneratingSections _)`: the
sections `σ.s : σ.I → M.sections` of a `GeneratingSections` are by construction global
sections of `M`, and `σ.π : free σ.I ⟶ M` being an epimorphism is exactly the statement that
the map from the free module on those global sections is surjective as a map of sheaves.

As for theorem B, "coherent" is `SheafOfModules.IsFinitePresentation` together with
`SheafOfModules.IsQuasicoherent`. -/
theorem Scheme.Modules.exists_generatingSections_tensor_twist [Finite n]
    (i : X ⟶ ℙ(n; Spec (.of k))) [IsClosedImmersion i] (F : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) F] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀,
      Nonempty (SheafOfModules.GeneratingSections (F ⊗ₘ ProjectiveSpace.twistRestrict k i m)) :=
  sorry

end AlgebraicGeometry
