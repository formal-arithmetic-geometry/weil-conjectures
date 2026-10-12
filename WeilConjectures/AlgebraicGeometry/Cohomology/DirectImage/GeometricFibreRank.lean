/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.Constructible
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.BaseChange
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Semicontinuity
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-!
# Constructibility of the geometric fibre dimensions of a flat coherent module

Let `f : X ⟶ S` be projective with Noetherian base and `𝒢` a coherent `𝒪_X`-module flat over
`S`. For every `r`, the function `s ↦ dim_{κ(s̄)} H^r(X_{s̄}, 𝒢_{s̄})` on `S` takes finitely many
values, each on a constructible subset (`lem-fin-projective-flat-coherent-ranks`).

The geometric fibre dimension is the fibre dimension over the residue field
(`AlgebraicGeometry.Scheme.Modules.hFiber_pullback_of_isPullback`), which is upper
semicontinuous (`AlgebraicGeometry.Scheme.Modules.upperSemicontinuous_hFiber`); on a Noetherian
space an upper semicontinuous function is bounded and its level sets are locally closed.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.finite_range_and_isConstructible_finrankH_geometricFibre`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {X S : Scheme.{u}}

/-- The geometric point `Spec κ(s)‾ ⟶ S` over a point `s` of `S`, for the algebraic closure
`κ(s)‾` of the residue field. -/
noncomputable abbrev geometricPointAt (S : Scheme.{u}) (s : S) :
    Spec (.of (AlgebraicClosure (S.residueField s))) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s)
    (AlgebraicClosure (S.residueField s)))) ≫ S.fromSpecResidueField s

/-- Blueprint `lem-fin-projective-flat-coherent-ranks`: Constructible dimensions from coherent
base change.

Let `f : X ⟶ S` be projective (`f = π ∘ i` for a closed immersion `i : X ⟶ ℙ(n; S)`) with `S`
Noetherian, and let `𝒢` be a coherent `𝒪_X`-module flat over `S`. For each `r`, the function
`s ↦ dim_{κ(s̄)} H^r(X_{s̄}, 𝒢_{s̄})`, for the geometric fibre `X_{s̄} = X ×_S Spec κ(s)‾`,
is constructible: it takes finitely many values, each on a constructible subset of `S`. -/
theorem Modules.finite_range_and_isConstructible_finrankH_geometricFibre [IsNoetherian S]
    (f : X ⟶ S)
    {n : Type u} [Finite n] (i : X ⟶ ℙ(n; S)) [IsClosedImmersion i] (hi : i ≫ ℙ(n; S) ↘ S = f)
    (𝒢 : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) 𝒢]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) 𝒢] (h𝒢 : 𝒢.IsFlatOver f)
    (r : ℕ) :
    let φ : S → ℕ := fun s ↦
      letI : (Limits.pullback f (S.geometricPointAt s)).Over
          (Spec (.of (AlgebraicClosure (S.residueField s)))) := ⟨pullback.snd _ _⟩
      ((Modules.pullback (pullback.fst f (S.geometricPointAt s))).obj 𝒢).finrankH
        (AlgebraicClosure (S.residueField s)) r
    (Set.range φ).Finite ∧ ∀ m : ℕ, Topology.IsConstructible (φ ⁻¹' {m}) := by
  sorry

end AlgebraicGeometry.Scheme
