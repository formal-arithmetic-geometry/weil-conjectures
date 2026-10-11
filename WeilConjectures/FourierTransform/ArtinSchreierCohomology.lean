/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.FourierTransform.ArtinSchreier
public import WeilConjectures.SixFunctors.Finite.GlobalSections

/-!

# Cohomology of the affine line with coefficients in an Artin–Schreier sheaf

Let `k` be a finite field with `q` elements, `Ω` an algebraically closed field containing `k`,
`Λ` a finite coefficient ring in which `q` is invertible, and `Ψ` a primitive additive
character of `k` with values in `Λ`. On the affine line `𝔸¹_Ω`, viewed as a `k`-scheme, the
Artin–Schreier sheaf `ℒ_{Ψ, a x}` of the linear function `x ↦ a x` has no cohomology at all
when `a ≠ 0`, while for `a = 0` it is the constant sheaf, whose cohomology is `Λ` in degree
`0` and vanishes in the other degrees.

## Main statements

- `AlgebraicGeometry.Etale.cohomology_affineLine_unit`: `H^0(𝔸¹_Ω, Λ) ≅ Λ` and
  `H^q(𝔸¹_Ω, Λ) = 0` for `q ≠ 0`.
- `AlgebraicGeometry.Etale.isZero_cohomology_affineLine_artinSchreierSheafOf`: for `a ≠ 0`,
  `H^q(𝔸¹_Ω, ℒ_{Ψ, a x}) = 0` for every `q`.
- `AlgebraicGeometry.Etale.cohomology_affineLine_artinSchreierSheafOf`: the cohomology of
  `ℒ_{Ψ, a x}` on `𝔸¹_Ω` for every `a`.

## Implementation notes

The cohomology `H^q(X, F)` of an étale sheaf `F` of `Λ`-modules is
`AlgebraicGeometry.Etale.cohomology` applied to `F` placed in degree `0`, the `q`-th cohomology
of the derived global sections `RΓ(X, F)`.
The blueprint works with `ℚ̄_ℓ`-coefficients; here the coefficients are a finite domain `Λ` in
which `q` is invertible, a finite level of the `ℓ`-adic coefficients.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The affine line `𝔸¹_Ω` over a field extension `Ω` of `k`, as a `k`-scheme. -/
@[instance_reducible]
def affineLineOverOfAlgebra (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] :
    (𝔸(PUnit; Spec (CommRingCat.of Ω))).Over (Spec (.of k)) :=
  ⟨𝔸(PUnit; Spec (CommRingCat.of Ω)) ↘ Spec (.of Ω) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k Ω))⟩

variable (Λ) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

/-- **Constant cohomology of the affine line.** For an algebraically closed field `Ω` of
characteristic `p` and a finite coefficient ring `Λ` in which `p` is invertible,
`H^0(𝔸¹_Ω, Λ) ≅ Λ` and `H^q(𝔸¹_Ω, Λ) = 0` for `q ≠ 0`: the affine line is connected, its
cohomological dimension is one, and `H^1(𝔸¹_Ω, ℤ/n) ≅ Pic(𝔸¹_Ω)[n] = 0` for `n` prime to `p`.
(blueprint: `lem-fd-affine-line-constant-cohomology`) -/
theorem cohomology_affineLine_unit [Finite Λ] (p : ℕ) [CharP Ω p] [Invertible (p : Λ)] :
    Nonempty ((cohomology (ModuleCat.{u + 1} Λ) 𝔸(PUnit; Spec (CommRingCat.of Ω)) 0).obj
        ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _)) ≅ ModuleCat.of Λ Λ) ∧
      ∀ q : ℤ, q ≠ 0 →
        IsZero ((cohomology (ModuleCat.{u + 1} Λ) 𝔸(PUnit; Spec (CommRingCat.of Ω)) q).obj
          ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _))) :=
  -- `H^0` is `Λ` as `𝔸¹_Ω` is connected; `H^q = 0` for `q ≥ 2` by the cohomological dimension
  -- of an affine curve (`sbc-thm-cohomological-dimension-of-an-affine-curve`); and
  -- `H^1 = 0` by the Kummer sequence (`thm-sc-affine-cohomology`), the units of `Ω[x]` being
  -- divisible and `Pic(𝔸¹_Ω) = 0` (`lem-sc-pic-affine`). The étale cohomology of the affine
  -- line with coefficients in `Λ`-modules is not yet connected to these statements, which are
  -- about the constant sheaves `ℤ/n` of abelian groups.
  sorry

variable {k : Type u} [Field k] [Fintype k] [Algebra k Ω] [Invertible (Fintype.card k : Λ)]

attribute [local instance] affineLineOverOfAlgebra

/-- The linear function `x ↦ a x` on `𝔸¹_Ω`, for `a ∈ k`. -/
abbrev affineLineLinearFunction (a : k) : Γ(𝔸(PUnit; Spec (CommRingCat.of Ω)), ⊤) :=
  (𝔸(PUnit; Spec (CommRingCat.of Ω)) ↘ Spec (.of Ω)).appTop
      ((Scheme.ΓSpecIso (.of Ω)).inv.hom (algebraMap k Ω a)) *
    AffineSpace.coord _ PUnit.unit

/-- **Vanishing of the cohomology of a nontrivial Artin–Schreier sheaf on the affine line.**
For a primitive additive character `Ψ` of `k` with values in a finite domain `Λ` and `a ≠ 0`,
`H^q(𝔸¹_Ω, ℒ_{Ψ, a x}) = 0` for every `q`. The scaling `x ↦ a x` identifies `ℒ_{Ψ, a x}` with
`ℒ_{Ψ(a ·), x}`, and `Ψ(a ·)` is a nontrivial character; by the finite pushforward along the
Artin–Schreier covering `y ↦ y ^ q - y` and the isotypic decomposition, the cohomology of
`𝔸¹_Ω` with constant coefficients is the direct sum of the cohomology of the `ℒ_{Ψ(b ·), x}`,
and only the trivial character contributes, in degree `0`. -/
theorem isZero_cohomology_affineLine_artinSchreierSheafOf [IsDomain Λ] [Finite Λ]
    (Ψ : AddChar k Λ) (hΨ : Ψ.IsPrimitive) {a : k} (ha : a ≠ 0) (q : ℤ) :
    IsZero ((cohomology (ModuleCat.{u + 1} Λ) 𝔸(PUnit; Spec (CommRingCat.of Ω)) q).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        (artinSchreierSheafOf _ Ψ (affineLineLinearFunction a)))) :=
  sorry

/-- **Cohomology of an affine line with an exponential sheaf.** Let `Ψ` be a primitive additive
character of `k` with values in a finite domain `Λ`, and `a ∈ k`. On `𝔸¹_Ω`,
`H^q(𝔸¹_Ω, ℒ_{Ψ, a x})` is `Λ` for `q = 0` and `a = 0`, and vanishes otherwise.
(blueprint: `lem-fd-cohomology-affine-line-character`) -/
theorem cohomology_affineLine_artinSchreierSheafOf [IsDomain Λ] [Finite Λ] (Ψ : AddChar k Λ)
    (hΨ : Ψ.IsPrimitive) (a : k) :
    (a ≠ 0 → ∀ q, IsZero ((cohomology (ModuleCat.{u + 1} Λ) 𝔸(PUnit; Spec (CommRingCat.of Ω))
      q).obj ((DerivedCategory.singleFunctor _ 0).obj
        (artinSchreierSheafOf _ Ψ (affineLineLinearFunction a))))) ∧
    (a = 0 → Nonempty ((cohomology (ModuleCat.{u + 1} Λ) 𝔸(PUnit; Spec (CommRingCat.of Ω))
        0).obj ((DerivedCategory.singleFunctor _ 0).obj
          (artinSchreierSheafOf _ Ψ (affineLineLinearFunction a))) ≅ ModuleCat.of Λ Λ) ∧
      ∀ q : ℤ, q ≠ 0 → IsZero ((cohomology (ModuleCat.{u + 1} Λ)
        𝔸(PUnit; Spec (CommRingCat.of Ω)) q).obj ((DerivedCategory.singleFunctor _ 0).obj
          (artinSchreierSheafOf _ Ψ (affineLineLinearFunction a))))) := by
  refine ⟨fun ha q ↦ isZero_cohomology_affineLine_artinSchreierSheafOf Λ Ψ hΨ ha q,
    fun ha ↦ ?_⟩
  subst ha
  -- `ℒ_{Ψ, 0} ≅ Λ`, and the characteristic of `Ω` is that of `k`, invertible in `Λ`
  rw [show affineLineLinearFunction (Ω := Ω) (0 : k) = 0 by simp]
  obtain ⟨e⟩ := nonempty_iso_artinSchreierSheafOf_zero 𝔸(PUnit; Spec (CommRingCat.of Ω)) Ψ
  obtain ⟨m, hp, hm⟩ := FiniteField.card k (ringChar k)
  have := Fact.mk hp
  have : CharP Ω (ringChar k) := charP_of_injective_algebraMap (algebraMap k Ω).injective _
  have hu : IsUnit ((ringChar k : Λ) ^ (m : ℕ)) := by
    rw [← Nat.cast_pow, ← hm]
    exact isUnit_of_invertible _
  let : Invertible (ringChar k : Λ) := ((isUnit_pow_iff m.ne_zero).mp hu).invertible
  obtain ⟨⟨e₀⟩, hq⟩ := cohomology_affineLine_unit (Ω := Ω) Λ (ringChar k)
  let E (q : ℤ) := (cohomology (ModuleCat.{u + 1} Λ) _ q).mapIso
    ((DerivedCategory.singleFunctor _ 0).mapIso e)
  exact ⟨⟨(E 0) ≪≫ e₀⟩, fun q hq0 ↦ (hq q hq0).of_iso (E q)⟩

end AlgebraicGeometry.Etale
