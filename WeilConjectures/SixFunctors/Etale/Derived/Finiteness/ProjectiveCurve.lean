/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.GeometricFibreRank
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage

/-!
# Constant coefficients on projective families of curves

Let `f : X ⟶ S` be a projective morphism of finite-type schemes over a field whose geometric
fibres have dimension at most one. The higher direct images `Rᵠf_* M` of a constant sheaf with
finite value `M` of order invertible on `S` are constructible. This is the curve case of the
constructibility of proper direct images (`thm-fin-projective-line-constructible`).

The case of a smooth projective family of curves comes first: there the stalks of `Rᵠf_* 𝔽_ℓ`
are the cohomology groups of the geometric fibres, whose cardinalities `ℓ^c`, `ℓ^{2g}`, `ℓ^c`
are constructible functions of the base point by coherent base change
(`lem-fin-projective-curve-betti-cardinalities`, `thm-fin-projective-smooth-curve-finiteness`).
The general case is reduced to it by a generic curve model
(`lem-fin-generic-curve-model`), Noetherian induction and a filtration of `M`
(`thm-fin-projective-curve-constant`, `cor-fin-projective-curve-finite-group`).

## Main statements

- `AlgebraicGeometry.Etale.natCard_sheafH_constantZMod_geometricFibre`
- `AlgebraicGeometry.Etale.isConstructibleSheaf_homology_rightDerivedLowerStar_of_smooth`
- `AlgebraicGeometry.Etale.isConstructibleSheaf_homology_rightDerivedLowerStar_zmod`
- `AlgebraicGeometry.Etale.isConstructibleSheaf_homology_rightDerivedLowerStar_constantSheaf`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {X S : Scheme.{u}}

/-- Blueprint `lem-fin-projective-curve-betti-cardinalities`: Betti cardinalities in a smooth
projective curve family.

Let `S` be Noetherian, `f : X ⟶ S` smooth of relative dimension one and projective
(`f = π ∘ i` for a closed immersion `i : X ⟶ ℙ(n; S)`), and `ℓ` a prime invertible on `S`. For a
point `s` of `S` let `X_{s̄} = X ×_S Spec κ(s)‾` be the geometric fibre, `c_s` the number of its
connected components and `g_s = dim H¹(X_{s̄}, 𝒪)` its arithmetic genus, which is the sum of the
genera of its connected components (each an integral smooth proper curve). Then
`|H⁰(X_{s̄}, 𝔽_ℓ)| = |H²(X_{s̄}, 𝔽_ℓ)| = ℓ^{c_s}`, `|H¹(X_{s̄}, 𝔽_ℓ)| = ℓ^{2 g_s}` and
`|Hʳ(X_{s̄}, 𝔽_ℓ)| = 1` for `r > 2`, and `c` and `g` are constructible functions on `S`: they
take finitely many values, each on a constructible subset. -/
theorem natCard_sheafH_constantZMod_geometricFibre [IsNoetherian S] (f : X ⟶ S)
    [SmoothOfRelativeDimension 1 f] {n : Type u} [Finite n] (i : X ⟶ ℙ(n; S))
    [IsClosedImmersion i] (hi : i ≫ ℙ(n; S) ↘ S = f) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : IsUnit (ℓ : Γ(S, ⊤))) :
    let Xs : S → Scheme.{u} := fun s ↦ Limits.pullback f (S.geometricPointAt s)
    let c : S → ℕ := fun s ↦ Nat.card (_root_.ConnectedComponents (Xs s))
    let g : S → ℕ := fun s ↦
      letI : (Xs s).Over (Spec (.of (AlgebraicClosure (S.residueField s)))) :=
        ⟨pullback.snd f (S.geometricPointAt s)⟩
      arithmeticGenus (AlgebraicClosure (S.residueField s)) (Xs s)
    (∀ s : S,
      Nat.card (Sheaf.H ((Xs s).constantZMod ℓ) 0) = ℓ ^ c s ∧
      Nat.card (Sheaf.H ((Xs s).constantZMod ℓ) 1) = ℓ ^ (2 * g s) ∧
      Nat.card (Sheaf.H ((Xs s).constantZMod ℓ) 2) = ℓ ^ c s ∧
      ∀ r, 2 < r → Nat.card (Sheaf.H ((Xs s).constantZMod ℓ) r) = 1) ∧
    ((Set.range c).Finite ∧ ∀ m : ℕ, Topology.IsConstructible (c ⁻¹' {m})) ∧
    ((Set.range g).Finite ∧ ∀ m : ℕ, Topology.IsConstructible (g ⁻¹' {m})) := by
  sorry

/-- Blueprint `thm-fin-projective-smooth-curve-finiteness`: Constant-coefficient finiteness for
projective smooth curves.

Let `S` be Noetherian, `f : X ⟶ S` projective and smooth of relative dimension one, and `ℓ` a
prime invertible on `S`. Every higher direct image `Rʳf_* 𝔽_ℓ` is constructible. -/
theorem isConstructibleSheaf_homology_rightDerivedLowerStar_of_smooth [IsNoetherian S]
    (f : X ⟶ S) [SmoothOfRelativeDimension 1 f] {n : Type u} [Finite n] (i : X ⟶ ℙ(n; S))
    [IsClosedImmersion i] (hi : i ≫ ℙ(n; S) ↘ S = f) (ℓ : ℕ) [Fact ℓ.Prime]
    [HasInvertibleExponent (ULift.{u + 1} (ZMod ℓ)) S] (r : ℤ) :
    IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ r).obj
      ((R((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
            (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ))))))) := by
  sorry

variable {k : Type u} [Field k]

/-- Blueprint `thm-fin-projective-curve-constant`: Constant coefficients on projective families
of dimension at most one.

Let `f : X ⟶ S` be projective (`f = π ∘ i` for a closed immersion `i : X ⟶ ℙ(n; S)`), with `S`
of finite type over a field `k`, such that every geometric fibre `X ×_S Spec Ω` has dimension at
most one, and let `ℓ` be a prime invertible on `S`. Every higher direct image `Rᵠf_* 𝔽_ℓ` is
constructible. -/
theorem isConstructibleSheaf_homology_rightDerivedLowerStar_zmod (aS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] (f : X ⟶ S) {n : Type u} [Finite n]
    (i : X ⟶ ℙ(n; S)) [IsClosedImmersion i] (hi : i ≫ ℙ(n; S) ↘ S = f)
    (hf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ 1)
    (ℓ : ℕ) [Fact ℓ.Prime] [HasInvertibleExponent (ULift.{u + 1} (ZMod ℓ)) S] (q : ℤ) :
    IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
            (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ))))))) := by
  sorry

/-- Blueprint `cor-fin-projective-curve-finite-group`: Finite constant groups on projective
curve families.

Let `f : X ⟶ S` be projective, with `S` of finite type over a field `k`, such that every
geometric fibre has dimension at most one. Let `Λ` be a finite ring whose exponent is invertible
on `S` and `M` a finite `Λ`-module. Every higher direct image `Rᵠf_* M` of the constant sheaf
`M` is constructible.

The blueprint states this for a finite abelian group `M` of order invertible on `S`, i.e. for
`Λ = ℤ/N` with `N = |M|`; the statement for finite modules over a finite ring is what the
constructibility of `Rπ_*` on `ℙ¹_S` (`thm-fin-projective-line-constructible`) consumes. -/
theorem isConstructibleSheaf_homology_rightDerivedLowerStar_constantSheaf
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (aS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] (f : X ⟶ S) {n : Type u} [Finite n]
    (i : X ⟶ ℙ(n; S)) [IsClosedImmersion i] (hi : i ≫ ℙ(n; S) ↘ S = f)
    (hf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ 1)
    [HasInvertibleExponent Λ S] (M : ModuleCat.{u + 1} Λ) [Finite M] (q : ℤ) :
    IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) := by
  sorry

end Etale

end AlgebraicGeometry
