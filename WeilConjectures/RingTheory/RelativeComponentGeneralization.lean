/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.RingTheory.RelativeComponentConstructible
public import WeilConjectures.RingTheory.DiscreteValuationRing.Dominating
public import WeilConjectures.Mathlib.RingTheory.DiscreteValuationRing.Basic
public import WeilConjectures.Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
# The relative connected component of a section is stable under generalization

Let `B` be a flat, finitely presented `A`-algebra whose fibres are geometrically reduced, and
`s : B →ₐ[A] A` a section. The relative connected component of `s` (the primes `q` of `B` lying in
the connected component of `s⁻¹ (q ∩ A)` in their fibre) is stable under generalization
(Stacks `055Q`).

The proof follows Stacks. Over a discrete valuation ring, an idempotent of the generic fibre of a
flat algebra with reduced special fibre extends to the algebra (Stacks `055J`,
`IsDiscreteValuationRing.exists_eq_algebraMap_of_isIdempotentElem`), so two sections meeting the
same connected component of the special fibre meet the same connected component of the generic
fibre. Over a noetherian base, a specialisation is traced by a discrete valuation ring
(`Ideal.exists_isDiscreteValuationRing_of_lt`) and the relative component is compatible with base
change (Stacks `055M`). The general case reduces to the noetherian one by noetherian approximation,
flatness descending at the finitely many points needed to cover the relative component of a fibre
(Stacks `00R6`).

## Main statements

- `PrimeSpectrum.mem_relativeComponent_of_isDiscreteValuationRing`: the discrete valuation ring
  case.
- `PrimeSpectrum.mem_relativeComponent_of_le_of_isNoetherianRing`: the noetherian case.
- `PrimeSpectrum.stableUnderGeneralization_relativeComponent`: the general case (Stacks `055Q`).

## References

- Stacks Project, Tags `055J`, `055Q`
-/

@[expose] public section

universe u

open TensorProduct Topology IsLocalRing

/-- **Flatness at a point is stable under base change.** Let `B₁` be an `R₁`-algebra, `R₂` an
`R₁`-algebra and `Q` a prime of `R₂ ⊗[R₁] B₁` lying over the prime `Q₁` of `B₁`. If `B₁` is flat
over `R₁` at `Q₁`, then `R₂ ⊗[R₁] B₁` is flat over `R₂` at `Q`. -/
theorem Module.Flat.localization_tensorProduct {R₁ R₂ B₁ : Type*} [CommRing R₁] [CommRing R₂]
    [CommRing B₁] [Algebra R₁ R₂] [Algebra R₁ B₁] (Q : Ideal (R₂ ⊗[R₁] B₁)) [Q.IsPrime]
    (h : Module.Flat R₁ (Localization.AtPrime
      (Q.comap (Algebra.TensorProduct.includeRight.toRingHom : B₁ →+* R₂ ⊗[R₁] B₁)))) :
    Module.Flat R₂ (Localization.AtPrime Q) := by
  sorry

namespace PrimeSpectrum

/-- **The relative component over a discrete valuation ring** (Stacks `055J`). Let `R` be a
discrete valuation ring, `C` a finite type `R`-algebra with reduced special fibre, and `σ, τ` two
sections of `C`. Assume that `C` is flat over `R` at the points of the relative component of `σ`
in the special fibre. If the special point of `τ` lies in the relative component of `σ`, then so
does its generic point.

The connected component `Z` of the special point of `σ` in the noetherian special fibre is open
and closed there, so there is `g ∈ C` with `D(g) ∩ V(𝔪 C) = Z` and `C_g` flat over `R`. An
idempotent of `C_g[1/ϖ]` separating the generic points of `σ` and `τ` comes from an idempotent of
`C_g`, which would separate their special points in `Z`. -/
theorem mem_relativeComponent_of_isDiscreteValuationRing {R C : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing C] [Algebra R C] [Algebra.FiniteType R C]
    (σ τ : C →ₐ[R] R) (hred : IsReduced (ResidueField R ⊗[R] C))
    (hflat : ∀ q ∈ relativeComponent σ, comap (algebraMap R C) q = closedPoint R →
      Module.Flat R (Localization.AtPrime q.asIdeal))
    (hτ : comap (τ : C →+* R) (closedPoint R) ∈ relativeComponent σ) :
    comap (τ : C →+* R) ⟨⊥, Ideal.isPrime_bot⟩ ∈ relativeComponent σ := by
  sorry

/-- **The relative component is stable under generalization over a noetherian base.** Let `A` be
noetherian, `B` a finite type `A`-algebra with a section `s`, and `x' ≤ x` primes of `B` with `x`
in the relative component of `s`, lying over `y`. Assume that the fibre over `y` is geometrically
reduced and that `B` is flat over `A` at the points of the relative component lying over `y`.
Then `x'` lies in the relative component of `s`.

A discrete valuation ring `R` traces the specialisation `x' ⤳ x`, giving a second section `τ` of
`R ⊗[A] B` over `R`, and we conclude by
`PrimeSpectrum.mem_relativeComponent_of_isDiscreteValuationRing` and the compatibility of the
relative component with base change. -/
theorem mem_relativeComponent_of_le_of_isNoetherianRing {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [IsNoetherianRing A] [Algebra.FiniteType A B] (s : B →ₐ[A] A)
    {x x' : PrimeSpectrum B} (hle : x' ≤ x) (hx : x ∈ relativeComponent s)
    (hred : ∀ (L : Type u) [Field L] [Algebra A L],
      RingHom.ker (algebraMap A L) = (comap (algebraMap A B) x).asIdeal → IsReduced (L ⊗[A] B))
    (hflat : ∀ q ∈ relativeComponent s, comap (algebraMap A B) q = comap (algebraMap A B) x →
      Module.Flat A (Localization.AtPrime q.asIdeal)) :
    x' ∈ relativeComponent s := by
  sorry

/-- **Noetherian approximation along the relative component.** Let `B` be a flat, finitely
presented `A`-algebra with a section `s`, and `y` a prime of `A`. Then `B` and `s` descend to a
finite type algebra `B₁` with a section `s₁` over a noetherian subring `A₁` of `A`, such that `B₁`
is flat over `A₁` at the points of the relative component of `s₁` lying under `y`.

Each point of the relative component of `s` over `y` has a neighbourhood on which some
noetherian model is flat (Stacks `00R6`, `Module.exists_fg_flat_localization_tensor`, and openness
of the flat locus). This part of the fibre is quasi-compact, so finitely many models suffice. -/
theorem exists_isPushout_forall_flat (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [Algebra.FinitePresentation A B] (s : B →ₐ[A] A) (y : PrimeSpectrum A) :
    ∃ (A₁ : Subalgebra ℤ A) (B₁ : Type u) (_ : CommRing B₁) (_ : Algebra A₁ B₁)
      (_ : Algebra B₁ B) (_ : IsScalarTower A₁ B₁ B),
      IsNoetherianRing A₁ ∧ Algebra.FiniteType A₁ B₁ ∧ Algebra.IsPushout A₁ A B₁ B ∧
      ∃ s₁ : B₁ →ₐ[A₁] A₁, (∀ b, (s₁ b : A) = s (algebraMap B₁ B b)) ∧
        ∀ q ∈ relativeComponent s₁,
          comap (algebraMap A₁ B₁) q = comap (algebraMap A₁ A) y →
          Module.Flat A₁ (Localization.AtPrime q.asIdeal) := by
  sorry

/-- **The relative component of a section is stable under generalization** (Stacks `055Q`). Let
`B` be a flat, finitely presented `A`-algebra with geometrically reduced fibres, and `s` a section
of `B`. Then the relative component of `s` is stable under generalization. -/
theorem stableUnderGeneralization_relativeComponent {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Flat A B] [Algebra.FinitePresentation A B]
    (hred : ∀ (L : Type u) [Field L] [Algebra A L], IsReduced (L ⊗[A] B)) (s : B →ₐ[A] A) :
    StableUnderGeneralization (relativeComponent s) := by
  sorry

end PrimeSpectrum
