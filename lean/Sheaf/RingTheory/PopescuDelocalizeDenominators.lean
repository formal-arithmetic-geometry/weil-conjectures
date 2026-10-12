/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Denominator data for delocalization

Source: Stacks Project, Smoothing Ring Maps, proof of Lemma Tag 07F4.
(blueprint: lem-weil-pbc-popescu-delocalize-denominators).
-/

@[expose] public section

universe u v w x

namespace Algebra

open MvPolynomial

/-- The rescaling and denominator-clearing data before forming the quotient.
Source: Stacks Project, Smoothing Ring Maps, Lemma Tag 07F4, proof from rescaling the
extra variables through choosing the elements `sⱼ` and `s'ⱼ`.
(blueprint: lem-weil-pbc-popescu-delocalize-denominators).

Proof: put `K = Localization S` and `T = R[X]`. For each extra index choose
`dᵢ ∈ S` and `lᵢ ∈ Λ` with `γ (Q.val i) = lᵢ/dᵢ`; for the first `n` indices
put `dᵢ = 1` and `lᵢ = α (P.val i)`, using `hfactor` and `hval`. The new generators
are `dᵢ * Q.val i`. If `qⱼ` are the old relations, substitute `Xᵢ/dᵢ` into them.
This is an automorphism of `K[X]`, inverse to substitution by `dᵢ * Xᵢ`, so the
new equations generate the new evaluation kernel. The chain rule scales row `i`
of the initial Jacobian by `dᵢ⁻¹`; hence its determinant still evaluates to a unit.
Multiply each equation by a common denominator of its finitely many coefficients,
obtaining `fⱼ ∈ T`. These multipliers are units in `K`, so the kernel ideal is
unchanged and the new minor still evaluates to a unit. The new generator values
map under `γ` to `lᵢ/1`.

Lift the inverse of this minor from `D` to `K[X]` using surjectivity of evaluation.
Then `1 = b₀ * Δ(f) + ∑ bⱼ * fⱼ` in `K[X]`, because the error lies in the
relation ideal. Choose a common denominator `d ∈ S` for the finitely many
coefficients of all `bⱼ`, obtaining polynomials `aⱼ` whose coefficient extensions
are `d * bⱼ`. The difference `C d - a₀ * Δ(f) - ∑ aⱼ * fⱼ` maps to zero in
`K[X]`. This polynomial ring is the localization of `T` at the constants from
`S`, so some `e ∈ S` kills that difference in `T`. Replace each `aⱼ` by
`C e * aⱼ` and take `s₀ = e * d`, giving the asserted exact identity in `T`.

Each renamed relation of `P` evaluates to zero in `D`: the first `n` generators
were fixed, and `β` preserves the original relations. Express that polynomial in
the localized ideal `(f)`. Clear the finitely many coefficients of the expression
and kill the residual polynomial equality by another localization annihilator,
just as above; their product is `sgⱼ`. Finally each `fⱼ` evaluates at `l` to zero
after localization, since it vanishes on the new generators of `D` and `γ` maps
those generators to `lᵢ/1`. The localization kernel criterion in `Λ` gives `sfⱼ`
killing this evaluation. Empty families use empty products and determinant `1`.
No injectivity of a localization map was used; the extra annihilators handle its
kernel, including when `0 ∈ S`. -/
theorem exists_delocalization_denominator_data
    {R : Type u} {A : Type v} {Λ : Type w}
    [CommRing R] [CommRing A] [CommRing Λ] [Algebra R A] [Algebra R Λ]
    (α : A →ₐ[R] Λ) (S : Submonoid R) {n t m c : ℕ}
    (P : Presentation R A (Fin n) (Fin t)) (hc : c ≤ n + m)
    {D : Type x} [CommRing D] [Algebra (Localization S) D]
    (Q : SubmersivePresentation (Localization S) D (Fin (n + m)) (Fin c))
    (β : Localization (algebraMapSubmonoid A S) →ₐ[Localization S] D)
    (γ : D →ₐ[Localization S] Localization (algebraMapSubmonoid Λ S))
    (hfactor : γ.comp β =
      IsLocalization.mapₐ S (Localization S)
        (Localization (algebraMapSubmonoid A S)) (Localization (algebraMapSubmonoid Λ S)) α)
    (hmap : Q.map = Fin.castLE hc)
    (hval : ∀ i : Fin n, Q.val (Fin.castAdd m i) =
      β (algebraMap A (Localization (algebraMapSubmonoid A S)) (P.val i))) :
    ∃ (f : Fin c → MvPolynomial (Fin (n + m)) R)
      (l : Fin (n + m) → Λ) (s₀ : S) (a₀ : MvPolynomial (Fin (n + m)) R)
      (a : Fin c → MvPolynomial (Fin (n + m)) R) (sg : Fin t → S) (sf : Fin c → S),
      (∀ i : Fin n, l (Fin.castAdd m i) = α (P.val i)) ∧
      C s₀.val = a₀ * Matrix.det (fun i j : Fin c ↦ pderiv (Fin.castLE hc i) (f j)) +
        ∑ j, a j * f j ∧
      (∀ j : Fin t, C (sg j).val * rename (Fin.castAdd m) (P.relation j) ∈
        Ideal.span (Set.range f)) ∧
      ∀ j : Fin c, aeval l (C (sf j).val * f j) = 0 := by
  sorry

end Algebra
