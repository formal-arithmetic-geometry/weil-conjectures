/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.FiniteType

/-!
# Global and relative global complete intersections

Following Stacks, Algebra, Sections 00S8 and 00SP, we define

- `Algebra.IsGlobalCompleteIntersection k T`: `T ≅ k[x₁,…,xₙ]/(f₁,…,f_c)` with `dim T = n - c`
  (or `T = 0`);
- `Algebra.IsLocalCompleteIntersection k S`: `S` is covered by principal opens `D(g_i)` with
  each `S_{g_i}` a global complete intersection;
- `Algebra.IsRelativeGlobalCompleteIntersectionPresentation`: every nonempty fibre of
  `Spec R[x₁,…,xₙ]/(f₁,…,f_c) → Spec R` has dimension `n - c`;
- `Algebra.IsRelativeGlobalCompleteIntersection R S`.
-/

@[expose] public section

universe u v

namespace Algebra

/-- `k[x₁,…,xₙ]/(f₁,…,f_c)`. -/
abbrev PolynomialQuotient (R : Type u) [CommRing R] {n c : ℕ}
    (f : Fin c → MvPolynomial (Fin n) R) : Type u :=
  MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)

/-- A `k`-algebra `T` is a *global complete intersection over `k`* if `T = 0`, or there are
`f₁, …, f_c ∈ k[x₁,…,xₙ]` with `k[x₁,…,xₙ]/(f₁,…,f_c) ≅ T` and `dim T = n - c`
(Stacks 00S9). (blueprint: `def-weil-pbc-complete-intersection-over-field`) -/
def IsGlobalCompleteIntersection (k : Type u) [Field k] (T : Type v) [CommRing T] [Algebra k T] :
    Prop :=
  Subsingleton T ∨ ∃ (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) k),
    Nonempty (PolynomialQuotient k f ≃ₐ[k] T) ∧ c ≤ n ∧
      topologicalKrullDim (PrimeSpectrum T) = ((n - c : ℕ) : WithBot ℕ∞)

/-- A finitely generated `k`-algebra `S` is a *local complete intersection over `k`* if there is a
family `(g_i)` with `Spec S = ⋃ D(g_i)` and each `S_{g_i}` a global complete intersection.
(blueprint: `def-weil-pbc-complete-intersection-over-field`) -/
def IsLocalCompleteIntersection (k : Type u) [Field k] (S : Type v) [CommRing S] [Algebra k S] :
    Prop :=
  Algebra.FiniteType k S ∧ ∃ (J : Type v) (g : J → S),
    ⋃ i, (PrimeSpectrum.basicOpen (g i) : Set (PrimeSpectrum S)) = Set.univ ∧
      ∀ i, IsGlobalCompleteIntersection k (Localization.Away (g i))

/-- `T = R[x₁,…,xₙ]/(f₁,…,f_c)` is a *relative global complete intersection* over `R` if every
nonempty fibre has dimension `n - c`: for every prime `𝔭` with `κ(𝔭) ⊗[R] T ≠ 0`, the Krull
dimension of `Spec(κ(𝔭) ⊗[R] T)` is `n - c` (in particular `c ≤ n`).
(blueprint: `def-weil-pbc-relative-global-complete-intersection`) -/
def IsRelativeGlobalCompleteIntersectionPresentation (R : Type u) [CommRing R] {n c : ℕ}
    (f : Fin c → MvPolynomial (Fin n) R) : Prop :=
  ∀ (p : Ideal R) [p.IsPrime], Nontrivial (p.Fiber (PolynomialQuotient R f)) →
    c ≤ n ∧ topologicalKrullDim (PrimeSpectrum (p.Fiber (PolynomialQuotient R f))) =
      ((n - c : ℕ) : WithBot ℕ∞)

/-- A ring map `R → S` is a *relative global complete intersection* if `S` is isomorphic as an
`R`-algebra to a relative global complete intersection `R[x₁,…,xₙ]/(f₁,…,f_c)`.
(blueprint: `def-weil-pbc-relative-global-complete-intersection`) -/
def IsRelativeGlobalCompleteIntersection (R : Type u) [CommRing R] (S : Type v) [CommRing S]
    [Algebra R S] : Prop :=
  ∃ (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R),
    IsRelativeGlobalCompleteIntersectionPresentation R f ∧
      Nonempty (PolynomialQuotient R f ≃ₐ[R] S)

end Algebra
