/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import Sheaf.Algebra.Module.DegreeZeroFractions

/-!
# Basic-open fractions for finite coproducts of Proj twists

Source: Stacks Project, Constructions, Tags 01M6 (3), 01M7 (2),(3), 01MN (1).
(blueprint: lem-sc-proj-finite-twist-coproduct-fractions)
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite LocalizedModule

namespace AlgebraicGeometry.Proj

/-- For any graded commutative ring, the finite coproduct of its twists is the
associated sheaf of the finite sum of shifts, with scalar-compatible fraction maps.
Source: Stacks Project, Constructions, Tags 01M6 (3), 01M7 (2),(3), 01MN (1).
(blueprint: lem-sc-proj-finite-twist-coproduct-fractions)

Proof: identify the sections of each twist on D₊(f) with degree-zero fractions
of A(a i), by 01MN (1) and 01M7 (2). Finite coproducts of modules are finite
products, and finite products of sheaves are computed on sections. Thus send
a tuple of sections to its componentwise fractions, viewed in the localization
of Fin r → A. Localization commutes with this finite product: choose a common
power f^m for the finitely many denominators, multiplying the i-th numerator
by the missing power of f. This gives an additive injection. A tuple of
homogeneous fractions with common denominator f^m has numerator degree
a i + m * b in component i. Conversely every tuple satisfying those degree
conditions gives sections of each twist, proving the range equality. When r = 0,
both sides are zero, and choose numerator zero and denominator 1.
The scalar action is multiplication in the localization, so the fraction map
intertwines awayToSection q with the algebra map of q. For a restriction with
g^e = h * f, multiply a numerator y over f^m by h^m; the new denominator is
g^(e*m), since (g^e)^m = h^m * f^m. This is the canonical localization map
of 01M7 (3), hence agrees with the sheaf restriction on every component. -/
theorem finite_twist_coproduct_fractions
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (r : ℕ) (a : Fin r → ℤ) :
  ∃ alpha : ∀ (f : A) (b : ℕ),
    0 < b → f ∈ 𝒜 b →
    (∐ (fun i : Fin r ↦ twist 𝒜 (a i))).val.obj (op (basicOpen 𝒜 f))
      →+ LocalizedModule.Away f (Fin r → A),
  (∀ (f : A) (b : ℕ) (hb : 0 < b)
    (hf : f ∈ 𝒜 b),
    Function.Injective (alpha f b hb hf) ∧
    Set.range (alpha f b hb hf) = degreeZeroFractions
      (fun n : ℕ ↦ (𝒜 n : Set _))
      (fun n : ℕ ↦ {y : Fin r → A | ∀ i,
        if 0 ≤ a i + n then
          y i ∈ 𝒜 (a i + n).toNat
        else y i = 0}) (Submonoid.powers f)) ∧
  (∀ (f : A) (b : ℕ) (hb : 0 < b)
    (hf : f ∈ 𝒜 b)
    (q : HomogeneousLocalization.Away 𝒜 f)
    (s : (∐ (fun i : Fin r ↦ twist 𝒜 (a i))).val.obj (op (basicOpen 𝒜 f))),
    alpha f b hb hf (awayToSection 𝒜 f q
      • s) = algebraMap
        (HomogeneousLocalization.Away 𝒜 f)
        (Localization.Away f) q • alpha f b hb hf s) ∧
  (∀ (f g : A) (b c : ℕ) (hb : 0 < b) (hc : 0 < c)
    (hf : f ∈ 𝒜 b)
    (hg : g ∈ 𝒜 c)
    (inc : basicOpen 𝒜 g ≤
      basicOpen 𝒜 f)
    (e t : ℕ) (h : A),
    0 < e → h ∈ 𝒜 t → g ^ e = h * f →
    ∀ (m : ℕ) (y : Fin r → A)
      (s : (∐ (fun i : Fin r ↦ twist 𝒜 (a i))).val.obj
          (op (basicOpen 𝒜 f))),
      alpha f b hb hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
      alpha g c hc hg ((∐ (fun i : Fin r ↦
        twist 𝒜 (a i))).val.map
          (homOfLE inc).op s) =
        mk (h ^ m • y) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g)) := by sorry

end AlgebraicGeometry.Proj
