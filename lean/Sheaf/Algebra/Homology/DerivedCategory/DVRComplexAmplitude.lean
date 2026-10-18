/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q110
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Nakayama

/-!
# Detecting cohomological amplitude modulo a uniformizer

Source: Milne, Lectures on Etale Cohomology, proof of Theorem 19.2, p. 125;
Stacks Project, Tags 05RS, 05RT, 05RU, 0147 and 00DV (2)
(blueprint: lem-pod-dvr-complex-amplitude-mod-uniformizer).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

/-- Cohomological amplitude of a bounded complex with finitely generated cohomology over a
DVR is detected by derived reduction modulo its uniformizer. The distinguished triangle
in `hcone` says precisely that `N` is a cone of `ϖ • 𝟙 M`. Thus `N` represents
`M ⊗ᴸ[R] (R / ϖ R)`, using the free resolution `R --ϖ--> R` of the residue field.
No choice of a cone or of a representative complex is fixed.

Source: Milne, Lectures on Etale Cohomology, proof of Theorem 19.2, p. 125, abstracted
to complexes of DVR modules; Stacks Project, Tags 05RS/05RT/05RU/0147 and 00DV (2)
(blueprint: lem-pod-dvr-complex-amplitude-mod-uniformizer).

Proof: Apply the long exact cohomology sequence of the distinguished cone triangle
(`lem-sf-derived-homology-long-exact`, using `def-weil-abstract-derived-category`).
In degree `i` this gives the exact segment
`Hⁱ(M) --ϖ--> Hⁱ(M) --> Hⁱ(N) --> Hⁱ⁺¹(M) --ϖ--> Hⁱ⁺¹(M)`.
The kernel at the second term is `ϖ Hⁱ(M)` and the image in the fourth term is its
`ϖ`-torsion. Consequently the induced sequence
`0 --> Hⁱ(M)/ϖ Hⁱ(M) --> Hⁱ(N) --> Hⁱ⁺¹(M)[ϖ] --> 0` is exact.
For each `i` outside `[a,b]`, the middle term vanishes by `hN`, so
`Hⁱ(M)/ϖ Hⁱ(M) = 0`, equivalently `ϖ Hⁱ(M) = Hⁱ(M)`.
The ideal `(ϖ)` is the maximal ideal and hence the Jacobson radical by
`def-sc-discrete-valuation-ring`. Apply `lem-weil-pbc-nakayama-jacobson` to this ideal
and the finitely generated module `Hⁱ(M)` to conclude that `Hⁱ(M) = 0`.
This proves the required vanishing in every degree outside the interval. -/
theorem cohomology_amplitude_of_uniformizer_cone
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (M N : DerivedCategory (ModuleCat.{max u v} R))
    (ι : M ⟶ N) (δ : N ⟶ M⟦(1 : ℤ)⟧)
    (hcone : Triangle.mk (ϖ • 𝟙 M) ι δ ∈ distTriang _)
    (hbounded : Set.Finite
      {i : ℤ | ¬ IsZero ((homologyFunctor (ModuleCat.{max u v} R) i).obj M)})
    (hfinite : ∀ i : ℤ,
      Module.Finite R ((homologyFunctor (ModuleCat.{max u v} R) i).obj M))
    (a b : ℤ) (hab : a ≤ b)
    (hN : ∀ i : ℤ, i ∉ Set.Icc a b →
      IsZero ((homologyFunctor (ModuleCat.{max u v} R) i).obj N)) :
    ∀ i : ℤ, i ∉ Set.Icc a b →
      IsZero ((homologyFunctor (ModuleCat.{max u v} R) i).obj M) := by
  sorry

end DerivedCategory
