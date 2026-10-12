/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.Algebra.Module.DegreeZeroFractions
public import Sheaf.AlgebraicGeometry.ProjectiveLineProjChartIsomorphism
import Sheaf.AlgebraicGeometry.ProjectiveLineTwistExists

/-!
# Shifted free graded modules and the glued twists on the projective line

Source: blueprint `lem-sc-p1-graded-resolution`, final clause; Stacks Project,
Constructions, Definitions 01M6, 01MN and Lemma 01M7.
(blueprint: lem-sc-p1-proj-shifted-free-twist)

`Proj.twist` is the recorded sheaf of `S(d)`. Its comparison target is the glued
`ProjectiveLine.TwistData`, transported along a chart-compatible scheme isomorphism.
For a finite family, the coproduct is specified as the associated sheaf by injective
section maps onto degree-zero fractions, respecting scalars and canonical restrictions.
The finite direct sum is represented by `Fin r → S`. Its degree-`n` part consists of
vectors whose `i`th component has polynomial degree `a i + n`, with negative parts zero.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite LocalizedModule

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The sheaf of `S(d)` agrees with the twist glued using `g₀ = t⁻ᵈ g₁`, and the
sheaf of a finite direct sum of shifts is the coproduct of their twists.
Source: Stacks Project, Constructions, Definitions 01M6 (3), 01MN (1), Lemma 01M7 (2),(3).
(blueprint: lem-sc-p1-proj-shifted-free-twist)

Proof:
1. On `Uᵢ = D₊(xᵢ)`, def-weil-pbc-proj-twisting-sheaf gives the degree-`d`
   fractions. Multiplication by `xᵢ⁻ᵈ` identifies these with `k[x_{1-i}/xᵢ]`,
   making `xᵢᵈ` a generator on every subopen. The standard charts of
   def-sc-p1-standard identify polynomial Proj with the glued projective line.
2. On the overlap, `x₀ᵈ = (x₀/x₁)ᵈ x₁ᵈ = t⁻ᵈ x₁ᵈ`. Hence these trivializations
   give precisely TwistData. By lem-sc-p1-twist-exists the chart identifications
   glue to the isomorphism with the transported glued twist.
3. Localization and taking the degree-zero part commute with finite direct sums.
   The associated-sheaf description of def-weil-pbc-proj-twisting-sheaf therefore
   identifies the sheaf of the sum with the coproduct of the individual sheaves.
   Componentwise fraction maps give the displayed scalar and restriction formulas,
   including the empty family. Apply the isomorphism of step 2 to each summand.
-/
theorem proj_shifted_free_is_twist (k : Type v) [Field k] (d : ℤ) :
    ∃ C : ProjectiveLine.ProjChartIsomorphism k,
      (∃ (L : (ProjectiveLine (Spec (.of k))).Modules),
        Nonempty (ProjectiveLine.TwistData (Spec (.of k)) d L) ∧
        Nonempty (twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) d ≅
          (Scheme.Modules.tensorPullback C.iso.hom).obj L)) ∧
      (∀ (r : ℕ) (a : Fin r → ℤ),
        ∃ alpha : ∀ (f : MvPolynomial (Fin 2) k) (b : ℕ),
          0 < b → f ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k b →
          (∐ (fun i : Fin r ↦ twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)
            (a i))).val.obj (op (basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) f))
            →+ LocalizedModule.Away f (Fin r → MvPolynomial (Fin 2) k),
        (∀ (f : MvPolynomial (Fin 2) k) (b : ℕ) (hb : 0 < b)
          (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k b),
          Function.Injective (alpha f b hb hf) ∧
          Set.range (alpha f b hb hf) = degreeZeroFractions
            (fun n : ℕ ↦ (MvPolynomial.homogeneousSubmodule (Fin 2) k n : Set _))
            (fun n : ℕ ↦ {y : Fin r → MvPolynomial (Fin 2) k | ∀ i,
              if 0 ≤ a i + n then
                y i ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k (a i + n).toNat
              else y i = 0}) (Submonoid.powers f)) ∧
        (∀ (f : MvPolynomial (Fin 2) k) (b : ℕ) (hb : 0 < b)
          (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k b)
          (q : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin 2) k) f)
          (s : (∐ (fun i : Fin r ↦ twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)
            (a i))).val.obj (op (basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) f))),
          alpha f b hb hf (awayToSection (MvPolynomial.homogeneousSubmodule (Fin 2) k) f q
            • s) = algebraMap
              (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin 2) k) f)
              (Localization.Away f) q • alpha f b hb hf s) ∧
        (∀ (f g : MvPolynomial (Fin 2) k) (b c : ℕ) (hb : 0 < b) (hc : 0 < c)
          (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k b)
          (hg : g ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k c)
          (inc : basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) g ≤
            basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) f)
          (e t : ℕ) (h : MvPolynomial (Fin 2) k),
          0 < e → h ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k t → g ^ e = h * f →
          ∀ (m : ℕ) (y : Fin r → MvPolynomial (Fin 2) k)
            (s : (∐ (fun i : Fin r ↦ twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)
              (a i))).val.obj
                (op (basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) f))),
            alpha f b hb hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
            alpha g c hc hg ((∐ (fun i : Fin r ↦
              twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (a i))).val.map
                (homOfLE inc).op s) =
              mk (h ^ m • y) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g))) := by
  sorry

end AlgebraicGeometry.Proj
