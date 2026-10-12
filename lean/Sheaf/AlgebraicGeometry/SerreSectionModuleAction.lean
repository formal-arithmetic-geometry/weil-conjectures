/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.DirectSum.Module
import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules

/-! # The explicit action on the nonnegative twisted section direct sum

Source: Stacks Project, Lemma 01YS(5), construction of the section module.
(blueprint: lem-sc-p1-section-action-laws). -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]
variable (G : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Modules)

/-- The degree `z` group is the section group when `z ≥ 0`, and the zero group otherwise.
Using functions out of the proposition makes negative degrees empty products. -/
abbrev serreSectionPiece (z : ℤ) :=
  PLift (0 ≤ z) → Γ(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) z, ⊤)

noncomputable instance serreSectionPieceAddCommGroup (z : ℤ) :
    AddCommGroup (serreSectionPiece k G z) := by
  unfold serreSectionPiece
  infer_instance

/-- The explicit additive direct sum of the nonnegative section groups. -/
abbrev serreSectionSum := DirectSum ℤ (serreSectionPiece k G)

/-- The effect of a homogeneous scalar on a single degree, extended by zero in negative
source degrees. -/
noncomputable def serreSectionHomogeneous (e : ℕ) (z : ℤ)
    (a : MvPolynomial.homogeneousSubmodule (Fin 2) k e) (s : serreSectionPiece k G z) :
    serreSectionPiece k G (z + e) :=
  fun _ ↦ if hz : 0 ≤ z then Scheme.Modules.Hom.app (G ◁ Proj.twistMul z a.property) ⊤
    (s ⟨hz⟩) else 0

/-- Scalar multiplication, explicitly summing the finitely many homogeneous polynomial
components and the finitely many section components. -/
noncomputable def serreSectionSMul (a : MvPolynomial (Fin 2) k) (x : serreSectionSum k G) :
    serreSectionSum k G := by
  classical
  exact ∑ e ∈ (DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin 2) k) a).support,
    ∑ z ∈ x.support, DirectSum.of (serreSectionPiece k G) (z + e)
      (serreSectionHomogeneous k G e z
        (DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin 2) k) a e) (x z))

/-- The scalar operation on the explicitly constructed additive direct sum. -/
noncomputable instance serreSectionSumSMul :
    SMul (MvPolynomial (Fin 2) k) (serreSectionSum k G) := ⟨serreSectionSMul k G⟩

/-- The explicit finite-sum action satisfies the polynomial module laws.

Source: Stacks Project, Lemma 01YS(5), the graded module of twisted global sections;
Stacks Definition 01MN for twists and Lemma 01M7 for localizations and functoriality.
(blueprint: lem-sc-p1-section-action-laws).
Proof: the decomposition of a polynomial is additive and multiplicative. On a summand of
nonnegative degree, `serreSectionHomogeneous` is the map on sections induced by multiplication
of local homogeneous fractions, tensored with the identity of G. Multiplication of fractions
is additive in each variable, multiplication by one is the identity, and composition is
multiplication by the product, after transporting the degree equality. Tensoring and taking
sections preserve these equalities. In negative source degrees the section group is the zero
group, so the same equalities hold. Expand the two finite sums defining `serreSectionSMul`,
use distributivity of finite sums, and the decomposition identity for the product of two
polynomials to obtain `mul_smul`; the remaining additive laws follow from the additive and
unit identities. For a homogeneous scalar and a single section summand, both decompositions
have a single possibly nonzero component; the same expansion yields the displayed single
summand formula, including the zero polynomial and zero section. No coherence, nonzero
section, or finite generation hypothesis is used. -/
theorem serreSectionActionLaws :
    (∀ x : serreSectionSum k G, (1 : MvPolynomial (Fin 2) k) • x = x) ∧
    (∀ (a b : MvPolynomial (Fin 2) k) (x : serreSectionSum k G),
      (a * b) • x = a • (b • x)) ∧
    (∀ (a : MvPolynomial (Fin 2) k) (x y : serreSectionSum k G),
      a • (x + y) = a • x + a • y) ∧
    (∀ (a b : MvPolynomial (Fin 2) k) (x : serreSectionSum k G),
      (a + b) • x = a • x + b • x) ∧
    (∀ (e : ℕ) (z : ℤ) (a : MvPolynomial (Fin 2) k)
      (ha : a ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k e)
      (s : serreSectionPiece k G z),
      a • DirectSum.of (serreSectionPiece k G) z s =
        DirectSum.of (serreSectionPiece k G) (z + e)
          (serreSectionHomogeneous k G e z ⟨a, ha⟩ s)) := by sorry

/-- The module structure on the explicit direct sum, using only the named action-law proof. -/
noncomputable instance serreSectionSumModule :
    Module (MvPolynomial (Fin 2) k) (serreSectionSum k G) where
  one_smul := (serreSectionActionLaws k G).1
  mul_smul := (serreSectionActionLaws k G).2.1
  smul_add := (serreSectionActionLaws k G).2.2.1
  smul_zero a := by
    classical
    change serreSectionSMul k G a 0 = 0
    simp [serreSectionSMul]
  add_smul := (serreSectionActionLaws k G).2.2.2.1
  zero_smul x := by
    classical
    change serreSectionSMul k G 0 x = 0
    simp [serreSectionSMul]

end AlgebraicGeometry
