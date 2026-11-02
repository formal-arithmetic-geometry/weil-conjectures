/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedWeil.NativeCondensedWeilReality
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Purity of real condensed Weil sheaves on curves

Source: latest Weil blueprint, `sk-p-real-purity/_section.md` and its proof,
clauses on constituent purity and mixedness (blueprint: `sk-p-real-purity`).

The statement is written for the actual condensed Weil-module category.  Its
punctual predicate is `NativeL2.Pure`, and its finite-filtration predicate is
`NativeL2.Mixed`; the determinant weight is the local determinant-line weight
recorded by the determinant-line helper below.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.NativeL2

open NativeCondensedModule

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀))) [IsSeparated X₀.hom]
  [SmoothOfRelativeDimension 1 X₀.hom] [GeometricallyConnected X₀.hom]
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- The native determinant-line weight used for a constituent.

Source: determinant-weight clause of `sk-d-real-detweights`, statement and
complement (`literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-rank-one-curves/sec-logarithms-and-rank-one-purity/
sk-d-real-detweights/_section.md`,
blueprint: `sk-d-real-detweights`). At every closed point and residue-field
lift, the determinant of native local Frobenius has absolute value
`q_x ^ (rank * w / 2)`. -/
def DeterminantWeight (M : WeilModule D l X₀) (iota : PadicAlgCl l →+* ℂ)
    (w : ℝ) : Prop :=
  ∀ (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k),
    ‖iota ((LinearMap.det (closedOperator D l X₀ M x i hi).hom).down)‖ =
      (Nat.card (X₀.left.residueField x.val) : ℝ) ^
        (Module.finrank (ULift.{u + 1} (PadicAlgCl l))
          (fibre l D M.carrier (localClosedPoint D X₀ x i hi)) * w / 2)

/-- A nonzero irreducible lisse native subquotient of `M`.

Source: constituent clause of `sk-p-real-purity`, proof Steps 1 and 3
(`literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-purity-real-sheaves/sec-rankin-s-argument/sk-p-real-purity/
sk-p-real-purity.proof.md`,
blueprint: `sk-p-real-purity`). The witnesses are lisse modules
`N ↪ P ↪ M`; the constituent is the nonzero simple quotient `P/N`. -/
def IsIrreducibleLisse (M : WeilModule D l X₀) : Prop :=
  IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier ∧
    ¬ IsZero M ∧
    ∀ (N : WeilModule D l X₀) (f : N ⟶ M),
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) N.carrier →
      Mono f → IsZero N ∨ IsIso f

/-- A nonzero simple lisse subquotient represented by `N ↪ P ↪ M`.

Source: constituent clause of `sk-p-real-purity`, proof Steps 1 and 3
(`literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-purity-real-sheaves/sec-rankin-s-argument/sk-p-real-purity/
sk-p-real-purity.proof.md`,
blueprint: `sk-p-real-purity`). -/
def IsNonzeroSimpleSubquotient (M Q : WeilModule D l X₀) : Prop :=
  IsIrreducibleLisse D l X₀ Q ∧
    ∃ (N P : WeilModule D l X₀) (f : N ⟶ P) (g : P ⟶ M),
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) N.carrier ∧
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) P.carrier ∧
      Mono f ∧ Mono g ∧ Nonempty (cokernel f ≅ Q)

/-- Purity of constituents and mixedness for a real lisse condensed Weil sheaf.

Source: `literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-purity-real-sheaves/sec-rankin-s-argument/sk-p-real-purity/_section.md`
and its proof at `sk-p-real-purity.proof.md`
(blueprint: `sk-p-real-purity`).
The proof steps stated by the source are: (1) use the exact lisse tensor
formalism, composition filtration, semisimplification, and determinant-weight
blocks; (2) place each block in an exterior power and apply the Rankin upper
bound; (3) identify the selected determinant-tensor summand and its
Frobenius eigenvalue; (4) cancel determinant moduli to obtain the upper bound
for each block; (5) repeat the construction for the real dual to obtain the
reverse bound; (6) restrict to affine neighbourhoods while preserving
constituents and determinant weights; (7) conclude punctual purity at every
closed point; and (8) use the finite composition filtration to obtain
`NativeL2.Mixed`. The theorem below states both resulting clauses, with all
proofs postponed at stage 2. -/
theorem isPure_of_isConstituent_of_isReal_and_isMixed
    (hl : l ≠ D.p)
    (M : WeilModule D l X₀)
    (iota : PadicAlgCl l →+* ℂ)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
    (hreal : NativeCondensedWeil.Real D l X₀ M iota) :
    (∀ (Q : WeilModule D l X₀), IsNonzeroSimpleSubquotient D l X₀ M Q →
      ∃ w : ℝ, DeterminantWeight D l X₀ Q iota w ∧
        Pure D l X₀ Q iota w) ∧
      ∃ w : ℝ, Mixed D l X₀ M iota w := by
  sorry

end WeilConjectures.NativeL2
