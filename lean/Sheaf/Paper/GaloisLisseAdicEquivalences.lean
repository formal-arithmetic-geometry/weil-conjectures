/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.Paper.GaloisLisseRepresentationData
import Sheaf.NumberTheory.Padics.AdicLimitFiniteModules
import Sheaf.RepresentationTheory.ProfiniteStableLattice
import Sheaf.NumberTheory.Padics.FiniteCoefficientFields

/-! # GaloisLisseAdicEquivalences

Source: the proof of `cor-galois-lisse-representations`. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

/-- Construction of the three adic evaluation equivalences, before tensor exactness.
Source: Weil II (1.1.1) b)-d), (1.1.6); Stanford Weil II seminar,
lecture 19, Proposition 1.1.9, pp. 2-3; blueprint
`cor-galois-lisse-representations`, proof steps 6-9.
Proof: use the specified profinite model P and homeomorphic group identification delta.
At every finite quotient use c.e and
c.finiteEvaluationAction. Take the inverse limit of the actions on stalks.
`adicLimit_finite_modules` gives finiteness, the projection quotient formula,
and continuity for the adic topology. The Hom comparison in
`finite_module_adic_complete_and_hom` gives full faithfulness; quotient towers
and the inverse finite equivalence give essential surjectivity. The projections
pin the integral evaluation formula. Rationalize the functor and its Hom maps.
Invariants commute with this localization since all torsion of the finite Hom
module is killed by a fixed uniformizer power. A stable lattice gives rational
essential surjectivity. The rational action formula follows on a tensor a tensor z.
Finally pass to the directed finite-coefficient localization. A matrix has
finitely many coefficients, so an equivariant map descends to one common finite
extension. Every l-adic representation descends by its definition, proving
essential surjectivity. The algebraic fibre comparison is canonical scalar
extension, giving the model comparison and its pure-tensor formula.
(blueprint: lem-pod-galois-lisse-adic-equivalences). -/
theorem galois_lisse_adic_equivalences
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    [ConnectedSpace Y] [IsTopologicalGroup G] [CompactSpace G]
    [IsFundamentalGroup (FiniteEtale.fiber y) G]
    (P : ProfiniteGrp.{u}) (δ : G ≃ₜ* P) :
    ∃ d : GaloisLisseAdicData y G c l Q,
      d.P = P ∧ HEq d.δ δ ∧
      galoisIntegralEvaluationAction y G c l Q d ∧
      galoisRationalEvaluationAction y G c l Q d ∧
      galoisAlgebraicModelScalarExtension y G c l Q d := by sorry

end AlgebraicGeometry.Scheme
