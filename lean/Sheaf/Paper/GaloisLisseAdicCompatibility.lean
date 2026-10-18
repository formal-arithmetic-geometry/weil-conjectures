/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.Paper.GaloisLisseRepresentationData
import Sheaf.NumberTheory.Padics.AdicLimitFiniteModules
import Sheaf.NumberTheory.Padics.FiniteCoefficientFields

/-! # GaloisLisseAdicCompatibility

Source: the proof of `cor-galois-lisse-representations`. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

/-- Monoidal and scalar comparisons, and abelianity on the representation side.
Source: blueprint `cor-galois-lisse-representations`, proof steps 9-10;
Weil II (1.1.1), (1.1.6); lecture 19, Proposition 1.1.9.
Proof: continuous finite-dimensional representations are closed under kernels,
cokernels and finite sums. Restricted actions are continuous for subspaces;
quotient actions descend along the open linear quotient map. For algebraic
coefficients, descend objects and a morphism to a common finite extension
using the finitely many matrix coefficients, and form kernel and cokernel there.
The full-subcategory criterion gives the two abelian structures.
For integral tensors, the finite-level fibre tensor maps are equivariant by
c.finiteTensor and the integral evaluation formula. The finite-module tensor
reduction and reconstruction theorems identify their limit with the tensor of
integral fibres. The same construction for units and scalar extension gives
canonical comparisons. Their constraint diagrams can be checked after every
finite-level projection, hence hold by separatedness. Rationalize them; the
rational evaluation formula gives equivariance on pure tensors. Extend to
algebraic coefficients over a common finite field, using the model scalar
comparison. Naturality and constraint diagrams hold on the generators and pass
through localization. This supplies the specified monoidal structures and the
natural integral/rational scalar comparisons, without postulating tensor clauses.
(blueprint: lem-pod-galois-lisse-adic-compatibility). -/
theorem galois_lisse_adic_compatibility
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : GaloisLisseAdicData y G c l Q)
    (hI : galoisIntegralEvaluationAction y G c l Q d)
    (hR : galoisRationalEvaluationAction y G c l Q d)
    (hA : galoisAlgebraicModelScalarExtension y G c l Q d) :
    galoisRationalRepresentationsAbelian y G c l Q d ∧
      galoisAlgebraicRepresentationsAbelian y G c l Q d ∧
      galoisIntegralMonoidal y G c l Q d ∧
      galoisRationalMonoidal y G c l Q d ∧
      galoisAlgebraicMonoidal y G c l Q d ∧
      galoisIntegralScalarExtension y G c l Q d ∧
      galoisRationalScalarExtension y G c l Q d := by sorry

end AlgebraicGeometry.Scheme
