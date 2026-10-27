/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3
-/
module

public import Sheaf.Paper.AdicPunctualWeights

/-! # Exact Frobenius fibres realizing the finite-stage punctual spectrum

Source: Bhatt--Scholze, Corollary 6.8.5, Lemma 6.8.7, Proposition 6.8.14;
blueprint main-20261015, sk-d-dl-general-weights, subobject and quotient clauses.
(blueprint: lem-zl-punctual-spectrum-exact-fibre).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

/-- The local spectrum defined using finite Weil presentations is the spectrum of
an exact finite-dimensional fibre with its natural Frobenius automorphism.

Source: Bhatt--Scholze 6.8.5, 6.8.7, 6.8.14 and 6.8.15; blueprint
sk-d-dl-general-weights, subobject and quotient closure; the exact Frobenius-fibre
argument of lem-wf-rational-stalk-exact, with independent universes and no global
separatedness assumption (blueprint: lem-zl-punctual-spectrum-exact-fibre).

Proof: choose a k0-embedding of the finite residue field of y into k and its
geometric lift x. On the underlying constructible heart take H^0 of completed
pullback to x and point sections, then extend each finite coefficient field to
Qbar. The point-section and cohomology/scalar comparisons identify these functors
under field enlargement. Their tensor unit and tower identities descend them to
the common-stage category and its Weil heart. Finite-dimensionality holds at each
finite presentation and is unchanged by scalar extension. Kernels and cokernels
are computed on a common finite lisse stratification, where fibre evaluation is
exact on finite-dimensional representations (BS 6.8.5 and 6.8.7); extension of fields
is exact. Forgetting Weil structure creates kernels and cokernels, so the resulting
fibre preserves finite limits and colimits. These computations can be made on an
affine neighbourhood of y defined over k0, whose base change is Frobenius-stable;
thus no separatedness assumption on the whole scheme is needed.

At a finite Weil presentation the local operator is the specified iterated point
transport, the return comparison, and the image of the iterated Weil isomorphism.
The point-transport clause of lem-weil-frobenius-cohomology-transport-iso on
the auxiliary model Spec(k0) proves transport invertible, without assuming Y0
separated. All other factors are isomorphisms. Naturality and pullback composition,
together with the defining commuting square of a Weil morphism, makes these
operators a natural automorphism. The composition/scalar and point-transport/scalar
identities identify them under field enlargement, so they descend with the fibre.
Every Weil object, arrow, inverse and finite list of equations descends to a common
finite field. Hence on any presentation this operator is conjugate to the scalar
extension of localClosedFrobeniusCohomology in degree zero. Changing the residue
embedding conjugates the operator by transport along the finite Frobenius orbit.
Conjugacy preserves eigenvalues, giving the forward implication of the displayed
spectrum equivalence. Conversely, choose a finite Weil presentation of F; the
same conjugacy carries every eigenvalue of its fibre operator to that presentation,
which is a witness for SfPunctualEigenvalue. Zero fibres have no eigenvalues and
the empty scheme has no y. No fibre object chosen here is used to define data. -/
theorem sfPunctualSpectrumExactFibre
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Qbar : Type v) [Field Qbar] [Algebra (Padic l) Qbar]
    [IsAlgClosure (Padic l) Qbar]
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left}) :
    ∃ V : sfCommonStageWeilSheaf D l hl Y₀ Qbar ⥤ ModuleCat.{max (u + 1) v} Qbar,
      ∃ φ : V ≅ V, PreservesFiniteLimits V ∧ PreservesFiniteColimits V ∧
        (∀ F, FiniteDimensional Qbar (V.obj F)) ∧
        ∀ F α, SfPunctualEigenvalue D l hl Qbar Y₀ F y α ↔
          Module.End.HasEigenvalue (φ.hom.app F).hom α := by
  sorry

end WeilConjectures
