/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Functoriality
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Basic
public import WeilConjectures.Mathlib.RepresentationTheory.Basic
public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.AdicPunctualWeights
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Determinant purity is independent of the finite coefficient field

Source: blueprint main-20261015, sec-purity-real-sheaves, sk-d-real-detweights,
lemma lem-wf-determinantal-weight-coefficient-field
(blueprint: lem-wf-determinantal-weight-coefficient-field).

A basis of the given finite coefficient model realizes its scalar extensions by mapping
matrix entries. The determinant line is the existing represented degree datum `det`.
For a line, punctual purity is exactly the norm equality for its single Frobenius scalar;
we write this specialization of def-weil-punctual-weights explicitly.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry.WeilGroup

/-- Regard a matrix Weil representation as the existing represented degree datum, keeping
its actual degree map and chosen degree-one lift. No extra monodromy datum is chosen.
Source: blueprint sk-d-real-weil and the coefficient model in
lem-wf-determinantal-weight-coefficient-field
(blueprint: lem-wf-determinantal-weight-coefficient-field). -/
def representedDegreeDatumOfMatrix {K : Type u} [Field K] [Finite K]
    {X : Scheme.{u}} {p : X ⟶ Spec (.of K)} [IsCurve p] (W : WeilGroup p)
    {E : Type v} [Field E] {r : ℕ}
    (ρ : W.carrier →* Matrix.GeneralLinearGroup (Fin r) E) :
    Monodromy.RepresentedDegreeDatum W.carrier (Fin r) E where
  deg := W.deg
  surjective_deg := W.deg_surjective
  degreeOneElement := W.frobeniusLift
  deg_degreeOneElement := W.deg_frobeniusLift
  rep := ρ

/-- Extending a finite coefficient field preserves the punctual weight of the determinant.
The model has rank `r`, and its closure-valued representation is irreducible and lisse.
The displayed norm hypotheses and conclusion are precisely punctual purity for the
existing rank-one determinant representation: its sole eigenvalue is its `(0, 0)` entry.

Source: blueprint main-20261015, sec-purity-real-sheaves, sk-d-real-detweights,
lem-wf-determinantal-weight-coefficient-field
(blueprint: lem-wf-determinantal-weight-coefficient-field).

Proof: (1) In a basis of the E-model, the vectors 1 tensor e_i give a basis after extension
and the Frobenius matrix is the entrywise image under E -> E'.
(2) The determinant permutation formula commutes with this field inclusion.
(3) By def-mg-determinant-line, the determinant Frobenius is the resulting scalar on a
one-dimensional space, so that scalar is its unique eigenvalue. The compatible inclusions
in the fixed closure identify the E and E' scalars.
(4) Substitute this equality in the norm equality of def-weil-punctual-weights at each
closed point. Neither iota, the residue cardinality, nor the weight changes. -/
theorem isPunctuallyPure_det_coefficientExtension
    {K : Type u} [Field K] [Finite K] {X : Scheme.{u}}
    {p : X ⟶ Spec (.of K)} [IsConnectedCurve p]
    (_hNormal : IsNormalScheme X) (W : WeilGroup p)
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ ringChar K)
    (iota : PadicAlgCl l ≃+* ℂ)
    (E E' : IntermediateField (Padic l) (PadicAlgCl l))
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) E']
    (hEE' : E ≤ E') {r : ℕ}
    (ρ : W.carrier →* Matrix.GeneralLinearGroup (Fin r) E)
    (_hIrreducible : Representation.IsIrreducible
      ((Matrix.GeneralLinearGroup.toRepresentation (Fin r) (PadicAlgCl l)).comp
        ((Matrix.GeneralLinearGroup.map E.subtype).comp ρ)))
    (_hLisse : ∀ i j : Fin r, Continuous fun g : W.geometric ↦
      E.subtype (ρ g.val i j))
    (a : ℝ)
    (hPure : ∀ x : X.finitePoints,
      ‖iota (E.subtype ((W.representedDegreeDatumOfMatrix ρ).det.rep
        (W.frobenius x) 0 0))‖ = (X.pointNorm x.val : ℝ) ^ (a / 2)) :
    ∀ x : X.finitePoints,
      ‖iota (E'.subtype ((W.representedDegreeDatumOfMatrix
        ((Matrix.GeneralLinearGroup.map (IntermediateField.inclusion hEE').toRingHom).comp
          ρ)).det.rep (W.frobenius x) 0 0))‖ =
        (X.pointNorm x.val : ℝ) ^ (a / 2) := by
  sorry

end AlgebraicGeometry.WeilGroup
