/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Sheaf.AlgebraicGeometry.BlockStraighteningData

import Sheaf.AlgebraicGeometry.BlockStraighteningInitialJet
import Sheaf.AlgebraicGeometry.BlockStraighteningGeometricChart
import Sheaf.AlgebraicGeometry.BlockProjectionFirstTransport
import Sheaf.RingTheory.FormalCoefficientOperatorBaseChange
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.LinearAlgebra.Matrix.Block

/-! # Block straightening and transport of exact stored projections -/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory
namespace AlgebraicGeometry.HilbertCoefficient

private theorem scalarEval_map {R S : Type u} [CommRing R] [CommRing S]
    (σ : R →+* S) {t : ℕ}
    (P : MvPowerSeries.FiniteCoefficientExpression R t 1 t 1)
    (H : MvPowerSeries (Fin t) R) :
    (P.map σ).scalarEval (MvPowerSeries.map σ H) =
      MvPowerSeries.map σ (P.scalarEval H) := by
  exact congrFun (P.eval_map σ (fun _ ↦ H)) 0

private theorem correction_map {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing S] (σ : R →+* S) {t s : ℕ}
    (P : MvPowerSeries.FiniteCoefficientExpression R t 1 t 1)
    (f : Fin s → MvPowerSeries (Fin t) R) (old : Fin s → Prop)
    (h : ∀ H, P.scalarEval H - H ∈ Ideal.span {g | ∃ i, old i ∧ g = f i}) :
    ∀ H, (P.map σ).scalarEval H - H ∈
      Ideal.span {g | ∃ i, old i ∧ g = MvPowerSeries.map σ (f i)} := by
  classical
  let e := Fintype.equivFin {i : Fin s // old i}
  let g : Fin (Fintype.card {i : Fin s // old i}) → MvPowerSeries (Fin t) R :=
    fun i ↦ f (e.symm i).val
  have hrange : Set.range g = {v | ∃ i, old i ∧ v = f i} := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(e.symm i).val, (e.symm i).property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨e ⟨i, hi⟩, by simp [g]⟩
  have hcor : P.HasIdealCorrection g := by
    intro H
    simpa only [hrange] using h H
  have hmap := P.hasIdealCorrection_map σ g hcor
  have hrange' : Set.range (fun i ↦ MvPowerSeries.map σ (g i)) =
      {v | ∃ i, old i ∧ v = MvPowerSeries.map σ (f i)} := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(e.symm i).val, (e.symm i).property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨e ⟨i, hi⟩, by simp [g]⟩
  simpa only [MvPowerSeries.FiniteCoefficientExpression.HasIdealCorrection, hrange'] using hmap

private theorem projection_transport {k L : Type u} [Field k] [CharZero k] [Field L]
    {B C : Scheme.{u}} {m r t s : ℕ}
    {c : MvPolynomial (Fin m ⊕ Fin r) k →+* Γ(B, ⊤)}
    {h : Fin r → Γ(B, ⊤)} {D : ImplicitCoordinateDerivations B c}
    (j : C ⟶ B) (center : C)
    (points : ∀ b : C, ImplicitTaylorPoint.{u, u} c h D j b)
    (α : Fin s → Fin ((m + r) + t) →₀ ℕ) (d Q : ℕ)
    (f : Fin s → MvPowerSeries (Fin t) Γ(B, ⊤))
    (ρ : Γ(B, ⊤) →+* MvPowerSeries (Fin r) Γ(C, ⊤))
    (τ : Γ(B, ⊤) →+* MvPowerSeries (Fin m ⊕ Fin r) L)
    [IsNoetherianRing Γ(C, ⊤)]
    (P : MvPowerSeries.FiniteCoefficientExpression Γ(B, ⊤) t 1 t 1)
    (hP : blockProjectionHypotheses α d Q f τ P)
    (hfirst : blockPreservesFirst α d Q P (blockPointCoefficientMap (points center))) :
    blockProjectionConclusions j center points α d Q f ρ P := by
  classical
  obtain ⟨hker, hcorr, hfix, _⟩ := hP
  have hkerρ := P.isKernelProjection_map ρ (blockEarlierTests α d Q) hker
  refine ⟨hkerρ, correction_map ρ P f (fun i ↦ (α i).degree < d) hcorr, ?_,
    ?_, ?_, hfirst, ?_⟩
  · intro i hi
    rw [scalarEval_map, hfix i hi]
  · intro H E γ δ
    rw [hkerρ.1 H E]
    simp
  · intro b
    let σ := blockPointCoefficientMap (points b)
    refine ⟨?_, P.isKernelProjection_map σ (blockEarlierTests α d Q) hker,
      correction_map σ P f (fun i ↦ (α i).degree < d) hcorr⟩
    intro i hi
    rw [scalarEval_map, hfix i hi]
  · intro hempty
    constructor
    · funext H
      exact hker.2 H (fun E ↦ isEmptyElim E)
    · funext H
      exact hkerρ.2 H (fun E ↦ isEmptyElim E)

/-- One block of derivative straightening, retaining exact earlier projections.
Source: BM Theorem 9.6, (9.7)--(9.8), Remarks 9.9--9.11, pp.279--280;
agent stored-projection refinement
(blueprint: lem-trf-block-straightening-projection-transport).

Proof: the initial-jet theorem gives vanishing of the equations, zero entries
above the diagonal, and nonzero diagonal entries of the evaluated Jacobian.
Mapping the determinant and using the lower triangular determinant formula
shows that the Jacobian determinant is nonzero. Apply the projection-free
geometric-chart theorem and retain all its geometric fields.

For each stored projection, transport its common-kernel property by
isKernelProjection_map. Enumerate the subset of earlier generators and apply
hasIdealCorrection_map to rho and every pointwise coefficient map; the target
coefficient rings are Noetherian. Evaluation compatibility transports the fixing
of later generators. Kernel image containment makes every extracted T and Y
coefficient vanish. The separate graph-conjugacy theorem transports the centered
first-exponent property. Empty tests make every input lie in the kernel, so
pointwise fixing proves both operators equal identity. Assemble these facts
with the geometric fields into the unchanged BlockStraighteningOutput.
-/
theorem blockStraighteningProjectionTransport {k : Type u} [Field k] [CharZero k]
    (B : Scheme.{u}) {m r t s : ℕ}
    (c : MvPolynomial (Fin m ⊕ Fin r) k →+* Γ(B, ⊤)) (a : B)
    (D : ImplicitCoordinateDerivations B c)
    (α : Fin s → Fin ((m + r) + t) →₀ ℕ) (d Q : ℕ)
    (f : Fin s → MvPowerSeries (Fin t) Γ(B, ⊤))
    (pick : Fin (r + t) → Fin s) (β : Fin (r + t) → Fin ((m + r) + t) →₀ ℕ)
    (A : BlockStraighteningInput B c a D α d Q f pick β) :
    (∀ j : Fin r, B.Γevaluation a (blockEquations D f pick β j) = 0) ∧
    B.Γevaluation a (implicitJacobian D (blockEquations D f pick β)) ≠ 0 ∧
    Nonempty (BlockStraighteningOutput A) := by
  classical
  obtain ⟨hzero, hupper, hdiag⟩ :=
    blockStraighteningInitialJet B c a D α d Q f pick β A
  let M : Matrix (Fin r) (Fin r) (B.residueField a) :=
    fun j l ↦ B.Γevaluation a (D.deriv ⊤ (Sum.inr l) (blockEquations D f pick β j))
  have htri : M.IsLowerTriangular := by
    intro j l hjl
    exact hupper j l hjl
  have hjac : B.Γevaluation a (implicitJacobian D (blockEquations D f pick β)) ≠ 0 := by
    rw [implicitJacobian, (B.Γevaluation a).hom.map_det]
    change M.det ≠ 0
    rw [Matrix.det_of_isLowerTriangular M htri]
    exact Finset.prod_ne_zero_iff.mpr (fun j _ ↦ hdiag j)
  obtain ⟨G, hnoeth⟩ := blockStraighteningGeometricChart B c a D α d Q f pick β A hzero hjac
  refine ⟨hzero, hjac, ⟨{
    open_in_zero := G.open_in_zero
    ambient := G.ambient
    toAmbient := G.toAmbient
    square := G.square
    closed := G.closed
    affine := G.affine
    center := G.center
    center_eq := G.center_eq
    etale := G.etale
    smooth := G.smooth
    points := G.points
    rho := G.rho
    rho_coeff := G.rho_coeff
    coefficient_specialization := G.coefficient_specialization
    old_tests := G.old_tests
    coefficients := G.coefficients
    first := G.first
    ideals := G.ideals
    membership := G.membership
    joint_derivatives := G.joint_derivatives
    projection := ?_ }⟩⟩
  intro P hP
  have hfirst := blockProjectionFirstTransport _ G.center a G.center_eq G.residue_center
    G.points (A.taylor a) (A.taylor_spec a) α d Q P hP.2.2.2
  exact projection_transport _ G.center G.points α d Q f G.rho (A.taylor a) P hP hfirst

end AlgebraicGeometry.HilbertCoefficient
