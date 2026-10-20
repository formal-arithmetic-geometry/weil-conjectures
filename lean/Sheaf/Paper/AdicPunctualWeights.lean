/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q72
-/
module

public import Sheaf.Paper.AdicHeartIntrinsicFibres
public import Sheaf.Paper.LocalFrobeniusTrace
public import Sheaf.Paper.WeilIndSheafCategory
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Punctual weights on the actual common-stage Weil heart

Source: blueprint main-20261015, sec-deligne-laumon-general,
sk-d-dl-general-weights, def-weil-punctual-weights
(blueprint: def-weil-punctual-weights).
The embedding need not be surjective; isomorphisms are included by their ring homomorphism.
Eigenvalues are computed at finite Weil stages using the recorded local geometric
Frobenius, then included in the chosen algebraic closure. No discrete Qbar sheaf
or derived category of Weil pairs is substituted for the recorded heart.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Qbar : Type v) [Field Qbar] [Algebra (Padic l) Qbar] [IsAlgClosure (Padic l) Qbar]
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- The local spectrum of a constructible Weil sheaf, computed on any finite Weil
presentation by the actual degree-zero local Frobenius. Extending scalars before
taking eigenvalues includes eigenvalues outside the finite field of definition.
The existential presentation is immaterial by coefficient extension and conjugacy.
Source: blueprint local eigenvalues (blueprint: def-weil-punctual-weights). -/
def SfPunctualEigenvalue (F : sfCommonStageWeilSheaf D l hl Y₀ Qbar)
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left}) (α : Qbar) : Prop :=
  ∃ (L : Padic.FiniteCoefficientFields l Qbar)
    (K : sfWeilComplex D l hl Y₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L)),
    Nonempty (F.obj ≅ sfWeilStageObject D l hl Y₀ Qbar L K) ∧
    ∃ (ι : Y₀.left.residueField y.val →+* D.k)
      (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k),
      Module.End.HasEigenvalue
        ((ModuleCat.extendScalars (sfAdicCoefficientEmbedding.{u} l Qbar L)).map
        (localClosedFrobeniusCohomology l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L)
          D hl Y₀ K y ι hι 0)).hom α

/-- Punctual iota-purity of weight w: every local geometric-Frobenius eigenvalue has
absolute value (#κ(y))^(w/2). This includes all closed points and all finite-stage
presentations, without fixing a coefficient field for the eigenvalues.
Source: blueprint punctual purity display (blueprint: def-weil-punctual-weights). -/
def SfIsPunctuallyPureOfWeight (iota : Qbar →+* ℂ)
    (F : sfCommonStageWeilSheaf D l hl Y₀ Qbar) (w : ℝ) : Prop :=
  ∀ (y : {y : Y₀.left // y ∈ closedPoints Y₀.left}) (α : Qbar),
    SfPunctualEigenvalue D l hl Qbar Y₀ F y α →
      ‖iota α‖ = (Nat.card (Y₀.left.residueField y.val) : ℝ) ^ (w / 2)

/-- Mixedness is the finite filtration in the actual abelian Weil heart, starting
at zero and ending at F, with pure quotients of weights at most w. The last term
is identified with F by an isomorphism, so no choice of a subobject representative
is imposed. A length-zero filtration includes the zero sheaf.
Source: blueprint mixed-weight filtration (blueprint: def-weil-punctual-weights). -/
def SfIsMixedOfWeightsAtMost (iota : Qbar →+* ℂ)
    (F : sfCommonStageWeilSheaf D l hl Y₀ Qbar) (w : ℝ) : Prop :=
  ∃ (m : ℕ) (G : Fin (m + 1) → sfCommonStageWeilSheaf D l hl Y₀ Qbar)
    (φ : ∀ i : Fin m, G i.castSucc ⟶ G i.succ),
    IsZero (G 0) ∧ Nonempty (G (Fin.last m) ≅ F) ∧ (∀ i : Fin m, Mono (φ i)) ∧
      ∀ i : Fin m, ∃ v : ℝ, v ≤ w ∧
        SfIsPunctuallyPureOfWeight D l hl Qbar Y₀ iota (cokernel (φ i)) v

end WeilConjectures
