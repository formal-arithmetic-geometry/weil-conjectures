/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Diagonal jet modules

Source: Bierstone--Milman 1997, Remarks 9.1; BMT, arXiv:0905.3580, §6.1 and §6.5
(blueprint: def-trf-diagonal-jets).
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v w
open scoped TensorProduct
open AlgebraicGeometry

namespace DiagonalJets

/-- Principal parts, with the left algebra structure inherited from the tensor product.
Source: BM 1997, Remarks 9.1 (blueprint: def-trf-diagonal-jets). -/
abbrev principalParts (k : Type u) (A : Type v) [CommRing k] [CommRing A] [Algebra k A]
    (n : ℕ) :=
  (A ⊗[k] A) ⧸ (KaehlerDifferential.ideal k A) ^ (n + 1)

/-- The dimension of the fibre for the specified evaluation into a field.
Source: BM 1997, Remarks 9.1 (blueprint: def-trf-diagonal-jets). -/
def fibreDimension (k : Type u) (A : Type v) [CommRing k] [CommRing A] [Algebra k A]
    {L : Type w} [Field L] (ev : A →+* L) (n : ℕ) : ℕ :=
  letI := ev.toAlgebra
  Module.finrank L (L ⊗[A] principalParts k A n)

/-- Evaluation of an affine coordinate ring in the actual scheme residue field.
Source: BM 1997, Remarks 9.1 (blueprint: def-trf-diagonal-jets). -/
def affineEvaluation {A : Type u} [CommRing A] (x : Spec (CommRingCat.of A)) :
    A →+* (Spec (CommRingCat.of A)).residueField x :=
  ((Spec (CommRingCat.of A)).Γevaluation x).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

end DiagonalJets
