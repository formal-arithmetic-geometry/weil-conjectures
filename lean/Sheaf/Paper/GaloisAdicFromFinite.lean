/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import Sheaf.Paper.GaloisLisseCorrespondenceData
import Sheaf.NumberTheory.Padics.AdicLimitFiniteModules
import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
import Sheaf.RepresentationTheory.ProfiniteStableLattice

/-! # Adic reconstruction from finite Galois modules -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.Scheme

/-- Reconstruct the adic correspondence from the normalized finite correspondence.
Source: Deligne, Weil II (1.1.1), (1.1.6); Stanford Weil II seminar L19,
Proposition 1.1.9; proof steps 6--10 of `cor-galois-lisse-representations`.
(blueprint: new-e4-galois-adic-from-finite).

Proof: use the supplied profinite model `P` and its continuous group isomorphism `δ`
throughout the construction. At each coefficient
quotient apply `c.e` and its evaluation normalization to the levels of an integral lisse
system. The finite-module inverse-limit theorem constructs its complete finite module,
quotient identifications and continuous action, functorially on compatible maps. Conversely
apply the inverse finite equivalence to the quotients of a continuous integral module.
The inverse-limit quotient identifications and finite counits give the two natural
isomorphisms of the integral equivalence. They also give its canonical fibre comparison
and the specified projection formula for the action. Rationalize integral Hom modules.
Equivariant Hom commutes with inverting the uniformizer: any denominator is a fixed
power, and the torsion in each finite target module is annihilated by a fixed power.
A stable lattice in a continuous finite-dimensional representation gives essential
surjectivity, producing the rational equivalence and its fibre comparison. Coefficient
extension is the balanced tensor comparison on finite levels, followed by inverse limit
and rationalization. Its uniqueness on pure germs makes it compatible with compositions
of field inclusions. Pass to the common-finite-coefficient localization: every algebraic
adic representation descends by its definition, and a finite list of matrices descends
all morphisms and their relations to one common finite extension. This gives the
algebraic equivalence and fibre comparison. Kernels and cokernels of finite-dimensional
continuous representations have the induced continuous actions; their finite coefficient
models give the rational and algebraic abelian structures. Equivalences preserve finite
limits and colimits. Transport the finite tensor and unit comparisons through the limit,
rationalization and localization constructions. Their pure-tensor formulas give the
three monoidal structures, the two braided inclusions and both integral and rational
scalar fibre identities, including the required normalizations. -/
theorem galois_adic_from_finite
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber y) G]
    (c : GaloisLisseFiniteCorrespondence y G)
    (P : ProfiniteGrp.{u}) (δ : G ≃ₜ* P)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q] :
    ∃ a : GaloisLisseAdicCorrespondence y G c l Q, a.P = P ∧ HEq a.δ δ := by
  sorry

end AlgebraicGeometry.Scheme
