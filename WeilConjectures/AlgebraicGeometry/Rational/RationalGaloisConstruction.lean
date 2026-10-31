/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralGaloisConstruction
import all WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicFiberFunctors
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Finite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Rational reconstruction from integral Galois modules

Source: Weil II (1.1.1), (1.1.6); Stanford Weil II seminar L19, Proposition 1.1.9.
(blueprint: new-e7-rational-galois-construction).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] lisseRationalFiberFunctor

set_option genSizeOfSpec false in
set_option genInjectivity false in
variable {Y : Scheme.{u}} [ConnectedSpace Y]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
  [IsFundamentalGroup (FiniteEtale.fiber y) G]
  (c : GaloisLisseFiniteCorrespondence y G)
  (P : ProfiniteGrp.{u}) (δ : G ≃ₜ* P)
  (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
  [∀ x : Y, Invertible (l : Y.residueField x)]
  (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (i : IntegralGaloisConstruction y G c P δ l E)

set_option maxHeartbeats 1000000 in
-- Tensor induction compares the scalar-extended action and rationalized Hom map.
open Padic in
set_option maxHeartbeats 1000000 in
-- Resolve the coefficient and representation topology instances once for localization.
set_option maxHeartbeats 1000000 in
-- The localization extensionality proof elaborates several scalar restrictions.
set_option maxHeartbeats 1000000 in
-- Transport the fixed rational fibre map through both tensor comparisons.
set_option maxHeartbeats 2000000 in
-- Clear denominators uniformly, then compare maps after localization.
set_option maxHeartbeats 3000000 in
-- Transport a stable lattice through the integral equivalence and base change.
set_option maxHeartbeats 2000000 in
-- Elaborate the rational Hom injection through the representation category.
set_option maxHeartbeats 2000000 in
-- Assemble the equivalence with the chosen fibre functor and its normalization.
end AlgebraicGeometry.Scheme
