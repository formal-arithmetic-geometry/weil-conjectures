/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseRepresentations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.StratifiedLattice
public import WeilConjectures.WeilObject.Sheaf.Stalk
public import WeilConjectures.RepresentationTheory.PoincareDuality.LAdic
public import WeilConjectures.AlgebraicGeometry.RegularNormalDecomposition
public import WeilConjectures.AlgebraicGeometry.ProEtaleLisseOrigin
public import WeilConjectures.AlgebraicGeometry.GaloisCategories
public import WeilConjectures.CategoryTheory.SetFunctorAut.AutProfinite
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonFiniteLevel
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import WeilConjectures.CategoryTheory.RingObjects.GlobalSections

/-! # Lisse sheaves and continuous representations

Source: latest blueprint, sec-six-functors/sk-lem-finite,
thm-lisse-qlbar-representations, clauses (1)--(5)
(blueprint: thm-lisse-qlbar-representations).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct CategoryTheory.Obj
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale
namespace LisseQlbar

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The actual fibre: pull back to the geometric point, then evaluate sections.
Source: blueprint, Fibres (blueprint: thm-lisse-qlbar-representations). -/
abbrev fibre {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    (x : Spec (.of Ω) ⟶ X) :=
  CondensedRing.upperStar Λ x ⋙
    CondensedRing.Evaluation.sections (Scheme.ProEt.topology (Spec (.of Ω)))
      (condensedRingObj Λ (Spec (.of Ω))) (Scheme.ProEt.mk (𝟙 _))

set_option maxHeartbeats 0 in
-- Large clause records contain canonical sheaf, fibre and coefficient comparison types.
set_option genSizeOfSpec false in
set_option genInjectivity false in
set_option maxHeartbeats 0 in
-- Large clause records contain canonical sheaf, fibre and coefficient comparison types.
set_option genSizeOfSpec false in
set_option genInjectivity false in
set_option maxHeartbeats 0 in
-- Large clause records contain canonical sheaf, fibre and coefficient comparison types.
set_option genSizeOfSpec false in
set_option genInjectivity false in
variable (l : ℕ) [Fact l.Prime]

set_option maxHeartbeats 0 in
-- Large clause records contain canonical sheaf, fibre and coefficient comparison types.
set_option genSizeOfSpec false in
set_option genInjectivity false in
set_option maxHeartbeats 0 in
-- Large clause records contain canonical sheaf, fibre and coefficient comparison types.
set_option genSizeOfSpec false in
set_option genInjectivity false in
end LisseQlbar
end AlgebraicGeometry.ProEtale
