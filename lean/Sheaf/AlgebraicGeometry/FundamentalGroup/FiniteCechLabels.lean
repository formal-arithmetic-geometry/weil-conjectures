/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits

/-! # Finite quotient and consecutive Cech labels

Source: Stacks Project, Tag 097D, and the cumulative-label construction of
Bhatt--Scholze, The pro-etale topology for schemes, section 7.4
(blueprint: def-sfb-finite-cech-labels).

These four definitions require no chosen universal cover and no theorem about its
coordinates. They live in their own namespace `FiniteCechLabels`: the parent assembly
`PointedLimitCech` (owner lem-sfb-pointed-finite-etale-limit-cover, which cites the
Cech-coordinate item) still declares bodies under `UniversalCover`, which are equal by `rfl`.
Its prover should switch to these and delete its copies, and must not import a module
that declares the same names.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.FiniteCechLabels

/-- The q-th power of a finite label set. Source: the consecutive-label construction in
§7.4 (blueprint: def-sfb-finite-cech-labels). -/
def labelPower (q : ℕ) : Type u ⥤ Type u where
  obj A := Fin q → A
  map f := ↾fun a ↦ f ∘ a

/-- The prescribed inverse system `N ↦ ∐_(G/N)^q T`, with quotient transition maps.
Source: Stacks 097D (blueprint: def-sfb-finite-cech-labels). -/
noncomputable def finiteLabelDiagram (T : Scheme.{u}) (G : ProfiniteGrp.{u}) (q : ℕ) :
    OpenNormalSubgroup G ⥤ Scheme.{u} :=
  ProfiniteGrp.toFiniteQuotientFunctor G ⋙ CategoryTheory.forget FiniteGrp ⋙ labelPower q ⋙
    (sigmaConst.obj T)

/-- Consecutive labels up to the i-th vertex, in their stated order.
Source: the cumulative-label formula in §7.4
(blueprint: def-sfb-finite-cech-labels). -/
def cumulativeLabel {G : Type u} [Group G] {q : ℕ} (g : Fin q → G) (i : ℕ) : G :=
  ((List.ofFn g).take i).prod

/-- Restrict a consecutive-label list along an arbitrary simplex map.
Source: the group-nerve construction in §7.4
(blueprint: def-sfb-finite-cech-labels). -/
def restrictedLabels {G : Type u} [Group G] {m n : ℕ}
    (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) (g : Fin m → G) : Fin n → G :=
  fun i ↦ (cumulativeLabel g (φ.toOrderHom i.castSucc).val)⁻¹ *
    cumulativeLabel g (φ.toOrderHom i.succ).val

end AlgebraicGeometry.Scheme.FiniteCechLabels
