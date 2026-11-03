/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralCoefficientComparison.ScalarSystems.IntegralAdjointScalarSystems
public import WeilConjectures.AlgebraicGeometry.IntegralCoefficientComparison.IntegralAdjointTateScalarData
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Finite-free comparison of the reconstructed integral adjoints

Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md, (1)--(2).
The coefficient fields lie in a fixed algebraic closure of Q_l, independently of
geometric k. All comparisons below use their inclusions, not arbitrary ring maps.
(blueprint: lem-pur-integral-adjoint-finite-free-coefficient-comparison).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.IntegralCoefficientComparison
open IntegralDirectImageTower CurrentNativeIntegralTower

variable (ell : ℕ) [Fact ell.Prime] (Ω : Type u) [Field Ω]
  [Algebra (Padic ell) Ω] [IsAlgClosure (Padic ell) Ω]

/-- The fixed inclusions of coefficient fields.
Source: (1), E ⊂ F (blueprint: lem-pur-integral-adjoint-finite-free-coefficient-comparison). -/
abbrev inc {E F : Padic.FiniteCoefficientFields ell Ω} (h : E ≤ F) :=
  IntermediateField.inclusion h

variable (s : ∀ E : Padic.FiniteCoefficientFields ell Ω, Presentation ell E.val)

/-- Forget normalization, retaining the original whole derived tower and its maps.
Source: (2), normalized towers
(blueprint: lem-pur-integral-adjoint-finite-free-coefficient-comparison). -/
def normInclusion (E : Padic.FiniteCoefficientFields ell Ω) (T : Scheme.{u}) :
    spNormalizedConstructibleTorTowerCategory ell E.val T ((s E).towers T) ⥤
      Towers ell E.val (s E) T :=
  ObjectProperty.lift _ (spNormalizedConstructibleTorTowers ell E.val T
    ((s E).towers T)).ι (fun M ↦ M.property.1)

/-- Restrict native scalar extension to Dbc without changing its objects or arrows.
Source: (1), constructibility preservation
(blueprint: lem-pur-integral-adjoint-finite-free-coefficient-comparison). -/
def scalarBc {E F : Padic.FiniteCoefficientFields ell Ω} (h : E ≤ F) (T : Scheme.{u})
    (closed : ∀ M : Constructible ell E.val T,
      constantModelBoundedConstructible (spIntegralCondensed ell F.val) T
        ((scalar ell E.val F.val (inc ell Ω h) T).obj M.obj)) :
    Constructible ell E.val T ⥤ Constructible ell F.val T :=
  ObjectProperty.lift _
    ((constantModelBoundedConstructible (spIntegralCondensed ell E.val) T).ι ⋙
      scalar ell E.val F.val (inc ell Ω h) T) closed

/-- Reconstruct P from its prescribed reduction comparison. The first arrow is
exactly the completion unit of the normalized reduction/total-limit adjunction.
Source: (2), realization of tower b
(blueprint: lem-pur-integral-adjoint-finite-free-coefficient-comparison). -/
def supportRealization (E : Padic.FiniteCoefficientFields ell Ω)
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (e : Edge ell E.val (s E) c) (M : Constructible ell E.val X)
    (hu : IsIso ((redLimitAdjunction ell E.val (s E) Y e.integral.limitY).unit.app
      (e.P.obj M).obj)) :
    (e.P.obj M).obj ≅ (lim ell E.val (s E) Y e.integral.limitY).obj
      ((towerSupport ell E.val (s E) c e.support_closed).obj
        ((reduction ell E.val (s E) X e.integral.reductionX).obj M)).obj :=
  letI := hu
  asIso ((redLimitAdjunction ell E.val (s E) Y e.integral.limitY).unit.app
      (e.P.obj M).obj) ≪≫
    (lim ell E.val (s E) Y e.integral.limitY).mapIso
      ((spConstructibleTorTowers ell E.val Y ((s E).towers Y)).ι.mapIso
        (e.integral.leftComparison.app M))

set_option maxHeartbeats 5000000 in
-- Elaborating the component equations expands several actual derived adjunctions.
end AlgebraicGeometry.ProEtale.IntegralCoefficientComparison
