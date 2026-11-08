/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Submission.WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Submission.WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import Submission.WeilConjectures.CategoryTheory.CommAlgebraSheafModule
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Submission.WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import Submission.WeilConjectures.AlgebraicGeometry.Coherent
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.CategoryTheory.Sites.LeftExact
import Submission.WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion
import Submission.WeilConjectures.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange
import Submission.WeilConjectures.RingTheory.SymmetricAlgebraBaseChange
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Submission.WeilConjectures.AlgebraicGeometry.Curve.AlgebraTensorPullbackComparison
import Submission.WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitQuotient
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Graded algebra and quotient of tensor powers

Source: Stacks Project, Tag 09MS, the direct-sum algebra sequence.
(blueprint: lem-sc-tensor-graded-algebra-data).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section

/-- The underlying module map, with its source and target stated explicitly.
Source: Stacks Project, Tag 09MS, the quotient in the graded ideal sequence.
(blueprint: lem-sc-square-zero-tensor-graded-presentation). -/
def tensorGradedAlgebraMap {X : Scheme.{u}} {B C : X.CommAlgebraSheaf} (p : B ⟶ C) :
    commAlgebraSheafModule X.sheaf B ⟶ commAlgebraSheafModule X.sheaf C :=
  (commAlgebraSheafModuleFunctor X.sheaf).map p

/-- Read a section of the underlying module as a section of the algebra sheaf.
Source: Stacks Project, Tag 09MS, the graded ideal sequence.
(blueprint: lem-sc-square-zero-tensor-graded-presentation). -/
def tensorGradedAlgebraSection {X : Scheme.{u}} (B : X.CommAlgebraSheaf) (U : X.Opens)
    (z : Γ(commAlgebraSheafModule X.sheaf B, U)) : B.right.obj.obj (op U) := z

attribute [local irreducible] tensorGradedAlgebraMap commAlgebraSheafModule

/-- The chosen tensor-pullback unit, with a compact explicit module-map type.
Source: Stacks Project, Tag 0096, the tensor-pullback adjunction.
(blueprint: lem-sc-square-zero-tensor-graded-presentation). -/
def tensorGradedUnit {X Z : Scheme.{u}} (j : Z ⟶ X) (M : X.Modules) :
    M ⟶ (pushforward j).obj ((tensorPullback j).obj M) :=
  (Classical.choose (exists_tensorPullbackAdjunction j)).unit.app M

attribute [local irreducible] tensorGradedUnit tensorPullback

/-- The two graded algebra sheaves, with their underlying module coproducts.
No exactness, kernel, or degree projection data are included.
Source: Stacks Project, Tag 09MS, the direct-sum algebra sequence.
(blueprint: lem-sc-tensor-graded-algebra-data). -/
structure TensorGradedAlgebraData {X Z : Scheme.{u}} (j : Z ⟶ X)
    (L : X.Modules) where
  B : X.CommAlgebraSheaf
  C : X.CommAlgebraSheaf
  p : B ⟶ C
  b : ∀ d : ℕ, L.tensorPow d ⟶ commAlgebraSheafModule X.sheaf B
  c : ∀ d : ℕ,
    (pushforward j).obj ((tensorPullback j).obj (L.tensorPow d)) ⟶
      commAlgebraSheafModule X.sheaf C
  b_colimit : IsColimit (Cofan.mk (commAlgebraSheafModule X.sheaf B) b)
  c_colimit : IsColimit (Cofan.mk (commAlgebraSheafModule X.sheaf C) c)
  b_quotient : ∀ d : ℕ, b d ≫ tensorGradedAlgebraMap p =
    tensorGradedUnit j (L.tensorPow d) ≫ c d
  b_multiply : ∀ (U : X.Opens) (a d : ℕ) (s : Γ(L.tensorPow a, U))
    (t : Γ(L.tensorPow d, U)),
    tensorGradedAlgebraSection B U ((b a).app U s) *
      tensorGradedAlgebraSection B U ((b d).app U t) =
      tensorGradedAlgebraSection B U
        ((b (a + d)).app U ((L.tensorPowAddIso a d).inv.app U (tmulSection s t)))

end
end AlgebraicGeometry.Scheme.Modules
