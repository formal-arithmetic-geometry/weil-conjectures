/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
public import WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.Curve.FLCFiber
public import WeilConjectures.AlgebraicGeometry.Curve.PointedEtaleStalk
public import WeilConjectures.AlgebraicGeometry.ProEtaleObjectPullbackRestriction
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.CategoryTheory.Sites.UnitHomEval
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTower.FiniteEtaleSurjectiveLimitCover
import WeilConjectures.AlgebraicGeometry.Limits.AffineOverLimitProperties

/-! # The connected pro-etale limit of pointed finite stages

Source: coefficient-heart proof (1), inverse limit of the connected finite etale covers.
(blueprint: lem-sfb-coefficient-heart-scheme-limit)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj TensorProduct
namespace AlgebraicGeometry.ProEtale.CoefficientHeartTower

/-- The finite stages of a pointed connected tower, before taking their scheme limit.
Source: coefficient-heart proof (1), compatible pointed finite covers.
(blueprint: lem-sfb-coefficient-heart-scheme-limit). -/
structure FinitePointedTower {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (v : Spec (.of Ω) ⟶ X) where
  diagram : ℕᵒᵖ ⥤ Over X
  finite : ∀ n : ℕ, IsFinite (diagram.obj (op n)).hom
  etale : ∀ n : ℕ, Etale (diagram.obj (op n)).hom
  surjective : ∀ n : ℕ, Surjective (diagram.obj (op n)).hom
  connected : ∀ n : ℕ, ConnectedSpace (diagram.obj (op n)).left
  transitionFinite : ∀ n : ℕ, IsFinite (diagram.map (homOfLE (Nat.le_succ n)).op).left
  transitionEtale : ∀ n : ℕ, Etale (diagram.map (homOfLE (Nat.le_succ n)).op).left
  transitionSurjective : ∀ n : ℕ,
    Surjective (diagram.map (homOfLE (Nat.le_succ n)).op).left
  point : ∀ n : ℕ, Spec (.of Ω) ⟶ (diagram.obj (op n)).left
  point_base : ∀ n : ℕ, point n ≫ (diagram.obj (op n)).hom = v
  point_transition : ∀ n : ℕ,
    point (n + 1) ≫ (diagram.map (homOfLE (Nat.le_succ n)).op).left = point n

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

/-- The actual limiting cone and its covering properties, without any choice of finite stages.
Source: coefficient-heart proof (1), the connected pro-etale limit cover.
(blueprint: lem-sfb-coefficient-heart-scheme-limit). -/
structure FinitePointedTower.LimitData {v : Spec (.of Ω) ⟶ X} (T : FinitePointedTower v) where
  cone : Cone T.diagram
  isLimit : IsLimit ((Over.forget X).mapCone cone)
  connected : ConnectedSpace cone.pt.left
  surjective : Surjective cone.pt.hom
  weaklyEtale : WeaklyEtale cone.pt.hom
  covering : Presieve.singleton (MorphismProperty.Over.homMk
    (A := MorphismProperty.Over.mk ⊤ cone.pt.hom weaklyEtale)
    (B := Scheme.ProEt.mk (𝟙 X)) cone.pt.hom (Category.comp_id _)) ∈
      Scheme.ProEt.precoverage X (Scheme.ProEt.mk (𝟙 X))

/-- A pointed connected finite-etale tower over an affine base has the required actual limit.
Source: coefficient-heart proof (1), connected inverse-limit covering; Stacks Tags 01YW,
097N and 0CUF.
(blueprint: lem-sfb-coefficient-heart-scheme-limit)
Proof: the finite-etale surjective limit-cover theorem gives an actual cone, its universal
property, surjectivity, weak etaleness and singleton covering condition. Finite stages over
an affine base are affine, hence quasi-compact and quasi-separated; all transition maps
are affine. Apply connectedness of cofiltered limits of connected qcqs schemes. Its clopen
partition argument is the topological form of the idempotent argument in the node's plan.
The harmless universe lift of the natural-number index fits the small diagram theorem. -/
theorem FinitePointedTower.existsLimitData [IsAffine X] {v : Spec (.of Ω) ⟶ X}
    (T : FinitePointedTower v) : Nonempty T.LimitData := by
  obtain ⟨c, ⟨hc⟩, _, hs, ⟨hw, hcover⟩, _⟩ :=
    exists_finiteEtale_surjective_limit_cover T.diagram T.finite T.etale T.surjective
      T.transitionFinite T.transitionEtale T.transitionSurjective
  let e : ULift.{u} ℕ ≌ ℕ := ULift.orderIso.equivalence
  let D := e.functor.op ⋙ T.diagram ⋙ Over.forget X
  have (i : (ULift.{u} ℕ)ᵒᵖ) : IsFinite (T.diagram.obj (op i.unop.down)).hom :=
    T.finite i.unop.down
  have (i : (ULift.{u} ℕ)ᵒᵖ) : IsAffine (D.obj i) :=
    isAffine_of_isAffineHom (T.diagram.obj (op i.unop.down)).hom
  have (i : (ULift.{u} ℕ)ᵒᵖ) : CompactSpace (D.obj i) := inferInstance
  have (i : (ULift.{u} ℕ)ᵒᵖ) : QuasiSeparatedSpace (D.obj i) := inferInstance
  have (i : (ULift.{u} ℕ)ᵒᵖ) : ConnectedSpace (D.obj i) := T.connected i.unop.down
  have {i j : (ULift.{u} ℕ)ᵒᵖ} (f : i ⟶ j) : IsAffineHom (D.map f) := by
    let g := T.diagram.map (e.functor.op.map f)
    have : IsFinite (T.diagram.obj (op j.unop.down)).hom := T.finite j.unop.down
    have : IsFinite (g.left ≫ (T.diagram.obj (op j.unop.down)).hom) := by
      change IsFinite (g.left ≫ (T.diagram.obj (e.functor.op.obj j)).hom)
      rw [Over.w g]
      exact T.finite i.unop.down
    have : IsFinite g.left := IsFinite.of_comp _ (T.diagram.obj (op j.unop.down)).hom
    change IsAffineHom g.left
    infer_instance
  have : IsCofiltered (ULift.{u} ℕ)ᵒᵖ := IsCofiltered.of_equivalence e.op.symm
  have hconn : ConnectedSpace c.pt.left :=
    Scheme.connectedSpace_of_isLimit D (hc.whiskerEquivalence e.op)
  exact ⟨⟨c, hc, hconn, hs, hw, hcover⟩⟩

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable {pi : A} {M : Modules A X}

/-- A finite stage considered as an object of the small etale site.
Source: coefficient-heart proof (1), pointed finite trivializations.
(blueprint: lem-sfb-coefficient-heart-scheme-limit). -/
def FinitePointedTower.object {v : Spec (.of Ω) ⟶ X} (T : FinitePointedTower v)
    (n : ℕ) : X.Etale :=
  MorphismProperty.Over.mk ⊤ (T.diagram.obj (op n)).hom (T.etale n)

/-- The adjacent etale arrow between finite stages.
Source: coefficient-heart proof (1), compatible pointed trivializations.
(blueprint: lem-sfb-coefficient-heart-scheme-limit). -/
def FinitePointedTower.arrow {v : Spec (.of Ω) ⟶ X} (T : FinitePointedTower v)
    (n : ℕ) : T.object (n + 1) ⟶ T.object n :=
  MorphismProperty.Over.homMk (T.diagram.map (homOfLE (Nat.le_succ n)).op).left (Over.w _)

end AlgebraicGeometry.ProEtale.CoefficientHeartTower
