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
public import Mathlib.CategoryTheory.Functor.OfSequence

/-! # The actual native scalar-cokernel diagram

Source: coefficient-heart proof (1), forming the quotients before etale descent.
(blueprint: lem-sfb-coefficient-heart-canonical-reductions)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CoefficientHeartTower
variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable {X : Scheme.{u}} (M : Modules A X)

/-- Native scalar multiplication respects multiplication in the coefficient ring.
Source: coefficient-heart proof (1), scalar quotient construction.
(blueprint: lem-sfb-coefficient-heart-canonical-reductions)
Proof: cancel the adjacent unitor and regular-module comparison isomorphisms, combine
right whiskerings and functor maps, and evaluate the resulting scalar linear maps. -/
theorem scalar_mul (a b : A) :
    scalar A X M (a * b) = scalar A X M a ≫ scalar A X M b := by
  let F := FiniteConstantModel.modelFunctor A X
  let e := modelRegularIso A X
  let f (c : A) : ModuleCat.of A (ULift.{u + 1} A) ⟶
      ModuleCat.of A (ULift.{u + 1} A) := ModuleCat.ofHom (c • LinearMap.id)
  have hf : f (a * b) = f a ≫ f b := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (a * b) • x = b • (a • x)
    rw [mul_comm, mul_smul]
  let k (c : A) : 𝟙_ (Modules A X) ⟶ 𝟙_ (Modules A X) :=
    e.inv ≫ F.map (f c) ≫ e.hom
  have hk : k (a * b) = k a ≫ k b := by
    dsimp only [k]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    simp only [hf, Functor.map_comp, Category.assoc]
  change (λ_ M).inv ≫ k (a * b) ▷ M ≫ (λ_ M).hom =
    ((λ_ M).inv ≫ k a ▷ M ≫ (λ_ M).hom) ≫
      (λ_ M).inv ≫ k b ▷ M ≫ (λ_ M).hom
  rw [hk, comp_whiskerRight]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- The quotient diagram before descent and completeness are established.
Source: coefficient-heart proof (1), actual scalar reductions.
(blueprint: lem-sfb-coefficient-heart-canonical-reductions) -/
structure ScalarReductionData (pi : A) where
  quotients : ℕᵒᵖ ⥤ Modules A X
  projection : (Functor.const ℕᵒᵖ).obj M ⟶ quotients
  killed : ∀ n : ℕ, scalar A X M (pi ^ (n + 1)) ≫ projection.app (op n) = 0
  quotient : ∀ n : ℕ, IsColimit (CokernelCofork.ofπ (projection.app (op n)) (killed n))

/-- The adjacent quotient transition is induced by the identity on the original module.
Source: coefficient-heart proof (1), quotient transitions.
(blueprint: lem-sfb-coefficient-heart-canonical-reductions)
Proof: the next scalar power factors through the preceding one. The latter is killed by
its cokernel projection, so the cokernel universal property supplies the transition. -/
def canonicalScalarTransition (pi : A) (n : ℕ) :
    cokernel (scalar A X M (pi ^ (n + 1 + 1))) ⟶
      cokernel (scalar A X M (pi ^ (n + 1))) :=
  cokernel.desc _ (cokernel.π _) (by
    rw [show pi ^ (n + 1 + 1) = pi * pi ^ (n + 1) by
      rw [pow_succ, mul_comm], scalar_mul,
      Category.assoc, cokernel.condition, comp_zero])

/-- The diagram consists of actual categorical scalar cokernels; no existence theorem
is used to choose its data.
Source: coefficient-heart proof (1), forming the reductions.
(blueprint: lem-sfb-coefficient-heart-canonical-reductions)
Proof: use the adjacent cokernel transitions in ofOpSequence. The cokernel factorization
equations make the projections a natural transformation. Their coforks are limiting by
the defining cokernel universal properties. -/
def canonicalScalarReductions (pi : A) : ScalarReductionData M pi := by
  let D := Functor.ofOpSequence
    (X := fun n ↦ cokernel (scalar A X M (pi ^ (n + 1))))
    (canonicalScalarTransition M pi)
  let q : (Functor.const ℕᵒᵖ).obj M ⟶ D :=
    NatTrans.ofOpSequence (fun n ↦ cokernel.π _) (fun n ↦ by
      simp [D, canonicalScalarTransition])
  exact
    { quotients := D
      projection := q
      killed := fun n ↦ cokernel.condition _
      quotient := fun n ↦ cokernelIsCokernel _ }

/-- The fixed scalar quotients and their descended complete structure give Reduction.
Source: coefficient-heart proof (1), retaining the actual quotient projections.
(blueprint: lem-sfb-coefficient-heart-canonical-reductions)
Proof: retain each field of the constructed quotient diagram and each supplied descent
and completeness field, without choosing any replacement objects or projections. -/
def ScalarReductionData.Completion.toReduction {M : Modules A X} {pi : A}
    {D : ScalarReductionData M pi} (C : D.Completion) : Reduction A X pi M where
  quotients := D.quotients
  projection := D.projection
  killed := D.killed
  quotient := D.quotient
  complete := C.complete
  etale := C.etale
  finiteLocallyConstant := C.finiteLocallyConstant
  annihilated := C.annihilated
  origin := C.origin
  linear := C.linear

end AlgebraicGeometry.ProEtale.CoefficientHeartTower
