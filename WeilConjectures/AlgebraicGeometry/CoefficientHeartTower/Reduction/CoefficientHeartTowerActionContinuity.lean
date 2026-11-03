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
import Mathlib.Topology.Constructions.SumProd

/-! # Continuity of the completed geometric-fibre action

Source: coefficient-heart proof (1), completed fibres and their continuous actions.
(blueprint: lem-sfb-coefficient-heart-action-continuity)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.CoefficientHeartTower

private theorem aut_evaluation_continuous {C : Type*} [Category C]
    (F : C ⥤ Type (u + 1)) (Y : C) (x : F.obj Y) :
    let : TopologicalSpace (F.obj Y) := ⊥
    Continuous (fun g : Aut F ↦ g.hom.app Y x) := by
  let : TopologicalSpace (F.obj Y) := ⊥
  have hE : Continuous (SetFunctorAut.evaluation F) := continuous_induced_dom
  have hY : Continuous (fun g : Aut F ↦ SetFunctorAut.evaluation F g Y) :=
    (continuous_apply Y).comp hE
  have hH : Continuous (fun g : Aut (F.obj Y) ↦ (g.hom : F.obj Y → F.obj Y)) :=
    continuous_induced_dom
  exact (continuous_apply x).comp (hH.comp hY)

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
variable {pi : A} {M : Modules A X}

/-- Evaluation of the finite quotient action is jointly continuous for the discrete stalk.
Source: the pointwise evaluation topology on automorphisms of the fibre functor.
(blueprint: lem-sfb-coefficient-heart-action-continuity)
Proof: at a fixed discrete stalk element, evaluation is a coordinate of the topology of
natural automorphisms. Conjugating by the forgetful stalk comparison preserves continuity.
Joint continuity follows because the stalk argument has the discrete topology. -/
theorem Reduction.finiteAction_continuous (R : Reduction A X pi M)
    (v : Spec (.of Ω) ⟶ X) (n : ℕ) :
    let : TopologicalSpace ((R.fibres A v).obj (op n)) := ⊥
    Continuous (fun z : Aut (Scheme.flcFiber v) × (R.fibres A v).obj (op n) ↦
      R.finiteAction A v z.1 n z.2) := by
  let : TopologicalSpace ((R.fibres A v).obj (op n)) := ⊥
  let : DiscreteTopology ((R.fibres A v).obj (op n)) := ⟨rfl⟩
  let : PreservesColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u, u, u} A
  let : PreservesFilteredColimitsOfSize.{u, u} (forget Ab.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u + 1} A)) :=
    comp_preservesFilteredColimits
      (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}) (forget Ab.{u + 1})
  let c := ((Scheme.pointSmallEtale v).sheafFiberCompIso
    (forget (ModuleCat.{u + 1} A))).app (R.etale.obj (op n))
  let Y : X.FLC := ⟨(etaleSet A X).obj (R.etale.obj (op n)),
    R.finiteLocallyConstant n⟩
  let : TopologicalSpace ((Scheme.flcFiber v).obj Y) := ⊥
  let : DiscreteTopology ((Scheme.flcFiber v).obj Y) := ⟨rfl⟩
  apply continuous_prod_of_discrete_right.mpr
  intro p
  exact continuous_of_discreteTopology.comp
    (aut_evaluation_continuous (Scheme.flcFiber v) Y (c.inv p))

/-- A completed-fibre action with the prescribed finite coordinates is continuous.
Source: coefficient-heart proof (1), passage from finite actions to the completed fibre.
(blueprint: lem-sfb-coefficient-heart-action-continuity)
Proof: continuity into an induced product topology is checked coordinatewise. Each coordinate
is the finite action applied to the continuous quotient projection; the preceding theorem
makes this a continuous function of the group element and the completed-fibre element. -/
theorem Reduction.actionContinuous_of_projection (R : Reduction A X pi M)
    (v : Spec (.of Ω) ⟶ X) (rho : Aut (Scheme.flcFiber v) →* Aut (R.fibre A v))
    (h : ∀ (g : Aut (Scheme.flcFiber v)) (p : R.fibre A v) (n : ℕ),
      limit.π (R.fibres A v) (op n) ((rho g).hom p) =
        R.finiteAction A v g n (limit.π (R.fibres A v) (op n) p)) :
    R.ActionContinuous A v rho := by
  let : ∀ n : ℕ, TopologicalSpace ((R.fibres A v).obj (op n)) := fun _ ↦ ⊥
  let := R.fibreTopology A v
  change Continuous (fun z : Aut (Scheme.flcFiber v) × R.fibre A v ↦ (rho z.1).hom z.2)
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro n
  let : TopologicalSpace ((R.fibres A v).obj (op n)) := ⊥
  have hi : Continuous (fun p : R.fibre A v ↦
      (fun k : ℕ ↦ limit.π (R.fibres A v) (op k) p)) :=
    continuous_induced_dom (f := fun p : R.fibre A v ↦
      (fun k : ℕ ↦ limit.π (R.fibres A v) (op k) p))
  have hp : Continuous (fun p : R.fibre A v ↦ limit.π (R.fibres A v) (op n) p) :=
    (continuous_apply n).comp hi
  exact ((R.finiteAction_continuous v n).comp
    (continuous_fst.prodMk (hp.comp continuous_snd))).congr (fun z ↦ (h z.1 z.2 n).symm)

end AlgebraicGeometry.ProEtale.CoefficientHeartTower
