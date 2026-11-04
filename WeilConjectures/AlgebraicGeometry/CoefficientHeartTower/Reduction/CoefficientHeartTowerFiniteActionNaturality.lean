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

/-! # Naturality of the finite geometric-fibre action

Source: coefficient-heart proof (1), the reductions of a morphism are equivariant.
(blueprint: lem-sfb-coefficient-heart-finite-action-naturality)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.CoefficientHeartTower
variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
variable {pi : A} {M N : Modules A X}

/-- Maps of finite etale reductions commute with the prescribed action on their stalks.
Source: naturality of the automorphisms of the FLC fibre functor and of the forgetful stalk
comparison, coefficient-heart proof (1).
(blueprint: lem-sfb-coefficient-heart-finite-action-naturality)
Proof: transport to the underlying set stalks by the canonical comparison. Naturality of a
fibre-functor automorphism gives the commuting square there. Naturality of the comparison
transports its two sides back to the module stalks. -/
theorem Reduction.finiteAction_natural (R : Reduction A X pi M) (S : Reduction A X pi N)
    (v : Spec (.of Ω) ⟶ X) (g : Aut (Scheme.flcFiber v)) (n m : ℕ)
    (f : R.etale.obj (op n) ⟶ S.etale.obj (op m)) (p : (R.fibres A v).obj (op n)) :
    (Scheme.pointSmallEtale v).sheafFiber.map f (R.finiteAction A v g n p) =
      S.finiteAction A v g m ((Scheme.pointSmallEtale v).sheafFiber.map f p) := by
  let : PreservesColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u, u, u} A
  let : PreservesFilteredColimitsOfSize.{u, u} (forget Ab.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u + 1} A)) :=
    comp_preservesFilteredColimits
      (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}) (forget Ab.{u + 1})
  let c := (Scheme.pointSmallEtale v).sheafFiberCompIso (forget (ModuleCat.{u + 1} A))
  let F : X.FLC := ⟨(etaleSet A X).obj (R.etale.obj (op n)), R.finiteLocallyConstant n⟩
  let G : X.FLC := ⟨(etaleSet A X).obj (S.etale.obj (op m)), S.finiteLocallyConstant m⟩
  let q : F ⟶ G := ObjectProperty.homMk ((etaleSet A X).map f)
  have hn := ConcreteCategory.congr_hom (g.hom.naturality q)
    ((c.inv.app (R.etale.obj (op n))) p)
  have hc := ConcreteCategory.congr_hom (c.hom.naturality f)
    (g.hom.app F ((c.inv.app (R.etale.obj (op n))) p))
  have hi := ConcreteCategory.congr_hom (c.inv.naturality f) p
  change (Scheme.pointSmallEtale v).sheafFiber.map f
      ((c.hom.app (R.etale.obj (op n)))
        (g.hom.app F ((c.inv.app (R.etale.obj (op n))) p))) =
    (c.hom.app (S.etale.obj (op m))) (g.hom.app G
      ((c.inv.app (S.etale.obj (op m))) ((Scheme.pointSmallEtale v).sheafFiber.map f p)))
  change (g.hom.app G) ((Scheme.flcFiber v).map q
      ((c.inv.app (R.etale.obj (op n))) p)) =
    (Scheme.flcFiber v).map q
      ((g.hom.app F) ((c.inv.app (R.etale.obj (op n))) p)) at hn
  change (c.hom.app (S.etale.obj (op m)))
      ((Scheme.flcFiber v).map q
        ((g.hom.app F) ((c.inv.app (R.etale.obj (op n))) p))) =
    (Scheme.pointSmallEtale v).sheafFiber.map f
      ((c.hom.app (R.etale.obj (op n)))
        ((g.hom.app F) ((c.inv.app (R.etale.obj (op n))) p))) at hc
  change (c.inv.app (S.etale.obj (op m)))
      ((Scheme.pointSmallEtale v).sheafFiber.map f p) =
    (Scheme.flcFiber v).map q ((c.inv.app (R.etale.obj (op n))) p) at hi
  rw [← hc, hi]
  exact congrArg (c.hom.app (S.etale.obj (op m))) hn.symm

end AlgebraicGeometry.ProEtale.CoefficientHeartTower
