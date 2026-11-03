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
import WeilConjectures.AlgebraicGeometry.CoefficientHeartTower.Reduction.CoefficientHeartTowerActionContinuity
import WeilConjectures.AlgebraicGeometry.CoefficientHeartTower.Reduction.CoefficientHeartTowerFiniteActionNaturality

/-! # Passing the normalized finite actions to the completed fibre

Source: coefficient-heart proof (1), inverse limits of the finite representations.
(blueprint: lem-sfb-coefficient-heart-limit-action)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.CoefficientHeartTower
variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
variable {pi : A} {M N : Modules A X}

/-- The finite linear automorphisms form a natural automorphism of the stalk diagram.
Source: coefficient-heart proof (1), functoriality of finite Galois actions.
(blueprint: lem-sfb-coefficient-heart-limit-action).
Naturality is precisely naturality of the normalized underlying finite actions. -/
def finiteActionIso (R : Reduction A X pi M) (v : Spec (.of Ω) ⟶ X)
    (rho : ∀ n : ℕ, Aut (Scheme.flcFiber v) →* Aut ((R.fibres A v).obj (op n)))
    (h : ∀ (n : ℕ) (g : Aut (Scheme.flcFiber v)) (p : (R.fibres A v).obj (op n)),
      ((rho n g).hom p) = R.finiteAction A v g n p)
    (g : Aut (Scheme.flcFiber v)) : Aut (R.fibres A v) :=
  NatIso.ofComponents (fun n ↦ rho n.unop g) (by
    intro i j f
    ext p
    change (rho j.unop g).hom ((R.fibres A v).map f p) =
      (R.fibres A v).map f ((rho i.unop g).hom p)
    rw [h, h]
    exact (R.finiteAction_natural R v g i.unop j.unop (R.etale.map f) p).symm)

/-- The natural diagram automorphisms respect the group operation.
Source: coefficient-heart proof (1), finite Galois actions.
(blueprint: lem-sfb-coefficient-heart-limit-action).
The group identities hold at each component because every finite action is a monoid hom. -/
def finiteActionHom (R : Reduction A X pi M) (v : Spec (.of Ω) ⟶ X)
    (rho : ∀ n : ℕ, Aut (Scheme.flcFiber v) →* Aut ((R.fibres A v).obj (op n)))
    (h : ∀ (n : ℕ) (g : Aut (Scheme.flcFiber v)) (p : (R.fibres A v).obj (op n)),
      ((rho n g).hom p) = R.finiteAction A v g n p) :
    Aut (Scheme.flcFiber v) →* Aut (R.fibres A v) where
  toFun := finiteActionIso R v rho h
  map_one' := by
    apply Iso.ext
    apply NatTrans.ext
    funext n
    exact congrArg Iso.hom (map_one (rho n.unop))
  map_mul' g k := by
    apply Iso.ext
    apply NatTrans.ext
    funext n
    exact congrArg Iso.hom (map_mul (rho n.unop) g k)

/-- The completed linear action is the image of the finite-action automorphisms under lim.
Source: coefficient-heart proof (1), completed-fibre action.
(blueprint: lem-sfb-coefficient-heart-limit-action)
The normalized finite actions are natural for every etale map, hence define automorphisms of
the entire stalk diagram. The limit functor maps these automorphisms to the displayed action. -/
def Reduction.limitAction (R : Reduction A X pi M) (v : Spec (.of Ω) ⟶ X)
    (rho : ∀ n : ℕ, Aut (Scheme.flcFiber v) →* Aut ((R.fibres A v).obj (op n)))
    (h : ∀ (n : ℕ) (g : Aut (Scheme.flcFiber v)) (p : (R.fibres A v).obj (op n)),
      ((rho n g).hom p) = R.finiteAction A v g n p) :
    Aut (Scheme.flcFiber v) →* Aut (R.fibre A v) where
  toFun g :=
    { hom := limMap (finiteActionIso R v rho h g).hom
      inv := limMap (finiteActionIso R v rho h g).inv
      hom_inv_id := by
        apply limit.hom_ext
        intro n
        simp [Category.assoc]
      inv_hom_id := by
        apply limit.hom_ext
        intro n
        simp [Category.assoc] }
  map_one' := by
    apply Iso.ext
    change limMap (finiteActionIso R v rho h 1).hom = 𝟙 _
    have he := congrArg Iso.hom (map_one (finiteActionHom R v rho h))
    change (finiteActionIso R v rho h 1).hom = 𝟙 _ at he
    rw [he]
    apply limit.hom_ext
    intro n
    simp
  map_mul' g k := by
    apply Iso.ext
    change limMap (finiteActionIso R v rho h (g * k)).hom =
      limMap (finiteActionIso R v rho h k).hom ≫
        limMap (finiteActionIso R v rho h g).hom
    have he := congrArg Iso.hom (map_mul (finiteActionHom R v rho h) g k)
    change (finiteActionIso R v rho h (g * k)).hom =
      (finiteActionIso R v rho h k).hom ≫ (finiteActionIso R v rho h g).hom at he
    rw [he]
    apply limit.hom_ext
    intro n
    simp [Category.assoc]

/-- Projection from the limit action is exactly the prescribed finite action.
Source: naturality of the universal limit cone.
(blueprint: lem-sfb-coefficient-heart-limit-action)
Proof: the limMap projection equation gives the component of the diagram automorphism, and
its supplied normalization identifies that component with the finite fibre action. -/
theorem Reduction.limitAction_projection (R : Reduction A X pi M)
    (v : Spec (.of Ω) ⟶ X)
    (rho : ∀ n : ℕ, Aut (Scheme.flcFiber v) →* Aut ((R.fibres A v).obj (op n)))
    (h : ∀ (n : ℕ) (g : Aut (Scheme.flcFiber v)) (p : (R.fibres A v).obj (op n)),
      ((rho n g).hom p) = R.finiteAction A v g n p)
    (g : Aut (Scheme.flcFiber v)) (p : R.fibre A v) (n : ℕ) :
    limit.π (R.fibres A v) (op n) ((R.limitAction v rho h g).hom p) =
      R.finiteAction A v g n (limit.π (R.fibres A v) (op n) p) := by
  change limit.π (R.fibres A v) (op n)
      (limMap (finiteActionIso R v rho h g).hom p) = _
  have hp := ConcreteCategory.congr_hom (limMap_π (finiteActionIso R v rho h g).hom (op n)) p
  exact hp.trans (h n g _)

/-- The constructed action is continuous in the inverse-limit topology.
Source: coefficient-heart proof (1), continuity checked on finite projections.
(blueprint: lem-sfb-coefficient-heart-limit-action)
Proof: apply the coordinate continuity theorem to the preceding projection equation. -/
theorem Reduction.limitAction_continuous (R : Reduction A X pi M)
    (v : Spec (.of Ω) ⟶ X)
    (rho : ∀ n : ℕ, Aut (Scheme.flcFiber v) →* Aut ((R.fibres A v).obj (op n)))
    (h : ∀ (n : ℕ) (g : Aut (Scheme.flcFiber v)) (p : (R.fibres A v).obj (op n)),
      ((rho n g).hom p) = R.finiteAction A v g n p) :
    R.ActionContinuous A v (R.limitAction v rho h) :=
  R.actionContinuous_of_projection v _ (R.limitAction_projection v rho h)

/-- The inverse limit of an etale map of reductions is equivariant for the limit actions.
Source: coefficient-heart proof (1), the equivariant completed-fibre matrix.
(blueprint: lem-sfb-coefficient-heart-limit-action)
Proof: compare after every target limit projection. Both sides become the same finite stalk
map by naturality of the finite action and the normalized limit-action projection equation. -/
theorem Reduction.limitAction_equivariant (R : Reduction A X pi M)
    (S : Reduction A X pi N) (v : Spec (.of Ω) ⟶ X)
    (rhoR : ∀ n : ℕ, Aut (Scheme.flcFiber v) →* Aut ((R.fibres A v).obj (op n)))
    (hR : ∀ (n : ℕ) (g : Aut (Scheme.flcFiber v)) (p : (R.fibres A v).obj (op n)),
      ((rhoR n g).hom p) = R.finiteAction A v g n p)
    (rhoS : ∀ n : ℕ, Aut (Scheme.flcFiber v) →* Aut ((S.fibres A v).obj (op n)))
    (hS : ∀ (n : ℕ) (g : Aut (Scheme.flcFiber v)) (p : (S.fibres A v).obj (op n)),
      ((rhoS n g).hom p) = S.finiteAction A v g n p)
    (f : R.etale ⟶ S.etale) (g : Aut (Scheme.flcFiber v)) :
    (R.limitAction v rhoR hR g).hom ≫
        limMap (Functor.whiskerRight f (Scheme.pointSmallEtale v).sheafFiber) =
      limMap (Functor.whiskerRight f (Scheme.pointSmallEtale v).sheafFiber) ≫
        (S.limitAction v rhoS hS g).hom := by
  apply limit.hom_ext
  intro n
  ext p
  have he := ConcreteCategory.congr_hom
    (limMap_π (Functor.whiskerRight f (Scheme.pointSmallEtale v).sheafFiber) n)
  change ∀ x : R.fibre A v,
    limit.π (S.fibres A v) n
      (limMap (Functor.whiskerRight f (Scheme.pointSmallEtale v).sheafFiber) x) =
    (Scheme.pointSmallEtale v).sheafFiber.map (f.app n)
      (limit.π (R.fibres A v) n x) at he
  change limit.π (S.fibres A v) n
      (limMap (Functor.whiskerRight f (Scheme.pointSmallEtale v).sheafFiber)
        ((R.limitAction v rhoR hR g).hom p)) =
    limit.π (S.fibres A v) n
      ((S.limitAction v rhoS hS g).hom
        (limMap (Functor.whiskerRight f (Scheme.pointSmallEtale v).sheafFiber) p))
  rw [he, R.limitAction_projection, S.limitAction_projection, he]
  exact R.finiteAction_natural S v g n.unop n.unop (f.app n) _

end AlgebraicGeometry.ProEtale.CoefficientHeartTower
