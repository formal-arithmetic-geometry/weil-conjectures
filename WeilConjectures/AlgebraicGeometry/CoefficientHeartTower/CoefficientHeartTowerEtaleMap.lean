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
import WeilConjectures.AlgebraicGeometry.CoefficientHeartTower.Reduction.CoefficientHeartTowerQuotientMap
public import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
public import Mathlib.Algebra.Category.Grp.AB

/-! # Descent of maps between the finite etale reductions

Source: coefficient-heart proof (1), the reductions of the integral morphism.
(blueprint: lem-sfb-coefficient-heart-etale-map)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj TensorProduct
namespace AlgebraicGeometry.ProEtale.CoefficientHeartTower
variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable {X : Scheme.{u}} {pi : A} {M N : Modules A X}

private theorem inverse_scalar_square {C : Type*} [Category* C] {P Q : C}
    (e : P ≅ Q) (a : P ⟶ P) (b : Q ⟶ Q)
    (h : a ≫ e.hom = e.hom ≫ b) : b ≫ e.inv = e.inv ≫ a := by
  apply (cancel_mono e.hom).1
  simp only [Category.assoc, e.inv_hom_id, Category.comp_id]
  rw [h, e.inv_hom_id_assoc]

/-- The abelian descent is the preimage of the conjugated native map.
Source: full faithfulness of comparison, coefficient-heart proof (1).
(blueprint: lem-sfb-coefficient-heart-etale-map). -/
def descendedAbMapApp (R : Reduction A X pi M) (S : Reduction A X pi N)
    (q : R.quotients ⟶ S.quotients) (n : ℕᵒᵖ) :
    (etaleAb A X).obj (R.etale.obj n) ⟶ (etaleAb A X).obj (S.etale.obj n) :=
  (comparisonUpperStar Ab.{u + 1} X).preimage
    (R.origin.inv.app n ≫ (q.app n).hom ≫ S.origin.hom.app n)

/-- The comparison image of the descended map is its prescribed conjugate.
Source: full faithfulness of comparison, coefficient-heart proof (1).
(blueprint: lem-sfb-coefficient-heart-etale-map).
Proof: apply the map-preimage equation of a full functor. -/
theorem descendedAbMapApp_map (R : Reduction A X pi M)
    (S : Reduction A X pi N) (q : R.quotients ⟶ S.quotients) (n : ℕᵒᵖ) :
    (comparisonUpperStar Ab.{u + 1} X).map (descendedAbMapApp R S q n) =
      R.origin.inv.app n ≫ (q.app n).hom ≫ S.origin.hom.app n :=
  (comparisonUpperStar Ab.{u + 1} X).map_preimage _

/-- Descent commutes with scalar multiplication.
Source: coefficient-heart proof (1), finite reductions of an integral linear map.
(blueprint: lem-sfb-coefficient-heart-etale-map).
Proof: apply the faithful comparison functor, transport both scalars by the recorded
origin squares, and use naturality of native scalar multiplication. -/
theorem descendedAbMapApp_linear (R : Reduction A X pi M)
    (S : Reduction A X pi N) (q : R.quotients ⟶ S.quotients) (n : ℕᵒᵖ) (a : A) :
    (etaleAb A X).map (etaleScalar A (R.etale.obj n) a) ≫ descendedAbMapApp R S q n =
      descendedAbMapApp R S q n ≫
        (etaleAb A X).map (etaleScalar A (S.etale.obj n) a) := by
  let nu := comparisonUpperStar Ab.{u + 1} X
  have hR : nu.map ((etaleAb A X).map (etaleScalar A (R.etale.obj n) a)) ≫
      R.origin.inv.app n =
      R.origin.inv.app n ≫ (scalar A X (R.quotients.obj n) a).hom := by
    have hlin : (scalar A X (R.quotients.obj n) a).hom ≫
        (R.origin.app n).hom = (R.origin.app n).hom ≫
          nu.map ((etaleAb A X).map (etaleScalar A (R.etale.obj n) a)) :=
      R.linear n.unop a
    exact inverse_scalar_square (R.origin.app n)
      (scalar A X (R.quotients.obj n) a).hom
      (nu.map ((etaleAb A X).map (etaleScalar A (R.etale.obj n) a))) hlin
  have hq : (scalar A X (R.quotients.obj n) a).hom ≫ (q.app n).hom =
      (q.app n).hom ≫ (scalar A X (S.quotients.obj n) a).hom :=
    congrArg (fun f ↦ f.hom) (scalar_naturality (q.app n) a)
  apply nu.map_injective
  dsimp only [nu]
  simp only [Functor.map_comp, descendedAbMapApp_map, Category.assoc]
  rw [← Category.assoc _ (R.origin.inv.app n), hR, Category.assoc,
    ← Category.assoc _ (q.app n).hom, hq, Category.assoc, S.linear n.unop a]

/-- An additive sheaf map commuting with scalars is a module-sheaf map.
Source: sectionwise definition of an A-linear map.
(blueprint: lem-sfb-coefficient-heart-etale-map). -/
def liftAbLinear
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (f : (etaleAb A X).obj F ⟶ (etaleAb A X).obj G)
    (h : ∀ a : A, (etaleAb A X).map (etaleScalar A F a) ≫ f =
      f ≫ (etaleAb A X).map (etaleScalar A G a)) : F ⟶ G :=
  ⟨{ app := fun U ↦ ModuleCat.ofHom
      { toFun := f.hom.app U
        map_add' := (f.hom.app U).hom.map_add
        map_smul' := by
          intro a x
          have hx := ConcreteCategory.congr_hom (NatTrans.congr_app
            (congrArg (fun g : (etaleAb A X).obj F ⟶ (etaleAb A X).obj G ↦ g.hom)
              (h a)) U) x
          exact hx }
     naturality := fun {U V} g ↦ by
       ext x
       exact ConcreteCategory.congr_hom (f.hom.naturality g) x }⟩

omit [TopologicalSpace A] [IsTopologicalRing A] in
/-- Forgetting the linear lift recovers the specified additive map.
Source: the sectionwise construction of the lift.
(blueprint: lem-sfb-coefficient-heart-etale-map).
Proof: both transformations have the same function on every section. -/
theorem liftAbLinear_forget
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (f : (etaleAb A X).obj F ⟶ (etaleAb A X).obj G)
    (h : ∀ a : A, (etaleAb A X).map (etaleScalar A F a) ≫ f =
      f ≫ (etaleAb A X).map (etaleScalar A G a)) :
    (etaleAb A X).map (liftAbLinear F G f h) = f := by
  ext U x
  rfl

/-- A map of native quotients descends uniquely to the finite etale origins.
Source: coefficient-heart proof (1), functorial finite reductions.
(blueprint: lem-sfb-coefficient-heart-etale-map)
Proof: full faithfulness of the etale-to-pro-etale comparison descends the abelian map
conjugated by the recorded origin isomorphisms. The recorded scalar squares and naturality
of native scalar multiplication show that it commutes with every scalar. Its section maps
are therefore A-linear. Faithfulness of the comparison and of the module forgetful functor
proves naturality in the reduction index. -/
def Reduction.etaleMap (R : Reduction A X pi M) (S : Reduction A X pi N)
    (q : R.quotients ⟶ S.quotients) : R.etale ⟶ S.etale where
  app n := liftAbLinear _ _ (descendedAbMapApp R S q n)
    (descendedAbMapApp_linear R S q n)
  naturality {i j} f := by
    apply (etaleAb A X).map_injective
    apply (comparisonUpperStar Ab.{u + 1} X).map_injective
    simp only [Functor.map_comp, liftAbLinear_forget, descendedAbMapApp_map, Category.assoc]
    have hR := R.origin.inv.naturality f
    have hS := S.origin.hom.naturality f
    have hq := congrArg (fun g ↦ g.hom) (q.naturality f)
    change (comparisonUpperStar Ab.{u + 1} X).map
        ((etaleAb A X).map (R.etale.map f)) ≫ R.origin.inv.app j =
      R.origin.inv.app i ≫ (R.quotients.map f).hom at hR
    change (S.quotients.map f).hom ≫ S.origin.hom.app j = S.origin.hom.app i ≫
      (comparisonUpperStar Ab.{u + 1} X).map ((etaleAb A X).map (S.etale.map f)) at hS
    change (R.quotients.map f).hom ≫ (q.app j).hom =
      (q.app i).hom ≫ (S.quotients.map f).hom at hq
    change (comparisonUpperStar Ab.{u + 1} X).map
        ((etaleAb A X).map (R.etale.map f)) ≫
        R.origin.inv.app j ≫ (q.app j).hom ≫ S.origin.hom.app j =
      R.origin.inv.app i ≫ (q.app i).hom ≫ S.origin.hom.app i ≫
        (comparisonUpperStar Ab.{u + 1} X).map ((etaleAb A X).map (S.etale.map f))
    rw [← Category.assoc _ (R.origin.inv.app j), hR, Category.assoc,
      ← Category.assoc _ (q.app j).hom, hq, Category.assoc, hS]

/-- The descended map satisfies the canonical origin square at every finite level.
Source: the preimage equation for the fully faithful comparison.
(blueprint: lem-sfb-coefficient-heart-etale-map)
Proof: after applying the forgetful functor, the map is the preimage used in its
construction. Its image is the conjugated native quotient map; cancel the origin inverse. -/
theorem Reduction.etaleMap_natural (R : Reduction A X pi M) (S : Reduction A X pi N)
    (q : R.quotients ⟶ S.quotients) :
    R.origin.hom ≫ Functor.whiskerRight (Functor.whiskerRight (R.etaleMap S q)
      (etaleAb A X)) (comparisonUpperStar Ab.{u + 1} X) =
      Functor.whiskerRight q (Mod.forget _) ≫ S.origin.hom := by
  apply NatTrans.ext
  funext n
  change R.origin.hom.app n ≫ (comparisonUpperStar Ab.{u + 1} X).map
      ((etaleAb A X).map (liftAbLinear _ _ (descendedAbMapApp R S q n)
        (descendedAbMapApp_linear R S q n))) = _
  rw [liftAbLinear_forget, descendedAbMapApp_map, ← Category.assoc,
    ← Category.assoc, R.origin.hom_inv_id_app, Category.id_comp]
  rfl

end AlgebraicGeometry.ProEtale.CoefficientHeartTower
