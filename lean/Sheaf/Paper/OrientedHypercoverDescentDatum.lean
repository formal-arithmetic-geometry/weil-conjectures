/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q63
-/
module

public import Sheaf.Paper.OrientedNearbyCycles
public import Sheaf.CategoryTheory.ConstantRingModuleSheaves
public import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import WeilConjectures.CategoryTheory.Abelian.Filtration

/-!
# Oriented hypercover spectral-sequence data and canonical comparison maps

Source: Orgogozo, Modifications et cycles proches sur une base générale, §9.2,
printed p. 22; Stacks Project, Tags 0DHL and 0D7F
(blueprint: def-trf-oriented-hypercover-descent-datum).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v w v₁ w₁

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.AdicSites

namespace AlgebraicGeometry.OrientedNearbyCycles.Hypercover

/-- Canonically read transported constant modules on the original étale site.
This reuses the recorded scalar/site transport without changing the module action.
Source: ILO XI §4.3; Stacks 03CY
(blueprint: def-trf-oriented-hypercover-descent-datum). -/
def readModules (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :
    (etaleDatum.{u, u + 1} X).modules (Coeff.{u, u + 1} Λ) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u, u + 1} Λ)) :=
  haveI : (AsSmall.up : X.Etale ⥤ EtaleSite.{u, u + 1} X).IsContinuous
      X.smallEtaleTopology (etaleTopology X) :=
    inferInstanceAs ((AsSmall.equiv : X.Etale ≌ EtaleSite.{u, u + 1} X).functor.IsContinuous
      X.smallEtaleTopology
      ((AsSmall.equiv : X.Etale ≌ EtaleSite.{u, u + 1} X).inverse.inducedTopology
        X.smallEtaleTopology))
  SheafOfModules.restrictScalars
      (CategoryTheory.realizationRingIso (etaleTopology X) (Coeff.{u, u + 1} Λ)).inv ⋙
    CategoryTheory.constantRingModuleRestriction (etaleTopology X) (Coeff.{u, u + 1} Λ) ⋙
    (AsSmall.up : X.Etale ⥤ EtaleSite.{u, u + 1} X).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (Coeff.{u, u + 1} Λ)) X.smallEtaleTopology (etaleTopology X)

/-- Exactness of the canonical site/scalar reading functor.
Source: ILO XI §4.3; Stacks 03CY
(blueprint: def-trf-oriented-hypercover-descent-datum).
Proof: restriction along realizationRingIso is an additive equivalence. The constant-ring
module equivalence identifies its second factor with fixed-ring module sheaves. Finally
AsSmall is an equivalence of sites, so its sheaf functor is an additive equivalence too.
Consequently the composite preserves addition, finite limits and finite colimits. -/
theorem readModules_exact (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :
    (readModules X Λ).Additive ∧ PreservesFiniteLimits (readModules X Λ) ∧
      PreservesFiniteColimits (readModules X Λ) := by
  sorry

/-- Additivity of the recorded transport. Source: ILO XI §4.3; Stacks 03CY
(blueprint: def-trf-oriented-hypercover-descent-datum). -/
instance readModules_additive (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :
    (readModules X Λ).Additive := (readModules_exact X Λ).1

/-- Left exactness of the recorded transport. Source: ILO XI §4.3; Stacks 03CY
(blueprint: def-trf-oriented-hypercover-descent-datum). -/
instance readModules_finiteLimits (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :
    PreservesFiniteLimits (readModules X Λ) := (readModules_exact X Λ).2.1

/-- Right exactness of the recorded transport. Source: ILO XI §4.3; Stacks 03CY
(blueprint: def-trf-oriented-hypercover-descent-datum). -/
instance readModules_finiteColimits (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :
    PreservesFiniteColimits (readModules X Λ) := (readModules_exact X Λ).2.2

/-- The degree-i augmentation, as an arrow in schemes. Source: Stacks 0DHL
(blueprint: def-trf-oriented-hypercover-descent-datum). -/
abbrev epsilon {X : Scheme.{u}} (Y : SimplicialObject (Over X)) (i : ℕ) :=
  (Y.obj (op (SimplexCategory.mk i))).hom

/-- The square equation for a degree augmentation. Source: Orgogozo §9.2
(blueprint: def-trf-oriented-hypercover-descent-datum). -/
abbrev epsilon_comm {X S : Scheme.{u}} (f : X ⟶ S)
    (Y : SimplicialObject (Over X)) (i : ℕ) :
    epsilon Y i ≫ f = (epsilon Y i ≫ f) ≫ 𝟙 S := (Category.comp_id _).symm

/-- The induced map of vanishing topoi in degree i, using the universal square lift.
Source: Orgogozo §9.2; ILO XI §1.9
(blueprint: def-trf-oriented-hypercover-descent-datum). -/
abbrev orientedEpsilon {X S : Scheme.{u}} (f : X ⟶ S)
    (Y : SimplicialObject (Over X)) (i : ℕ) :=
  squareModules.{u, u + 1} f (epsilon Y i ≫ f) (epsilon Y i) (𝟙 S)
    (epsilon_comm f Y i)

/-- The degree-i coefficient complex is the exact inverse image of K.
Source: Orgogozo §9.2 (blueprint: def-trf-oriented-hypercover-descent-datum). -/
abbrev coefficient {X : Scheme.{u}} (Y : SimplicialObject (Over X))
    (Λ : Type (u + 1)) [CommRing Λ] (K : EtaleDerived X Λ) (i : ℕ) :=
  ((etaleModules.{u, u + 1} (epsilon Y i)).pull (Coeff.{u, u + 1} Λ)).obj K

/-- The derived object whose j-th cohomology is E_1^{i,j}.
Source: Orgogozo §9.2, printed p. 22
(blueprint: def-trf-oriented-hypercover-descent-datum). -/
abbrev term {X S : Scheme.{u}} (f : X ⟶ S) (Y : SimplicialObject (Over X))
    (Λ : Type (u + 1)) [CommRing Λ] (K : EtaleDerived X Λ) (i : ℕ) :=
  ((orientedEpsilon f Y i).push (Coeff.{u, u + 1} Λ)).obj
    ((nearbyCycles.{u, u + 1} (epsilon Y i ≫ f) Λ).obj (coefficient Y Λ K i))

/-- The canonical degree-i augmentation: the transpose of beta, under the same
adjunction used by the nearby-cycle definition. Mate pasting identifies this with
Rpsi_f of the ordinary descent unit followed by derived-composition comparison.
Source: Orgogozo §9.2; Stacks 0D6E, 09T5
(blueprint: def-trf-oriented-hypercover-descent-datum). -/
def augmentation {X S : Scheme.{u}} (f : X ⟶ S) (Y : SimplicialObject (Over X))
    (Λ : Type (u + 1)) [CommRing Λ] (K : EtaleDerived X Λ) (i : ℕ) :
    (nearbyCycles.{u, u + 1} f Λ).obj K ⟶ term f Y Λ K i :=
  ((orientedEpsilon f Y i).adj (Coeff.{u, u + 1} Λ)).homEquiv _ _
    (baseChange.{u, u + 1} f (epsilon Y i ≫ f) (epsilon Y i) (𝟙 S)
      (epsilon_comm f Y i) Λ K)

/-- Projection comparison for a composite of induced oriented maps: first projection.
Source: ILO XI §§1.4, 1.9 (blueprint: def-trf-oriented-hypercover-descent-datum). -/
def compositeFirst {X₀ S₀ X₁ S₁ X₂ S₂ : Scheme.{u}}
    (f₀ : X₀ ⟶ S₀) (f₁ : X₁ ⟶ S₁) (f₂ : X₂ ⟶ S₂)
    (h₁ : X₁ ⟶ X₀) (g₁ : S₁ ⟶ S₀) (w₁ : h₁ ≫ f₀ = f₁ ≫ g₁)
    (h₂ : X₂ ⟶ X₁) (g₂ : S₂ ⟶ S₁) (w₂ : h₂ ≫ f₁ = f₂ ≫ g₂) :
    (((squareMorphism.{u, u + 1} f₁ f₂ h₂ g₂ w₂).comp
      (squareMorphism.{u, u + 1} f₀ f₁ h₁ g₁ w₁)).comp (p₁.{u, u + 1} f₀)).direct ≅
        ((p₁.{u, u + 1} f₂).comp (etaleMorphism.{u, u + 1} (h₂ ≫ h₁))).direct :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (squareMorphism.{u, u + 1} f₁ f₂ h₂ g₂ w₂).direct
      (squareLift.{u, u + 1} f₀ f₁ h₁ g₁ w₁).first ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (squareLift.{u, u + 1} f₁ f₂ h₂ g₂ w₂).first
      (etaleMorphism.{u, u + 1} h₁).direct ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (p₁.{u, u + 1} f₂).direct (etaleComposition.{u, u + 1} h₂ h₁)

/-- Projection comparison for a composite of induced oriented maps: second projection.
Source: ILO XI §§1.4, 1.9 (blueprint: def-trf-oriented-hypercover-descent-datum). -/
def compositeSecond {X₀ S₀ X₁ S₁ X₂ S₂ : Scheme.{u}}
    (f₀ : X₀ ⟶ S₀) (f₁ : X₁ ⟶ S₁) (f₂ : X₂ ⟶ S₂)
    (h₁ : X₁ ⟶ X₀) (g₁ : S₁ ⟶ S₀) (w₁ : h₁ ≫ f₀ = f₁ ≫ g₁)
    (h₂ : X₂ ⟶ X₁) (g₂ : S₂ ⟶ S₁) (w₂ : h₂ ≫ f₁ = f₂ ≫ g₂) :
    (((squareMorphism.{u, u + 1} f₁ f₂ h₂ g₂ w₂).comp
      (squareMorphism.{u, u + 1} f₀ f₁ h₁ g₁ w₁)).comp (p₂.{u, u + 1} f₀)).direct ≅
        ((p₂.{u, u + 1} f₂).comp (etaleMorphism.{u, u + 1} (g₂ ≫ g₁))).direct :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (squareMorphism.{u, u + 1} f₁ f₂ h₂ g₂ w₂).direct
      (squareLift.{u, u + 1} f₀ f₁ h₁ g₁ w₁).second ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (squareLift.{u, u + 1} f₁ f₂ h₂ g₂ w₂).second
      (etaleMorphism.{u, u + 1} g₁).direct ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (p₂.{u, u + 1} f₂).direct (etaleComposition.{u, u + 1} g₂ g₁)

/-- Commutativity of the square in a degree of a changed hypercover.
Source: ILO XI §1.9 (blueprint: def-trf-oriented-hypercover-descent-datum). -/
abbrev rectangleComm {X S X' S' U U' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (e : U ⟶ X) (e' : U' ⟶ X')
    (h : X' ⟶ X) (g : S' ⟶ S) (q : U' ⟶ U)
    (w : h ≫ f = f' ≫ g) (we : q ≫ e = e' ≫ h) :
    q ≫ (e ≫ f) = (e' ≫ f') ≫ g :=
  (Category.assoc _ _ _).symm.trans ((congrArg (fun k ↦ k ≫ f) we).trans
    ((Category.assoc _ _ _).trans ((congrArg (fun k ↦ e' ≫ k) w).trans
      (Category.assoc _ _ _).symm)))

/-- The two oriented composites of a scheme rectangle have exactly one identification
with the prescribed first and second projections. Source: ILO XI Theorem 1.4, §1.9
(blueprint: def-trf-oriented-hypercover-descent-datum).
Proof: both composites lift (p₁.{u, u + 1} followed by qe=e'h, p₂.{u, u + 1} followed by g). Their
orientations are the same pasted orientation of f'. Apply orientation_universal.
Its uniqueness clause gives both equations and uniqueness, not an arbitrary square. -/
theorem rectangle_existsUnique {X S X' S' U U' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (e : U ⟶ X) (e' : U' ⟶ X')
    (h : X' ⟶ X) (g : S' ⟶ S) (q : U' ⟶ U)
    (w : h ≫ f = f' ≫ g) (we : q ≫ e = e' ≫ h) :
    ∃! z : ((squareMorphism.{u, u + 1} (e ≫ f) (e' ≫ f') q g
          (rectangleComm f f' e e' h g q w we)).comp
        (squareMorphism.{u, u + 1} f (e ≫ f) e (𝟙 S) (Category.comp_id _).symm)).direct ≅
      ((squareMorphism.{u, u + 1} f' (e' ≫ f') e' (𝟙 S') (Category.comp_id _).symm).comp
        (squareMorphism.{u, u + 1} f f' h g w)).direct,
      Functor.isoWhiskerRight z (p₁.{u, u + 1} f).direct ≪≫
          compositeFirst f f' (e' ≫ f') h g w e' (𝟙 S') (Category.comp_id _).symm =
        compositeFirst f (e ≫ f) (e' ≫ f') e (𝟙 S) (Category.comp_id _).symm q g
            (rectangleComm f f' e e' h g q w we) ≪≫
          Functor.isoWhiskerLeft (p₁.{u, u + 1} (e' ≫ f')).direct
            (eqToIso (congrArg (fun k ↦ (etaleMorphism.{u, u + 1} k).direct) we)) ∧
      Functor.isoWhiskerRight z (p₂.{u, u + 1} f).direct ≪≫
          compositeSecond f f' (e' ≫ f') h g w e' (𝟙 S') (Category.comp_id _).symm =
        compositeSecond f (e ≫ f) (e' ≫ f') e (𝟙 S) (Category.comp_id _).symm q g
            (rectangleComm f f' e e' h g q w we) ≪≫
          Functor.isoWhiskerLeft (p₂.{u, u + 1} (e' ≫ f')).direct
            (eqToIso (congrArg (fun k ↦ (etaleMorphism.{u, u + 1} k).direct)
              ((Category.comp_id g).trans (Category.id_comp g).symm))) := by
  sorry

/-- The canonical inverse-image square on derived constant modules of vanishing topoi.
Source: ILO XI §1.9; Stacks 0E46
(blueprint: def-trf-oriented-hypercover-descent-datum). -/
def rectangle {X S X' S' U U' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (e : U ⟶ X) (e' : U' ⟶ X')
    (h : X' ⟶ X) (g : S' ⟶ S) (q : U' ⟶ U)
    (w : h ≫ f = f' ≫ g) (we : q ≫ e = e' ≫ h)
    (Λ : Type (u + 1)) [CommRing Λ] :=
  CategoryTheory.AdicSites.derivedSquare
    (f := squareModules.{u, u + 1} f (e ≫ f) e (𝟙 S) (Category.comp_id _).symm)
    (g := squareModules.{u, u + 1} f f' h g w)
    (h := squareModules.{u, u + 1} (e ≫ f) (e' ≫ f') q g (rectangleComm f f' e e' h g q w we))
    (k := squareModules.{u, u + 1} f' (e' ≫ f') e' (𝟙 S') (Category.comp_id _).symm)
    (GeometricMorphism.inverseIso (rectangle_existsUnique f f' e e' h g q w we).choose)
    (Coeff.{u, u + 1} Λ)

/-- A Cartesian change of the base, including the simplicial comparison and its
Cartesian degree squares. The slice natural transformation supplies all face and
degeneracy compatibilities; no condition is imposed on the changed base scheme.
Source: Stacks 0DHL, 0D99; Orgogozo §9.2
(blueprint: def-trf-oriented-hypercover-descent-datum). -/
structure Change {X S : Scheme.{u}} (f : X ⟶ S) (Y : SimplicialObject (Over X)) where
  X' : Scheme.{u}
  S' : Scheme.{u}
  f' : X' ⟶ S'
  h : X' ⟶ X
  g : S' ⟶ S
  cartesian : IsPullback h f' f g
  Y' : SimplicialObject (Over X')
  a : Y' ⋙ Over.map h ⟶ Y
  degree_cartesian : ∀ i : ℕ,
    IsPullback (a.app (op (SimplexCategory.mk i))).left (epsilon Y' i) (epsilon Y i) h

/-- The canonical first-page complex comparison: ordinary base change for the degree
augmentation, then beta on Y_i, and the canonical identification of coefficient pullbacks.
Source: Stacks 0E46, 0E47; Orgogozo §9.2
(blueprint: def-trf-oriented-hypercover-descent-datum). -/
def termChange {X S : Scheme.{u}} (f : X ⟶ S) (Y : SimplicialObject (Over X))
    (b : Change f Y) (Λ : Type (u + 1)) [CommRing Λ] (K : EtaleDerived X Λ) (i : ℕ) :
    ((squareModules.{u, u + 1} f b.f' b.h b.g b.cartesian.w).pull (Coeff.{u, u + 1} Λ)).obj (term
      f Y Λ K i) ⟶
      term b.f' b.Y' Λ (((etaleModules.{u, u + 1} b.h).pull (Coeff.{u, u + 1} Λ)).obj K) i :=
  ((orientedEpsilon b.f' b.Y' i).adj (Coeff.{u, u + 1} Λ)).homEquiv _ _
    ((rectangle f b.f' (epsilon Y i) (epsilon b.Y' i) b.h b.g
        (b.a.app (op (SimplexCategory.mk i))).left b.cartesian.w
        ((b.degree_cartesian i).w) Λ).hom.app (term f Y Λ K i) ≫
      ((squareModules.{u, u + 1} (epsilon Y i ≫ f) (epsilon b.Y' i ≫ b.f')
          (b.a.app (op (SimplexCategory.mk i))).left b.g
          (rectangleComm f b.f' (epsilon Y i) (epsilon b.Y' i) b.h b.g
            (b.a.app (op (SimplexCategory.mk i))).left b.cartesian.w
            ((b.degree_cartesian i).w))).pull (Coeff.{u, u + 1} Λ)).map
        (((orientedEpsilon f Y i).adj (Coeff.{u, u + 1} Λ)).counit.app
          ((nearbyCycles.{u, u + 1} (epsilon Y i ≫ f) Λ).obj (coefficient Y Λ K i))) ≫
      baseChange.{u, u + 1} (epsilon Y i ≫ f) (epsilon b.Y' i ≫ b.f')
        (b.a.app (op (SimplexCategory.mk i))).left b.g
        (rectangleComm f b.f' (epsilon Y i) (epsilon b.Y' i) b.h b.g
          (b.a.app (op (SimplexCategory.mk i))).left b.cartesian.w
          ((b.degree_cartesian i).w)) Λ (coefficient Y Λ K i) ≫
      (nearbyCycles.{u, u + 1} (epsilon b.Y' i ≫ b.f') Λ).map
        ((CategoryTheory.AdicSites.derivedSquare
          (f := etaleModules.{u, u + 1} (epsilon Y i)) (g := etaleModules.{u, u + 1} b.h)
          (h := etaleModules.{u, u + 1} (b.a.app (op (SimplexCategory.mk i))).left)
          (k := etaleModules.{u, u + 1} (epsilon b.Y' i))
          (GeometricMorphism.inverseIso
            (squareDirect.{u, u + 1} (epsilon Y i) (epsilon b.Y' i)
              (b.a.app (op (SimplexCategory.mk i))).left b.h
              (b.degree_cartesian i).w)) (Coeff.{u, u + 1} Λ)).inv.app K))

/-- Action of the degree-i derived functor on coefficient maps.
Source: Orgogozo §9.2 (blueprint: def-trf-oriented-hypercover-descent-datum). -/
def termMap {X S : Scheme.{u}} (f : X ⟶ S) (Y : SimplicialObject (Over X))
    (Λ : Type (u + 1)) [CommRing Λ] {K L : EtaleDerived X Λ} (a : K ⟶ L) (i : ℕ) :
    term f Y Λ K i ⟶ term f Y Λ L i :=
  ((orientedEpsilon f Y i).push (Coeff.{u, u + 1} Λ)).map
    ((nearbyCycles.{u, u + 1} (epsilon Y i ≫ f) Λ).map
      (((etaleModules.{u, u + 1} (epsilon Y i)).pull (Coeff.{u, u + 1} Λ)).map a))

/-- Composition of exact étale module inverse images, normalized on scalar insertions.
Source: ILO XI §1.9; Stacks 03D2, 0E47
(blueprint: def-trf-oriented-hypercover-descent-datum).
Proof: the inverse of the mate of etaleComposition.{u, u + 1} identifies the two underlying
set-sheaf inverse images. It respects the additive and constant-ring operations. Extend
it by scalar extension; the two insertion maps give the displayed normalization.
Scalar insertions locally generate, hence determine the transformation uniquely.
Applying the inverse set-sheaf comparison supplies the inverse transformation. -/
theorem pullComposition_existsUnique {T U V : Scheme.{u}} (a : U ⟶ T) (b : V ⟶ U)
    (Λ : Type (u + 1)) [CommRing Λ] :
    ∃! z : (etaleModules.{u, u + 1} a).modulePull (Coeff.{u, u + 1} Λ) ⋙
          (etaleModules.{u, u + 1} b).modulePull (Coeff.{u, u + 1} Λ) ≅
        (etaleModules.{u, u + 1} (b ≫ a)).modulePull (Coeff.{u, u + 1} Λ),
      ∀ M : (etaleDatum.{u, u + 1} T).modules (Coeff.{u, u + 1} Λ),
        (etaleModules.{u, u + 1} b).inverse.map
            (CategoryTheory.ConstantCompletion.pullInsertion (etaleModules.{u, u + 1} a).algebra
              (CategoryTheory.ConstantCompletion.constantMap (etaleModules.{u, u + 1} a).algebra
                (Coeff.{u, u + 1} Λ)) M) ≫
          CategoryTheory.ConstantCompletion.pullInsertion (etaleModules.{u, u + 1} b).algebra
            (CategoryTheory.ConstantCompletion.constantMap (etaleModules.{u, u + 1} b).algebra
              (Coeff.{u, u + 1} Λ)) (((etaleModules.{u, u + 1} a).modulePull (Coeff.{u, u + 1}
                Λ)).obj M) ≫
          (CategoryTheory.ConstantCompletion.underlying ((etaleDatum.{u, u + 1} V).ring (Coeff.{u,
            u + 1} Λ))).map
            (z.hom.app M) =
        (GeometricMorphism.inverseIso (etaleComposition.{u, u + 1} b a)).inv.app
            ((CategoryTheory.ConstantCompletion.underlying
              ((etaleDatum.{u, u + 1} T).ring (Coeff.{u, u + 1} Λ))).obj M) ≫
          CategoryTheory.ConstantCompletion.pullInsertion (etaleModules.{u, u + 1} (b ≫ a)).algebra
            (CategoryTheory.ConstantCompletion.constantMap (etaleModules.{u, u + 1} (b ≫ a)).algebra
              (Coeff.{u, u + 1} Λ)) M := by
  sorry

/-- The canonical derived inverse-image composition; the preceding uniqueness fixes its
ordinary representative, and exact localization fixes its derived comparison.
Source: ILO XI §1.9; Stacks 0E47
(blueprint: def-trf-oriented-hypercover-descent-datum). -/
def pullComposition {T U V : Scheme.{u}} (a : U ⟶ T) (b : V ⟶ U)
    (Λ : Type (u + 1)) [CommRing Λ] :
    (etaleModules.{u, u + 1} a).pull (Coeff.{u, u + 1} Λ) ⋙ (etaleModules.{u, u + 1} b).pull
      (Coeff.{u, u + 1} Λ) ≅
      (etaleModules.{u, u + 1} (b ≫ a)).pull (Coeff.{u, u + 1} Λ) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (pullComposition_existsUnique a b Λ).choose

/-- A further Cartesian change between two base changes of the initial hypercover.
The equations over the initial base and each initial simplex ensure that these are
successive base changes of the same augmented object.
Source: Stacks 0D99, 0E47 (blueprint: def-trf-oriented-hypercover-descent-datum). -/
structure Between {X S : Scheme.{u}} {f : X ⟶ S} {Y : SimplicialObject (Over X)}
    (b₁ b₂ : Change f Y) where
  h : b₂.X' ⟶ b₁.X'
  g : b₂.S' ⟶ b₁.S'
  cartesian : IsPullback h b₂.f' b₁.f' g
  a : b₂.Y' ⋙ Over.map h ⟶ b₁.Y'
  degree_cartesian : ∀ i : ℕ,
    IsPullback (a.app (op (SimplexCategory.mk i))).left (epsilon b₂.Y' i)
      (epsilon b₁.Y' i) h
  overX : h ≫ b₁.h = b₂.h
  overS : g ≫ b₁.g = b₂.g
  overY : ∀ i : ℕ, (a.app (op (SimplexCategory.mk i))).left ≫
    (b₁.a.app (op (SimplexCategory.mk i))).left =
      (b₂.a.app (op (SimplexCategory.mk i))).left

/-- The Cartesian change underlying a successive change of base.
Source: Stacks 0D99 (blueprint: def-trf-oriented-hypercover-descent-datum). -/
def Between.change {X S : Scheme.{u}} {f : X ⟶ S} {Y : SimplicialObject (Over X)}
    {b₁ b₂ : Change f Y} (q : Between b₁ b₂) : Change b₁.f' b₁.Y' where
  X' := b₂.X'
  S' := b₂.S'
  f' := b₂.f'
  h := q.h
  g := q.g
  cartesian := q.cartesian
  Y' := b₂.Y'
  a := q.a
  degree_cartesian := q.degree_cartesian

/-- Canonical identification of the successively pulled-back coefficient complex.
Source: Stacks 0E47 (blueprint: def-trf-oriented-hypercover-descent-datum). -/
def Between.coefficients {X S : Scheme.{u}} {f : X ⟶ S}
    {Y : SimplicialObject (Over X)} {b₁ b₂ : Change f Y} (q : Between b₁ b₂)
    (Λ : Type (u + 1)) [CommRing Λ] (K : EtaleDerived X Λ) :
    ((etaleModules.{u, u + 1} q.h).pull (Coeff.{u, u + 1} Λ)).obj
        (((etaleModules.{u, u + 1} b₁.h).pull (Coeff.{u, u + 1} Λ)).obj K) ⟶
      ((etaleModules.{u, u + 1} b₂.h).pull (Coeff.{u, u + 1} Λ)).obj K :=
  (pullComposition b₁.h q.h Λ).hom.app K ≫
    eqToHom (congrArg (fun t ↦ ((etaleModules.{u, u + 1} t).pull (Coeff.{u, u + 1} Λ)).obj K)
      q.overX)

/-- Exact inverse image of a spectral sequence, page by page. The transition uses
Mathlib's canonical preserved-homology comparison of short complexes.
Source: Stacks 0D99 (blueprint: def-trf-oriented-hypercover-descent-datum). -/
def inverseSequence {C : Type v} {D : Type w} [Category.{v₁} C] [Category.{w₁} D]
    [Abelian C] [Abelian D] (P : C ⥤ D) [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (E : CohomologicalSpectralSequence C 1) : CohomologicalSpectralSequence D 1 where
  page r hr := (P.mapHomologicalComplex _).obj (E.page r hr)
  iso r r' pq hrr' hr :=
    ((E.page r hr).sc pq).mapHomologyIso P ≪≫ P.mapIso (E.iso r r' pq hrr' hr)

/-- The spectral sequence, finite abutment filtration and augmented edge, in the actual
module-sheaf category of V_f. A stable page is any page beyond n-c+1; we use
max(1,n-c+2). The support condition makes that representative E_infinity.
Source: Orgogozo §9.2; Stacks 0D7F
(blueprint: def-trf-oriented-hypercover-descent-datum). -/
structure Descent {X S : Scheme.{u}} (f : X ⟶ S) (Y : SimplicialObject (Over X))
    (Λ : Type (u + 1)) [CommRing Λ] (K : EtaleDerived X Λ) (c : ℤ) where
  sequence : CohomologicalSpectralSequence ((vanishingDatum.{u, u + 1} f).modules (Coeff.{u, u +
    1} Λ)) 1
  first : ∀ (i : ℕ) (j : ℤ), (sequence.page 1).X ((i : ℤ), j) ≅
    (DerivedCategory.homologyFunctor _ j).obj (term f Y Λ K i)
  support : ∀ (r : ℤ) (hr : 1 ≤ r) (p q : ℤ), p < 0 ∨ q < c →
    IsZero ((sequence.page r hr).X (p, q))
  filtration : ∀ n : ℤ, DecreasingFiltration
    ((DerivedCategory.homologyFunctor _ n).obj ((nearbyCycles.{u, u + 1} f Λ).obj K))
  top : ∀ n : ℤ, (filtration n).F 0 = ⊤
  bottom : ∀ n : ℤ, (filtration n).F (max 0 (n - c + 1)) = ⊥
  graded : ∀ (n p : ℤ) (_hp : 0 ≤ p) (_hpn : p ≤ n - c),
    (filtration n).gr p ≅
      (sequence.page (max 1 (n - c + 2)) (le_max_left _ _)).X (p, n - p)
  edge : ∀ (r : ℤ) (hr : 1 ≤ r) (j : ℤ),
    (DerivedCategory.homologyFunctor _ j).obj ((nearbyCycles.{u, u + 1} f Λ).obj K) ⟶
      (sequence.page r hr).X (0, j)
  edgeCycles : ∀ (r : ℤ) (hr : 1 ≤ r) (j : ℤ),
    (DerivedCategory.homologyFunctor _ j).obj ((nearbyCycles.{u, u + 1} f Λ).obj K) ⟶
      (sequence.page r hr).cycles (0, j)
  edge_cycles : ∀ (r : ℤ) (hr : 1 ≤ r) (j : ℤ),
    edgeCycles r hr j ≫ (sequence.page r hr).iCycles (0, j) = edge r hr j
  edge_next : ∀ (r : ℤ) (hr : 1 ≤ r) (j : ℤ),
    edgeCycles r hr j ≫ (sequence.page r hr).homologyπ (0, j) ≫
        (sequence.iso r (r + 1) (0, j) rfl hr).hom = edge (r + 1) (by omega) j
  edge_first : ∀ j : ℤ, edge 1 (le_refl 1) j ≫ (first 0 j).hom =
    (DerivedCategory.homologyFunctor _ j).map (augmentation f Y Λ K 0)
  edge_graded : ∀ (n : ℤ) (hn : c ≤ n),
    ((filtration n).F 0).arrow ≫ edge (max 1 (n - c + 2)) (le_max_left _ _) n =
      cokernel.π (Subobject.ofLE _ _ ((filtration n).F_succ_le 0)) ≫
        (graded n 0 (le_refl 0) (sub_nonneg.mpr hn)).hom ≫
        eqToHom (congrArg
          (fun j : ℤ ↦ (sequence.page (max 1 (n - c + 2)) (le_max_left _ _)).X (0, j))
          (sub_zero n))

/-- The actual module inverse image on the changed vanishing topos.
Source: ILO XI §1.9 (blueprint: def-trf-oriented-hypercover-descent-datum). -/
abbrev changePull {X S : Scheme.{u}} {f : X ⟶ S} {Y : SimplicialObject (Over X)}
    (b : Change f Y) (Λ : Type (u + 1)) [CommRing Λ] :=
  (squareModules.{u, u + 1} f b.f' b.h b.g b.cartesian.w).modulePull (Coeff.{u, u + 1} Λ)

/-- Cohomological base change: commute the exact inverse image with homology, then
apply the recorded ordinary nearby-cycle comparison beta.
Source: ILO XI §4.1; Stacks 0D99
(blueprint: def-trf-oriented-hypercover-descent-datum). -/
def abutmentChange {X S : Scheme.{u}} {f : X ⟶ S} {Y : SimplicialObject (Over X)}
    (b : Change f Y) (Λ : Type (u + 1)) [CommRing Λ] (K : EtaleDerived X Λ)
    {K' : EtaleDerived b.X' Λ} (κ : ((etaleModules.{u, u + 1} b.h).pull (Coeff.{u, u + 1} Λ)).obj
      K ⟶ K')
    (n : ℤ) :=
  ((changePull b Λ).mapDerivedCategoryHomologyFunctorIso n).hom.app
      ((nearbyCycles.{u, u + 1} f Λ).obj K) ≫
    (DerivedCategory.homologyFunctor _ n).map
      (baseChange.{u, u + 1} f b.f' b.h b.g b.cartesian.w Λ K ≫ (nearbyCycles.{u, u + 1} b.f'
        Λ).map κ)

/-- Naturality of pages, augmentation, finite filtration, and associated graded pieces.
The first-page map is the prescribed base-change-then-beta composite. In particular it
is a comparison map, with no assertion of invertibility. The homology compatibility in
SpectralSequence.Hom determines every later page from this first-page map, so identity
and composite changes give the same morphisms under the canonical pullback comparisons.
Source: Stacks 0D99, 0E46, 0E47; Orgogozo §9.2
(blueprint: def-trf-oriented-hypercover-descent-datum). -/
structure Comparison {X S : Scheme.{u}} {f : X ⟶ S} {Y : SimplicialObject (Over X)}
    {Λ : Type (u + 1)} [CommRing Λ] {K : EtaleDerived X Λ} {c : ℤ}
    (D : Descent f Y Λ K c) (b : Change f Y)
    {K' : EtaleDerived b.X' Λ}
    (κ : ((etaleModules.{u, u + 1} b.h).pull (Coeff.{u, u + 1} Λ)).obj K ⟶ K')
    (D' : Descent b.f' b.Y' Λ K' c) where
  pages : inverseSequence (changePull b Λ) D.sequence ⟶ D'.sequence
  first : ∀ (i : ℕ) (j : ℤ),
    (pages.hom 1).f ((i : ℤ), j) ≫ (D'.first i j).hom =
      (changePull b Λ).map (D.first i j).hom ≫
        ((changePull b Λ).mapDerivedCategoryHomologyFunctorIso j).hom.app
          (term f Y Λ K i) ≫
        (DerivedCategory.homologyFunctor _ j).map
          (termChange f Y b Λ K i ≫ termMap b.f' b.Y' Λ κ i)
  edge : ∀ (r : ℤ) (hr : 1 ≤ r) (j : ℤ),
    (changePull b Λ).map (D.edge r hr j) ≫ (pages.hom r hr).f (0, j) =
      abutmentChange b Λ K κ j ≫ D'.edge r hr j
  steps : ∀ (n p : ℤ), (changePull b Λ).obj ((D.filtration n).F p : _) ⟶
    ((D'.filtration n).F p : _)
  steps_comm : ∀ (n p : ℤ), steps n p ≫ ((D'.filtration n).F p).arrow =
    (changePull b Λ).map ((D.filtration n).F p).arrow ≫ abutmentChange b Λ K κ n
  graded : ∀ (n p : ℤ), (changePull b Λ).obj ((D.filtration n).gr p) ⟶
    (D'.filtration n).gr p
  quotient_comm : ∀ (n p : ℤ),
    (changePull b Λ).map
        (cokernel.π (Subobject.ofLE _ _ ((D.filtration n).F_succ_le p))) ≫ graded n p =
      steps n p ≫ cokernel.π (Subobject.ofLE _ _ ((D'.filtration n).F_succ_le p))
  convergence : ∀ (n p : ℤ) (hp : 0 ≤ p) (hpn : p ≤ n - c),
    (changePull b Λ).map (D.graded n p hp hpn).hom ≫
        (pages.hom (max 1 (n - c + 2)) (le_max_left _ _)).f (p, n - p) =
      graded n p ≫ (D'.graded n p hp hpn).hom

end AlgebraicGeometry.OrientedNearbyCycles.Hypercover
