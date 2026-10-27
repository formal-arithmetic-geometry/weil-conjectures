/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Sheaf.AlgebraicGeometry.MarkedSchemeLifts
public import Sheaf.AlgebraicGeometry.LciCotangentPresentation
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Cotangent Ext classification of marked scheme lifts

Source: Stacks Project, Deformation Theory, Tags 0D14, 0GPZ, 0GQ0--0GQ2;
Cotangent Complex, Tags 08UW and 08UZ; More on Morphisms, Tag 0D0I
(blueprint: def-sfb-scheme-lift-classification-data).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option genSizeOfSpec false
set_option genInjectivity false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open Algebra.CotangentResolution Simplicial

namespace AlgebraicGeometry.SchemeDeformation

variable [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
  [∀ X : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]

/-- The adjunction for the actual inverse-image construction used by tensor pullback.
Source: Stacks 008X (blueprint: def-sfb-scheme-lift-classification-data). -/
def inverseRingAdjunction {X S : Scheme.{u}} (f : X ⟶ S) :
    TopCat.Sheaf.inverseImageConstruction f.base CommRingCat.{u} ⊣
      TopCat.Sheaf.pushforward CommRingCat.{u} f.base :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (TopologicalSpace.Opens.map f.base) CommRingCat.{u}
    (Opens.grothendieckTopology S)
    (Opens.grothendieckTopology X)

/-- The structure-sheaf morphism as a morphism of sheaves. Source: Stacks 01HA
(blueprint: def-sfb-scheme-lift-classification-data). -/
def baseSheafMap {S S' : Scheme.{u}} (i : S ⟶ S') :
    S'.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} i.base).obj S.sheaf :=
  ⟨i.c⟩

/-- The canonical reduction map on inverse-image base rings. Its transpose is the
base reduction followed by the inverse-image unit. Source: Stacks 0D14
(blueprint: def-sfb-scheme-lift-classification-data). -/
def baseReduction {X S S' : Scheme.{u}} (f : X ⟶ S) (i : S ⟶ S') :
    TopCat.Sheaf.inverseImageRing (f ≫ i).base S'.sheaf ⟶
      TopCat.Sheaf.inverseImageRing f.base S.sheaf :=
  ((inverseRingAdjunction (f ≫ i)).homEquiv _ _).symm
    (baseSheafMap i ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} i.base).map
      ((inverseRingAdjunction f).unit.app S.sheaf))

/-- A local section of an inverse-image ring sheaf, including restriction to any
smaller open. Source: Stacks 008X (blueprint: def-sfb-scheme-lift-classification-data). -/
def inverseSection {X Y : Scheme.{u}} (g : X ⟶ Y) (V : Y.Opens) (W : X.Opens)
    (h : W ≤ g ⁻¹ᵁ V) (a : Γ(Y, V)) :
    (TopCat.Sheaf.inverseImageRing g.base Y.sheaf).obj.obj (op W) :=
  (TopCat.Sheaf.inverseImageRing g.base Y.sheaf).obj.map (homOfLE h).op
    ((CotangentPresentation.inverseUnit g).app (op V) a)

/-- The underlying scheme arrow of a marking-preserving morphism.
Source: Stacks 0D14 (blueprint: def-sfb-scheme-lift-classification-data). -/
abbrev liftMap {X S S' : Scheme.{u}} {f : X ⟶ S} {i : S ⟶ S'}
    {Y Z : Lift f i} (a : Y ⟶ Z) : Y.space ⟶ Z.space := a.hom.right.left

/-- The kernel on the marked space, with its conormal identification fixed on every
pulled-back section of the base ideal. The normalization fixes the actual kernel
map, including its sign. Source: Stacks 0D14 and 063Y
(blueprint: def-sfb-scheme-lift-classification-data). -/
structure LiftKernel {X S S' : Scheme.{u}} {f : X ⟶ S} {i : S ⟶ S'} (Y : Lift f i) where
  inclusion (V : X.Opens) : Γ(coefficient f i, V) →+
    (TopCat.Sheaf.inverseImageRing Y.marking.base Y.space.sheaf).obj.obj (op V)
  naturality {V W : X.Opens} (h : W ≤ V) (g : Γ(coefficient f i, V)) :
    (TopCat.Sheaf.inverseImageRing Y.marking.base Y.space.sheaf).obj.map
      (homOfLE h).op (inclusion V g) =
        inclusion W ((coefficient f i).val.map (homOfLE h).op g)
  injective (V : X.Opens) : Function.Injective (inclusion V)
  kernel (V : X.Opens)
    (e : (TopCat.Sheaf.inverseImageRing Y.marking.base Y.space.sheaf).obj.obj (op V)) :
    (Scheme.Modules.tensorPullbackRingMap Y.marking).hom.app (op V) e = 0 ↔
      ∃ g : Γ(coefficient f i, V), inclusion V g = e
  base (V : S'.Opens) (a : Γ(i.ker.toModules, V)) (W : X.Opens)
    (h : W ≤ f ⁻¹ᵁ (i ⁻¹ᵁ V)) (h' : W ≤ Y.marking ⁻¹ᵁ (Y.projection ⁻¹ᵁ V)) :
    inclusion W ((coefficient f i).val.map (homOfLE h).op
      (Scheme.Modules.tensorPullbackSection f _ (i ⁻¹ᵁ V)
        (Scheme.Modules.tensorPullbackSection i _ V a))) =
      inverseSection Y.marking (Y.projection ⁻¹ᵁ V) W h'
        (Y.projection.app V (i.ker.toModulesι.app V a))

/-- A derived map in degree zero represented by its actual universal derivation.
The formula on all standard polynomial differential sections determines the chain map.
Source: Stacks 08U8, 08UZ (blueprint: def-sfb-scheme-lift-classification-data). -/
structure DerivationRepresentative (C : Coherence.{u})
    (D : TopCat.SheafCotangent.Comparison C) {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) (ξ : Ext C D f G 0) where
  derivation : G.val.Derivation' (Scheme.Modules.tensorPullbackRingMap f).hom
  representative : cotangentComplex C D f ⟶
    (HomologicalComplex.single (SheafOfModules.{u} X.ringCatSheaf) (.up ℤ) 0).obj G
  derived : ξ = DerivedCategory.Q.map representative ≫
    (shiftFunctorZero (DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)) ℤ).inv.app _
  generators (V : (TopologicalSpace.Opens X.carrier)ᵒᵖ)
    (b : X.sheaf.obj.obj V)
    (x : (C.standard (TopCat.SheafCotangent.sectionArrow
      (Arrow.mk (Scheme.Modules.tensorPullbackRingMap f)) V)).algebra.obj (op ⦋0⦌)) :
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 G).hom.val.app V
      ((representative.f 0).val.app V (TopCat.SheafCotangent.sectionElement
        (D.sheaves X.carrier (Arrow.mk (Scheme.Modules.tensorPullbackRingMap f))).sections
        V 0 (complexGenerator (C.differentials (C.standard
          (TopCat.SheafCotangent.sectionArrow
            (Arrow.mk (Scheme.Modules.tensorPullbackRingMap f)) V))) 0 b x))) =
      b • derivation.d ((C.standard (TopCat.SheafCotangent.sectionArrow
        (Arrow.mk (Scheme.Modules.tensorPullbackRingMap f)) V)).augmentation.app (op ⦋0⦌) x)

/-- Postcomposition on the stated derived Hom groups. Source: Stacks 0GQ1
(blueprint: def-sfb-scheme-lift-classification-data). -/
def extMap (C : Coherence.{u}) (D : TopCat.SheafCotangent.Comparison C)
    {X S : Scheme.{u}} (f : X ⟶ S) {G H : X.Modules} (a : G ⟶ H) (n : ℤ)
    (ξ : Ext C D f G n) : Ext C D f H n :=
  ξ ≫ ((DerivedCategory.singleFunctor (SheafOfModules.{u} X.ringCatSheaf) 0).map a)⟦n⟧'

/-- A free transitive additive action on the actual marked isomorphism classes.
No origin is chosen. Source: Stacks 0D14, part (1)
(blueprint: def-sfb-scheme-lift-classification-data). -/
structure LiftTorsor (C : Coherence.{u}) (D : TopCat.SheafCotangent.Comparison C)
    {X S S' : Scheme.{u}} (f : X ⟶ S) (i : S ⟶ S') where
  translate : Ext C D f (coefficient f i) 1 → Classes f i → Classes f i
  zero (x : Classes f i) : translate 0 x = x
  add (a b : Ext C D f (coefficient f i) 1) (x : Classes f i) :
    translate (a + b) x = translate a (translate b x)
  unique (x y : Classes f i) : ∃! a : Ext C D f (coefficient f i) 1, translate a x = y

/-- Automorphisms fixing the marking are the additive Ext-zero group.
`Multiplicative` converts addition to the categorical composition convention.
Source: Stacks 0D14, part (2), and 08U8
(blueprint: def-sfb-scheme-lift-classification-data). -/
abbrev AutomorphismIdentification (C : Coherence.{u})
    (D : TopCat.SheafCotangent.Comparison C) {X S S' : Scheme.{u}}
    {f : X ⟶ S} {i : S ⟶ S'} (Y : Lift f i) :=
  Aut Y ≃* Multiplicative (Ext C D f (coefficient f i) 0)

/-- Split classification with its actual deformation vector operations and coefficient
maps. The additive group on Ext is inherited from the derived category.
Source: Stacks 0GPZ, 0GQ0--0GQ2
(blueprint: def-sfb-scheme-lift-classification-data). -/
structure SplitClassification (C : Coherence.{u}) (D : TopCat.SheafCotangent.Comparison C)
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) where
  classes : ∀ (M : ModuleCat.{u} k), FiniteDimensional k M →
    Classes f (directionReduction k M) ≃ Ext C D f (directionModule f M) 1
  module : ∀ (M : ModuleCat.{u} k), Module k (Ext C D f (directionModule f M) 1)
  scalar (M : ModuleCat.{u} k) (a : k) (ξ : Ext C D f (directionModule f M) 1) :
    @SMul.smul k _ (module M).toSMul a ξ =
      extMap C D f (directionModuleMap f (ModuleCat.ofHom (a • LinearMap.id))) 1 ξ
  trivial (M : ModuleCat.{u} k) (hM : FiniteDimensional k M)
    (Y : Lift f (directionReduction k M)) : IsTrivial f M Y ↔ classes M hM Y.class = 0
  trivial_exists (M : ModuleCat.{u} k) :
    ∃ Y : Lift f (directionReduction k M), IsTrivial f M Y
  addition (M : ModuleCat.{u} k) (hM : FiniteDimensional k M)
    (Y Z W : Lift f (directionReduction k M)) :
    IsSum f M Y Z W ↔ classes M hM W.class = classes M hM Y.class + classes M hM Z.class
  coefficients (M N : ModuleCat.{u} k) (hM : FiniteDimensional k M)
    (hN : FiniteDimensional k N) (a : M ⟶ N)
    (Y : Lift f (directionReduction k M)) (Z : Lift f (directionReduction k N))
    (q : Z.space ⟶ Y.space) : IsBaseChange (directionMap a) Y Z q →
      classes N hN Z.class = extMap C D f (directionModuleMap f a) 1 (classes M hM Y.class)


end AlgebraicGeometry.SchemeDeformation
