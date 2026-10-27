module

public import Sheaf.Paper.RingedExchangeTensorCoherence
public import Sheaf.CategoryTheory.RingedSiteModuleCupProduct
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-! # Open-site presentations for relative cup products

Source: Stacks Project, Cohomology, Tags 0H99, 0B68 and 079W
(blueprint: def-sfb-ringed-space-cup-presentation).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory TopologicalSpace SheafOfModules

namespace AlgebraicGeometry.RingedSpace

/-- The open-set site of the given ringed space, with its specified derived tensor.
The model field in `CupSquarePresentation` specifies that tensor on K-flat representatives.
Source: Stacks Project, Tags 0H99 and 06YT
(blueprint: def-sfb-ringed-space-cup-presentation). -/
def cupCorner (X : RingedSpace.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    (T : DerivedCategory (SheafOfModules.{u} (moduleRings X)) ×
      DerivedCategory (SheafOfModules.{u} (moduleRings X)) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings X))) : RingedTensorCorner.{u, w} where
  site := Opens X
  topology := Opens.grothendieckTopology X
  ring := X.sheaf
  tensor := T

/-- A ringed-site edge represents this particular ringed-space morphism: its inverse
image of sets, inverse-image ring and structural ring map, tensor formula on objects
and maps, direct image, and derived
right adjoint are pinned to the recorded ringed-space constructions.
Source: Stacks Project, Tags 008Y, 06YJ and 079W
(blueprint: def-sfb-ringed-space-cup-presentation). -/
structure CupEdgeRealization {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y))]
    (v : X ⟶ Y)
    (TX : DerivedCategory (SheafOfModules.{u} (moduleRings X)) ×
      DerivedCategory (SheafOfModules.{u} (moduleRings X)) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings X)))
    (TY : DerivedCategory (SheafOfModules.{u} (moduleRings Y)) ×
      DerivedCategory (SheafOfModules.{u} (moduleRings Y)) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings Y)))
    (e : RingedTensorEdge (cupCorner Y TY) (cupCorner X TX)) : Prop where
  inverse : e.inverse = TopCat.Sheaf.pullback (Type u) v.hom.base
  direct : e.direct = TopCat.Sheaf.pushforward (Type u) v.hom.base
  inverseRing : e.inverseRing = TopCat.Sheaf.inverseImageRing v.hom.base Y.sheaf
  ringMap : e.ringMap = eqToHom inverseRing ≫
    CochainComplex.tensorPullbackRingMap v.hom.base X.sheaf Y.sheaf ⟨v.hom.c⟩
  object_eq : ∀ M : SheafOfModules.{u} (moduleRings Y),
    e.pullback.obj M = SheafOfModules.changeOfRings.{u, u, u}
      (CochainComplex.tensorPullbackRingMap v.hom.base X.sheaf Y.sheaf ⟨v.hom.c⟩)
      (TopCat.Sheaf.inverseImageModule v.hom.base Y.sheaf M)
  map_eq : ∀ {M N : SheafOfModules.{u} (moduleRings Y)} (a : M ⟶ N),
    e.pullback.map a = eqToHom (object_eq M) ≫
      SheafOfModules.changeOfRingsHom.{u, u, u}
        (CochainComplex.tensorPullbackRingMap v.hom.base X.sheaf Y.sheaf ⟨v.hom.c⟩)
        (TopCat.Sheaf.inverseImageModule v.hom.base Y.sheaf M)
        (TopCat.Sheaf.inverseImageModuleMap v.hom.base Y.sheaf M a) ≫
      eqToHom (object_eq N).symm
  pushforward : e.pushforward = moduleDirectImage v
  right : e.right = derivedModuleDirectImage v

/-- Simultaneous open-site presentations of the four actual ringed spaces and maps.
The square's insertion equation pins its module comparison to its geometric set-sheaf
comparison, hence to the ring-compatible commutative square. No tensor coherence, cup
compatibility, flatness, or invertibility of exchange is a field of this structure.
Source: Stacks Project, Tag 0H99 and the constructions in Tags 06YJ and 079W
(blueprint: def-sfb-ringed-space-cup-presentation). -/
structure CupSquarePresentation {X X' Y Y' : RingedSpace.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X'))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y'))]
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X) where
  tensorX : DerivedCategory (SheafOfModules.{u} (moduleRings X)) ×
    DerivedCategory (SheafOfModules.{u} (moduleRings X)) ⥤
    DerivedCategory (SheafOfModules.{u} (moduleRings X))
  tensorX' : DerivedCategory (SheafOfModules.{u} (moduleRings X')) ×
    DerivedCategory (SheafOfModules.{u} (moduleRings X')) ⥤
    DerivedCategory (SheafOfModules.{u} (moduleRings X'))
  tensorY : DerivedCategory (SheafOfModules.{u} (moduleRings Y)) ×
    DerivedCategory (SheafOfModules.{u} (moduleRings Y)) ⥤
    DerivedCategory (SheafOfModules.{u} (moduleRings Y))
  tensorY' : DerivedCategory (SheafOfModules.{u} (moduleRings Y')) ×
    DerivedCategory (SheafOfModules.{u} (moduleRings Y')) ⥤
    DerivedCategory (SheafOfModules.{u} (moduleRings Y'))
  modelX : RingedTensorModel (cupCorner X tensorX)
  modelX' : RingedTensorModel (cupCorner X' tensorX')
  modelY : RingedTensorModel (cupCorner Y tensorY)
  modelY' : RingedTensorModel (cupCorner Y' tensorY')
  fEdge : RingedTensorEdge (cupCorner Y tensorY) (cupCorner X tensorX)
  f'Edge : RingedTensorEdge (cupCorner Y' tensorY') (cupCorner X' tensorX')
  gEdge : RingedTensorEdge (cupCorner Y tensorY) (cupCorner Y' tensorY')
  g'Edge : RingedTensorEdge (cupCorner X tensorX) (cupCorner X' tensorX')
  f_actual : CupEdgeRealization f tensorX tensorY fEdge
  f'_actual : CupEdgeRealization f' tensorX' tensorY' f'Edge
  g_actual : CupEdgeRealization g tensorY' tensorY gEdge
  g'_actual : CupEdgeRealization g' tensorX' tensorX g'Edge
  square : RingedTensorSquare (cupCorner Y tensorY) (cupCorner X tensorX)
    (cupCorner Y' tensorY') (cupCorner X' tensorX') fEdge gEdge g'Edge f'Edge

end AlgebraicGeometry.RingedSpace
