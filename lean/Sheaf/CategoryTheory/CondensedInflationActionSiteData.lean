module

public import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus
public import Sheaf.CategoryTheory.ProfiniteActionCoherentPresentation
public import Sheaf.CategoryTheory.ActionToposGeometricRestriction
public import Sheaf.Paper.CoefficientRingedTensorHomModel

/-! # Native action-site presentation of condensed inflation

Source: blueprint direct-image stability, paragraph (3), internal-action infrastructure;
Stacks 00YV, 06YN, 07A4, 0FPT.
(blueprint: def-sfb-condensed-inflation-action-site-data).

This specification identifies the original internal action category, its tensor and its
ordinary inflation with the independently specified small action-site models.
It introduces no chosen equivalence, derived tensor or pullback.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CondensedBar CategoryTheory.CondensedDerivedRestriction
open Profinite.CondensedAction (trivial)
namespace CategoryTheory.CondensedInflationNormalization
variable (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- The coefficient ring on the existing small twisted action site is ordinary inflation.
Source: blueprint paragraph (3), action-site presentation
(blueprint: def-sfb-condensed-inflation-action-site-data). -/
def inflatedRing
    (R : Sheaf Profinite.CondensedAction.CoherentPresentation.baseCoverage.toGrothendieck
      CommRingCat.{u + 1}) :=
  InternalActionSite.pulledCoefficient
    (InternalActionSite.topology
      (Profinite.CondensedAction.CoherentPresentation.groupPresheaf G)
      Profinite.CondensedAction.CoherentPresentation.baseCoverage)
    (InternalActionSite.projection
      (Profinite.CondensedAction.CoherentPresentation.groupPresheaf G)) R
    ((InternalActionSite.actionPrecomposition_isSheaf
      Profinite.CondensedAction.CoherentPresentation.baseCoverage
      Profinite.CondensedAction.CoherentPresentation.base_site
      (𝟙 (Profinite.CondensedAction.CoherentPresentation.groupPresheaf G))
      CommRingCat.{u + 1}).2 R)

/-- The actual small action-site presentation. Its section identifications specify the
original internal action, all restrictions and all maps. The ordinary pullback is the
section-normalized ringed pullback of geometricRestriction, rather than an arbitrary
left adjoint. The source equivalence is normalized on original section modules too.
Source: blueprint paragraph (3), action-site presentation, Stacks 00YV and 07A4
(blueprint: def-sfb-condensed-inflation-action-site-data). -/
structure ActionSitePresentation where
  /-- The original coefficient ring, transported to the common small parameter site. -/
  ring : Sheaf
    Profinite.CondensedAction.CoherentPresentation.baseCoverage.toGrothendieck
    CommRingCat.{u + 1}
  /-- This transport has exactly the original section rings and restrictions. -/
  ring_eq : ring.obj = AsSmall.down.op ⋙
    (InternalAbelianSheafModule.sectionRingSheaf
      (coherentTopology Profinite.{u}) A.X).obj
  /-- The induced identification of the transported section ring. -/
  ringSection (S : Profinite.CondensedAction.CoherentPresentation.Base.{u}) :
    ring.obj.obj (Opposite.op S) ≃+*
      CondensedBar.sectionRing A (Profinite.CondensedAction.CoherentPresentation.parameter S)
  /-- The section-ring identification is the one specified by ring_eq. -/
  ringSection_eq (S : Profinite.CondensedAction.CoherentPresentation.Base.{u})
      (r : ring.obj.obj (Opposite.op S)) :
    HEq (ringSection S r) ((eqToIso (congrArg
      (fun F : Profinite.CondensedAction.CoherentPresentation.Base.{u}ᵒᵖ ⥤
        CommRingCat.{u + 1} ↦ F.obj (Opposite.op S)) ring_eq)).hom r)
  /-- The geometric action-site presentation of the recorded dependency. -/
  geometry : InternalActionSite.GeometricRestriction
    Profinite.CondensedAction.CoherentPresentation.baseCoverage
    Profinite.CondensedAction.CoherentPresentation.base_site
  /-- The original modules on the small parameter site. -/
  base : Modules A ≌ ringedSiteModules.{u + 1}
    (InternalActionSite.baseRing _ ring)
  /-- Addition is the original addition of linear maps. -/
  base_additive : base.functor.Additive
  /-- This equivalence keeps the original section modules. -/
  base_sections (M : Modules A)
      (S : Profinite.CondensedAction.CoherentPresentation.Base.{u}) :
    (base.functor.obj M).val.obj (Opposite.op S) ≃+
      CondensedBar.sections A M
        (Profinite.CondensedAction.CoherentPresentation.parameter S)
  /-- Base section identifications commute with every original restriction. -/
  base_restriction (M : Modules A)
      {S T : Profinite.CondensedAction.CoherentPresentation.Base.{u}} (f : S ⟶ T)
      (x : (base.functor.obj M).val.obj (Opposite.op T)) :
    base_sections M S ((base.functor.obj M).val.map f.op x) =
      (M.X.obj.map f.down.op).hom (base_sections M T x)
  /-- On maps the base equivalence retains the original component map. -/
  base_maps {M N : Modules A} (f : M ⟶ N)
      (S : Profinite.CondensedAction.CoherentPresentation.Base.{u})
      (x : (base.functor.obj M).val.obj (Opposite.op S)) :
    base_sections N S ((base.functor.map f).val.app (Opposite.op S) x) =
      (f.hom.hom.app (Opposite.op
        (Profinite.CondensedAction.CoherentPresentation.parameter S))).hom (base_sections M S x)
  /-- Actions presented as module sheaves on the specified twisted action site. -/
  actions : Equivariant A G ≌ ringedSiteModules.{u + 1}
    (InternalActionSite.baseRing _ (inflatedRing G ring))
  /-- Action-site sections are the original module sections. -/
  sections (M : Equivariant A G)
      (S : Profinite.CondensedAction.CoherentPresentation.Base.{u}) :
    (actions.functor.obj M).val.obj (Opposite.op (InternalActionSite.Object.mk
      (K := Profinite.CondensedAction.CoherentPresentation.groupPresheaf G) S)) ≃+
        CondensedBar.sections A M.module
          (Profinite.CondensedAction.CoherentPresentation.parameter S)
  /-- The twisted restriction is exactly the specified action after base restriction. -/
  restriction (M : Equivariant A G)
      {S T : Profinite.CondensedAction.CoherentPresentation.Base.{u}} (f : S ⟶ T)
      (a : (Profinite.CondensedAction.CoherentPresentation.groupPresheaf G).obj (Opposite.op S))
      (x : (actions.functor.obj M).val.obj (Opposite.op (InternalActionSite.Object.mk
        (K := Profinite.CondensedAction.CoherentPresentation.groupPresheaf G) T))) :
    sections M S ((actions.functor.obj M).val.map
      (InternalActionSite.opArrow _ f a) x) =
        M.act (Profinite.CondensedAction.CoherentPresentation.parameter S) a.down
          ((M.module.X.obj.map f.down.op).hom (sections M T x))
  /-- Equivariant morphisms retain their original section maps. -/
  maps {M N : Equivariant A G} (f : M ⟶ N)
      (S : Profinite.CondensedAction.CoherentPresentation.Base.{u})
      (x : (actions.functor.obj M).val.obj (Opposite.op (InternalActionSite.Object.mk
        (K := Profinite.CondensedAction.CoherentPresentation.groupPresheaf G) S))) :
    sections N S ((actions.functor.map f).val.app _ x) =
      (f.val.hom.hom.app (Opposite.op
        (Profinite.CondensedAction.CoherentPresentation.parameter S))).hom (sections M S x)
  /-- Scalar multiplication uses the transported original section ring. -/
  linear (M : Equivariant A G)
      (S : Profinite.CondensedAction.CoherentPresentation.Base.{u})
      (r : ring.obj.obj (Opposite.op S))
      (x : (actions.functor.obj M).val.obj (Opposite.op (InternalActionSite.Object.mk
        (K := Profinite.CondensedAction.CoherentPresentation.groupPresheaf G) S))) :
    sections M S (r • x) = ringSection S r • sections M S x
  /-- The equivalence is additive on the given action-category morphisms. -/
  additive : actions.functor.Additive
  /-- Ordinary action tensor agrees with the sheafified relative tensor on the action site. -/
  tensor (M N : Equivariant A G) : actions.functor.obj (M ⊗ N) ≅
    (SheafOfModules.siteSheafTensorRight (actions.functor.obj N)).obj (actions.functor.obj M)
  /-- The comparison is the identity on every generalized pure tensor. -/
  tensor_pure (M N : Equivariant A G)
      (S : Profinite.CondensedAction.CoherentPresentation.Base.{u})
      (x : CondensedBar.sections A M.module
        (Profinite.CondensedAction.CoherentPresentation.parameter S))
      (y : CondensedBar.sections A N.module
        (Profinite.CondensedAction.CoherentPresentation.parameter S)) :
    sections (M ⊗ N) S ((tensor M N).inv.val.app _
      (SheafOfModules.siteSheafTensorTmul (actions.functor.obj M) (actions.functor.obj N)
        _ ((sections M S).symm x) ((sections N S).symm y))) =
      (((actionTensor A G).forgetCore.μIso M N).hom.hom.hom.app (Opposite.op
        (Profinite.CondensedAction.CoherentPresentation.parameter S))).hom
          (tensorSection M.module N.module
            (Profinite.CondensedAction.CoherentPresentation.parameter S) x y)
  /-- The module pullback is precisely trivial inflation under those equivalences. -/
  inflation : trivial (R := A.toMon) (P := G) ⋙ actions.functor ≅
    base.functor ⋙ (geometry.inflation_modules
      (Profinite.CondensedAction.CoherentPresentation.groupPresheaf G)
      (Profinite.CondensedAction.CoherentPresentation.group_isSheaf G) ring).pullback.functor
  /-- This is the identity comparison on the original coefficient-module sections. -/
  inflation_sections (M : Modules A)
      (S : Profinite.CondensedAction.CoherentPresentation.Base.{u})
      (x : (actions.functor.obj ((trivial (R := A.toMon) (P := G)).obj M)).val.obj
        (Opposite.op (InternalActionSite.Object.mk
          (K := Profinite.CondensedAction.CoherentPresentation.groupPresheaf G) S))) :
    base_sections M S
      ((geometry.inflation_modules
        (Profinite.CondensedAction.CoherentPresentation.groupPresheaf G)
        (Profinite.CondensedAction.CoherentPresentation.group_isSheaf G) ring).sections
          (base.functor.obj M) _ ((inflation.hom.app M).val.app _ x)) =
      sections ((trivial (R := A.toMon) (P := G)).obj M) S x
  /-- The actual ringed-site direct image is the existing fixed-section functor. -/
  directImage : actions.functor ⋙ (geometry.inflation_modules
      (Profinite.CondensedAction.CoherentPresentation.groupPresheaf G)
      (Profinite.CondensedAction.CoherentPresentation.group_isSheaf G) ring).ringed.modules ≅
    (invariants A G).functor ⋙ base.functor
  /-- The canonical site adjunction has the actual invariant-inclusion transpose. -/
  transpose (M : Modules A) (N : Equivariant A G)
      (f : (trivial (R := A.toMon) (P := G)).obj M ⟶ N) :
    ((geometry.inflation_modules
      (Profinite.CondensedAction.CoherentPresentation.groupPresheaf G)
      (Profinite.CondensedAction.CoherentPresentation.group_isSheaf G)
        ring).pullback.adjunction.homEquiv
        (base.functor.obj M) (actions.functor.obj N)
          (inflation.inv.app M ≫ actions.functor.map f)) ≫ directImage.hom.app N =
      base.functor.map ((invariants A G).adjunction.homEquiv M N f)

/-- The site equivalence preserves the original additive structure.
Source: blueprint paragraph (3)
(blueprint: def-sfb-condensed-inflation-action-site-data). -/
instance siteEquivalenceAdditive (P : ActionSitePresentation A G) :
    P.actions.functor.Additive := P.additive

/-- The module category on the presented small ringed action site, without a copied notion.
Source: Stacks 03D1 (blueprint: def-sfb-condensed-inflation-action-site-data). -/
abbrev siteModules (P : ActionSitePresentation A G) :=
  ringedSiteModules.{u + 1} (InternalActionSite.baseRing _ (inflatedRing G P.ring))

/-- The pure-tensor summand in the ordinary signed total complex of internal actions.
Source: Stacks 06YN (blueprint: def-sfb-condensed-inflation-action-site-data). -/
def actionTensorGenerator (P Q : CochainComplex (Equivariant A G) ℤ)
    (p q k : ℤ) (h : p + q = k) (S : Profinite.{u})
    (x : CondensedBar.sections A (P.X p).module S)
    (y : CondensedBar.sections A (Q.X q).module S) :
    CondensedBar.sections A ((P ⊗ Q).X k).module S :=
  ((HomologicalComplex.ιMapBifunctor P Q (curriedTensor _) (.up ℤ) p q k h).val.hom.hom.app
    (Opposite.op S)).hom
      ((((actionTensor A G).forgetCore.μIso (P.X p) (Q.X q)).hom.hom.hom.app
        (Opposite.op S)).hom (tensorSection (P.X p).module (Q.X q).module S x y))

/-- Native total tensor of the images of two internal action complexes.
Source: Stacks 06YN (blueprint: def-sfb-condensed-inflation-action-site-data). -/
abbrev siteTotalTensor (P : ActionSitePresentation A G)
    (X Y : CochainComplex (Equivariant A G) ℤ) :=
  (WeilConjectures.coefficientTotalTensor _ (inflatedRing G P.ring)).obj
    ((P.actions.functor.mapHomologicalComplex (.up ℤ)).obj X,
      (P.actions.functor.mapHomologicalComplex (.up ℤ)).obj Y)

end CategoryTheory.CondensedInflationNormalization
