/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Sheaves.Stalks
public import WeilConjectures.AlgebraicGeometry.FineSaturatedLogBlowup

/-!
# Zariski log structures and their association to the étale site

Source: ILO, Exposé VI 1.1 and Exposé VIII 3.3.2--3.3.4(ii), printed pp. 69, 106--107
(blueprint: def-trf-zariski-log-structure).

The Zariski chart condition uses the actual monoid stalk and the prescribed pushout
congruence. Association to the étale site is specified by its universal property,
including the map on every open and compatibility with regular functions. Thus no
choice of an unrelated map or of an unspecified log structure is involved.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- A monoid sheaf on the Zariski site with a map to regular functions.
Source: ILO VI 1.1, VIII 3.3.2 (blueprint: def-trf-zariski-log-structure). -/
structure ZariskiPrelogStructure (X : Scheme.{u}) where
  monoidSheaf : TopCat.Sheaf CommMonCat.{u} X.carrier
  alpha : monoidSheaf.obj ⟶ X.presheaf ⋙ forget₂ CommRingCat CommMonCat

/-- The monoid stalk of a Zariski prelog structure.
Source: ILO VI 1.1 (blueprint: def-trf-zariski-log-structure). -/
noncomputable def ZariskiPrelogStructure.stalk {X : Scheme.{u}}
    (Z : ZariskiPrelogStructure X) (x : X) : CommMonCat.{u} :=
  CommMonCat.FilteredColimits.colimit ((OpenNhds.inclusion x).op ⋙ Z.monoidSheaf.obj)

/-- The canonical germ in the explicit filtered-colimit monoid stalk.
Source: ILO VI 1.1 (blueprint: def-trf-zariski-log-structure). -/
noncomputable def ZariskiPrelogStructure.germ {X : Scheme.{u}}
    (Z : ZariskiPrelogStructure X) (U : X.Opens) (x : X) (hx : x ∈ U) :
    Z.monoidSheaf.obj.obj (op U) ⟶ Z.stalk x :=
  (CommMonCat.FilteredColimits.colimitCocone
    ((OpenNhds.inclusion x).op ⋙ Z.monoidSheaf.obj)).ι.app (op ⟨U, hx⟩)

/-- The structural map on actual Zariski stalks, induced by ring germs.
Source: ILO VI 1.1 (blueprint: def-trf-zariski-log-structure). -/
noncomputable def ZariskiPrelogStructure.stalkAlpha {X : Scheme.{u}}
    (Z : ZariskiPrelogStructure X) (x : X) : Z.stalk x →* X.presheaf.stalk x :=
  ((CommMonCat.FilteredColimits.colimitCoconeIsColimit
    ((OpenNhds.inclusion x).op ⋙ Z.monoidSheaf.obj)).desc
    { pt := CommMonCat.of (X.presheaf.stalk x)
      ι :=
        { app := fun U ↦ Z.alpha.app (op U.unop.1) ≫
            CommMonCat.ofHom (X.presheaf.germ U.unop.1 x U.unop.2).hom.toMonoidHom
          naturality := by
            intro U V f
            ext s
            change X.presheaf.germ V.unop.1 x V.unop.2
              (Z.alpha.app (op V.unop.1)
                (Z.monoidSheaf.obj.map
                  ((OpenNhds.inclusion x).map f.unop).op s)) =
              X.presheaf.germ U.unop.1 x U.unop.2 (Z.alpha.app (op U.unop.1) s)
            have hn := ConcreteCategory.congr_hom
              (Z.alpha.naturality ((OpenNhds.inclusion x).map f.unop).op) s
            change Z.alpha.app (op V.unop.1)
                (Z.monoidSheaf.obj.map ((OpenNhds.inclusion x).map f.unop).op s) =
              X.presheaf.map ((OpenNhds.inclusion x).map f.unop).op
                (Z.alpha.app (op U.unop.1) s) at hn
            exact (congrArg (fun a ↦ X.presheaf.germ V.unop.1 x V.unop.2 a) hn).trans
              (ConcreteCategory.congr_hom
                (X.presheaf.germ_res ((OpenNhds.inclusion x).map f.unop) x V.unop.2)
                (Z.alpha.app (op U.unop.1) s)) } }).hom

/-- The log axiom on Zariski stalks: the inverse image of ring units is the
unit group, and its map to ring units is bijective. These stalk conditions are
equivalent to the inverse-image-of-units sheaf isomorphism.
Source: ILO VI 1.1 (blueprint: def-trf-zariski-log-structure). -/
structure ZariskiLogStructure (X : Scheme.{u}) extends ZariskiPrelogStructure X where
  reflectsUnits : ∀ (x : X) (m : toZariskiPrelogStructure.stalk x),
    IsUnit (toZariskiPrelogStructure.stalkAlpha x m) → IsUnit m
  unitsBijective : ∀ x : X,
    Function.Bijective (Units.map (toZariskiPrelogStructure.stalkAlpha x))

/-- The canonical copy of local ring units in the log stalk.
Source: ILO VI 1.1 (blueprint: def-trf-zariski-log-structure). -/
noncomputable def ZariskiLogStructure.unitsIn {X : Scheme.{u}}
    (Z : ZariskiLogStructure X) (x : X) :
    (X.presheaf.stalk x)ˣ →* Z.toZariskiPrelogStructure.stalk x :=
  (Units.coeHom _).comp
    (MulEquiv.ofBijective (Units.map (Z.toZariskiPrelogStructure.stalkAlpha x))
      (Z.unitsBijective x)).symm.toMonoidHom

/-- A chart of the prescribed Zariski log structure on an open: at each point,
the map adjoining ring units is onto with exactly the associated-log pushout kernel.
The ring-valued chart is the structural map composed with the supplied section map.
Source: ILO VI 1.1, VIII 3.3.2--3.3.4(ii)
(blueprint: def-trf-zariski-log-structure). -/
def ZariskiLogStructure.IsChart {X : Scheme.{u}} (Z : ZariskiLogStructure X)
    (U : X.Opens) {P : Type u} [CommMonoid P]
    (h : P →* Z.monoidSheaf.obj.obj (op U)) : Prop :=
  ∀ (x : X) (hx : x ∈ U),
    Function.Surjective
      (((Z.toZariskiPrelogStructure.germ U x hx).hom.comp h).coprod (Z.unitsIn x)) ∧
      Con.ker (((Z.toZariskiPrelogStructure.germ U x hx).hom.comp h).coprod (Z.unitsIn x)) =
        divisorialChartCongruence
          ((Z.toZariskiPrelogStructure.stalkAlpha x).comp
            ((Z.toZariskiPrelogStructure.germ U x hx).hom.comp h)).mrangeRestrict

/-- A map from a Zariski prelog structure to an étale log structure, in adjoint
form on open subschemes. Naturality and compatibility specify the actual structure
map, using the canonical identification of functions on an open with its global sections.
Source: ILO VI 1.1, VIII 3.3.2 (blueprint: def-trf-zariski-log-structure). -/
structure ZariskiPrelogStructure.EtaleMap {X : Scheme.{u}}
    (Z : ZariskiPrelogStructure X) (M : EtaleLogStructure X) where
  sectionMap : ∀ U : X.Opens,
    Z.monoidSheaf.obj.obj (op U) →* M.monoidSheaf.obj.obj (op (Scheme.Etale.mk U.ι))
  naturality : ∀ (U V : X.Opens) (i : U ⟶ V),
    (M.monoidSheaf.obj.map
      (MorphismProperty.Over.homMk (X.homOfLE i.le) (X.homOfLE_ι i.le) trivial).op).hom.comp
        (sectionMap V) = (sectionMap U).comp (Z.monoidSheaf.obj.map i.op).hom
  compatibility : ∀ (U : X.Opens) (s : Z.monoidSheaf.obj.obj (op U)),
    M.alpha.app (op (Scheme.Etale.mk U.ι)) (sectionMap U s) =
      U.topIso.inv (Z.alpha.app (op U) s)

/-- The universal property of the associated étale log structure, normalized by
the given map on Zariski sections. By the inverse-image adjunction this is precisely
logification of the inverse image of the Zariski prelog sheaf. The compatible map
to each étale log structure extends uniquely, so the object and map are determined
up to unique log isomorphism. A log homomorphism over the identity is a monoid-sheaf
morphism commuting with the structural maps (the morphisms of ILO VI 1.1 with identity
underlying scheme map).
Source: ILO VI 1.1, VIII 3.3.2 (blueprint: def-trf-zariski-log-structure). -/
def ZariskiPrelogStructure.EtaleMap.IsAssociation {X : Scheme.{u}}
    {Z : ZariskiPrelogStructure X} {M : EtaleLogStructure X} (e : Z.EtaleMap M) : Prop :=
  ∀ (K : EtaleLogStructure X) (c : Z.EtaleMap K),
    ∃! f : {f : M.monoidSheaf ⟶ K.monoidSheaf // f.hom ≫ K.alpha = M.alpha}, ∀ U : X.Opens,
      (f.val.hom.app (op (Scheme.Etale.mk U.ι))).hom.comp (e.sectionMap U) = c.sectionMap U

end AlgebraicGeometry
