/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q103
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.Thickening

/-! # Zariski square-zero extensions with a specified kernel

Source: Stacks Project, Tag 05YV, lemma-first-order-thickening
(blueprint: def-sfb-zariski-square-zero-extension).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- Forget only the locality condition on a scheme morphism.
Source: Stacks Project, Tag 01IJ
(blueprint: def-sfb-zariski-square-zero-extension). -/
abbrev schemeToRinged : Scheme.{u} ⥤ SheafedSpace CommRingCat.{u} :=
  Scheme.forgetToLocallyRingedSpace ⋙ LocallyRingedSpace.forgetToSheafedSpace

/-- A Zariski ring-sheaf extension, with its actual additive kernel identified with `G`.
The base map is the adjoint description of the inverse-image base algebra structure.
Exactness at the quotient means local surjectivity, without sectionwise surjectivity.
Source: Stacks Project, Tag 05YV
(blueprint: def-sfb-zariski-square-zero-extension). -/
structure ZariskiSquareZeroExtension {X B : Scheme.{u}} (f : X ⟶ B) (G : X.Modules) where
  algebra : TopCat.Sheaf CommRingCat.{u} X
  quotient : algebra.obj ⟶ X.presheaf
  inclusion (U : X.Opens) : G.val.obj (op U) →+ algebra.obj.obj (op U)
  naturality {U V : X.Opens} (a : U ⟶ V) (m : G.val.obj (op V)) :
    algebra.obj.map a.op (inclusion V m) = inclusion U (G.val.map a.op m)
  injective (U : X.Opens) : Function.Injective (inclusion U)
  kernel (U : X.Opens) (a : algebra.obj.obj (op U)) :
    quotient.app (op U) a = 0 ↔ ∃ m : G.val.obj (op U), inclusion U m = a
  locally_surjective (U : X.Opens) (a : X.presheaf.obj (op U)) (x : U) :
    ∃ (V : X.Opens) (h : V ≤ U) (_ : x.val ∈ V) (b : algebra.obj.obj (op V)),
      quotient.app (op V) b = X.presheaf.map (homOfLE h).op a
  square_zero (U : X.Opens) (m n : G.val.obj (op U)) :
    inclusion U m * inclusion U n = 0
  scalar (U : X.Opens) (a : algebra.obj.obj (op U)) (m : G.val.obj (op U)) :
    inclusion U (quotient.app (op U) a • m) = a * inclusion U m
  base : B.presheaf ⟶ (Opens.map f.base).op ⋙ algebra.obj
  base_quotient : base ≫ Functor.whiskerLeft (Opens.map f.base).op quotient = f.c

/-- The ringed space of an extension, on the original topological space.
Source: Stacks Project, Tag 05YV
(blueprint: def-sfb-zariski-square-zero-extension). -/
def ZariskiSquareZeroExtension.space {X B : Scheme.{u}} {f : X ⟶ B} {G : X.Modules}
    (D : ZariskiSquareZeroExtension f G) : SheafedSpace CommRingCat.{u} where
  carrier := X.carrier
  presheaf := D.algebra.obj
  IsSheaf := D.algebra.property

/-- The quotient morphism of ringed spaces has the identity point map.
Source: Stacks Project, Tag 05YV
(blueprint: def-sfb-zariski-square-zero-extension). -/
def ZariskiSquareZeroExtension.reduction {X B : Scheme.{u}} {f : X ⟶ B} {G : X.Modules}
    (D : ZariskiSquareZeroExtension f G) : X.toSheafedSpace ⟶ D.space :=
  InducedCategory.homMk { base := 𝟙 X.carrier, c := D.quotient }

/-- The quotient map restricted to an arbitrary open, retaining its actual components.
Source: Stacks Project, Tag 05YV
(blueprint: def-sfb-zariski-square-zero-extension). -/
def ZariskiSquareZeroExtension.reductionOpen {X B : Scheme.{u}} {f : X ⟶ B}
    {G : X.Modules} (D : ZariskiSquareZeroExtension f G) (U : X.Opens) :
    U.toScheme.toSheafedSpace ⟶ D.space.restrict U.isOpenEmbedding :=
  InducedCategory.homMk
    { base := 𝟙 (TopCat.of U)
      c := Functor.whiskerLeft U.isOpenEmbedding.functor.op D.quotient }

/-- The base algebra structure as a morphism of ringed spaces.
Source: Stacks Project, Tag 05YV
(blueprint: def-sfb-zariski-square-zero-extension). -/
def ZariskiSquareZeroExtension.toBase {X B : Scheme.{u}} {f : X ⟶ B} {G : X.Modules}
    (D : ZariskiSquareZeroExtension f G) : D.space ⟶ B.toSheafedSpace :=
  InducedCategory.homMk { base := f.base, c := D.base }

/-- A marked realization uses the specified quotient and base algebra maps.
Source: Stacks Project, Tag 05YV
(blueprint: def-sfb-zariski-square-zero-extension). -/
def ZariskiSquareZeroExtension.Realizes {X B : Scheme.{u}} {f : X ⟶ B} {G : X.Modules}
    (D : ZariskiSquareZeroExtension f G) (Y : Scheme.{u})
    (e : Y.toSheafedSpace ≅ D.space) (j : X ⟶ Y) (q : Y ⟶ B) : Prop :=
  IsFirstOrderThickening j ∧ j ≫ q = f ∧
    schemeToRinged.map j ≫ e.hom = D.reduction ∧ e.hom ≫ D.toBase = schemeToRinged.map q

/-- Maps between extension ring sheaves are written in the geometric direction.
Their structure-sheaf component runs contravariantly and their point map is the identity.
Source: Stacks Project, Tag 05YV and locally ringed space morphisms, Tag 01HB
(blueprint: def-sfb-zariski-square-zero-extension). -/
def ZariskiSquareZeroExtension.IsExtensionMap {X B : Scheme.{u}} {f : X ⟶ B}
    {G H : X.Modules} (D : ZariskiSquareZeroExtension f G)
    (E : ZariskiSquareZeroExtension f H) (a : D.space ⟶ E.space) : Prop :=
  a.hom.base = 𝟙 X.carrier ∧ D.reduction ≫ a = E.reduction ∧ a ≫ E.toBase = D.toBase

end AlgebraicGeometry
