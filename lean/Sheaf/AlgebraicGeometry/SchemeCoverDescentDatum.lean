/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver
public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import Sheaf.CategoryTheory.SiteCoveringAxioms

/-! # Scheme descent data on a covering family

Source: Stacks Project, Descent, Tag 02W5 and the following remark;
Tag 023V for effectivity (blueprint: def-trf-scheme-cover-descent-datum).

## Main definitions

* `SchemeCoverDescentDatum`: local schemes with descent of their represented sheaves.
* `SchemeCoverDescent`: its category of compatible local maps.
* `SchemeCoverDescentDatum.IsEffective`: realization by Cartesian squares of schemes.
* `IsLocallyRepresentableFppfSheaf`: the full-subcategory predicate on global sheaves.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Scheme descent data for a family, expressed through the fully faithful Yoneda embedding.
Source: Stacks Project, Descent, Tag 02W5
(blueprint: def-trf-scheme-cover-descent-datum).

The local schemes are retained as data. The represented sheaves carry natural comparison
isomorphisms on every test overlap and the cocycle, using Mathlib's descent-data structure.
Conjugating these comparisons by `representation` gives precisely the scheme overlap maps
by Yoneda; their naturality and cocycle are the scheme naturality and cocycle. Morphisms in
the induced category below are compatible local sheaf maps, hence uniquely local scheme maps.
The diagonal normalization follows from the invertible cocycle and adds no hypothesis. -/
structure SchemeCoverDescentDatum
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}}
    (f : ∀ i, U i ⟶ T) where
  /-- The local sheaves and all transition isomorphisms, with their cocycle. -/
  data : (Scheme.fppfTopology.pseudofunctorOver (Type (u + 1))).DescentData f
  /-- The local schemes over the covering members. -/
  localScheme : ∀ i, Over (U i)
  /-- The specified natural identifications with the represented local sheaves. -/
  representation : ∀ i, (data.obj i).obj.RepresentableBy (localScheme i)

/-- The category of scheme descent data: maps are families of local scheme maps compatible
with the transition isomorphisms, expressed by Yoneda as compatible maps of local sheaves.
Source: Stacks Project, Descent, Tag 02W5
(blueprint: def-trf-scheme-cover-descent-datum). -/
abbrev SchemeCoverDescent
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}}
    (f : ∀ i, U i ⟶ T) :=
  InducedCategory
    ((Scheme.fppfTopology.pseudofunctorOver (Type (u + 1))).DescentData f)
    (SchemeCoverDescentDatum.data (f := f))

/-- The faithful presentation by descent data of local representable sheaves.
Source: Stacks Project, Descent, Tag 02W5
(blueprint: def-trf-scheme-cover-descent-datum). -/
def schemeCoverDescentForget
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}}
    (f : ∀ i, U i ⟶ T) :
    SchemeCoverDescent f ⥤
      (Scheme.fppfTopology.pseudofunctorOver (Type (u + 1))).DescentData f :=
  inducedFunctor (SchemeCoverDescentDatum.data (f := f))

/-- Geometric effectivity: the local schemes fit into Cartesian squares over one global
scheme, and their maps to it are invariant under the given transitions on all test points.
Source: Stacks Project, Descent, Tags 023V and 02W5
(blueprint: def-trf-scheme-cover-descent-datum).

This is the family version of `Over.DescentDatum.IsEffective`: the Cartesian-square clause
is the required local base-change isomorphism, and invariance says these isomorphisms induce
the specified overlap maps. No global sheaf or representability criterion enters this definition. -/
def SchemeCoverDescentDatum.IsEffective
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}}
    {f : ∀ i, U i ⟶ T} (D : SchemeCoverDescentDatum f) : Prop :=
  ∃ (X : Over T) (q : ∀ i, (D.localScheme i).left ⟶ X.left),
    (∀ i, IsPullback (q i) (D.localScheme i).hom X.hom (f i)) ∧
    ∀ (W : Scheme.{u}) (p : W ⟶ T) (i j : I)
      (a : W ⟶ U i) (b : W ⟶ U j) (ha : a ≫ f i = p) (hb : b ≫ f j = p)
      (x : (D.data.obj i).obj.obj (op ((Over.map a).obj (Over.mk (𝟙 W))))),
      ((D.representation j).homEquiv.symm
        ((D.data.hom p a b ha hb).hom.app (op (Over.mk (𝟙 W))) x)).left ≫ q j =
        ((D.representation i).homEquiv.symm x).left ≫ q i

/-- Local representability on the big fppf site: restriction to each covering member is
representable, equivalently each product `h_{U_i} × H` is representable.
Source: Stacks Project, Descent, Tag 02W5 and the following remark
(blueprint: def-trf-scheme-cover-descent-datum). -/
def IsLocallyRepresentableFppfSheaf
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}}
    (f : ∀ i, U i ⟶ T) :
    ObjectProperty (Sheaf (Scheme.fppfTopology.over T) (Type (u + 1))) :=
  fun H ↦ ∀ i,
    ((Scheme.fppfTopology.overMapPullback (Type (u + 1)) (f i)).obj H).obj.IsRepresentable

end AlgebraicGeometry
