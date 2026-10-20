/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q71
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Sheaf.Paper.OrientedNearbyCycles
import Sheaf.CategoryTheory.Sites.OrientedProductLargeSites
import Sheaf.CategoryTheory.Sites.OrientedProductSliceLocalization
import WeilConjectures.AlgebraicGeometry.FullAffineEtaleTopos

/-!
# Affine slice sites for oriented products

Source: Illusie--Laszlo--Orgogozo, Exposé XI 1.10(b), equivalence (1.b) and
localization (1.c), printed pp. 175--176 (blueprint: lem-trf-oriented-affine-slice-site).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace CategoryTheory

/-- The common-universe small étale site used for scheme morphisms.
(blueprint: lem-trf-oriented-affine-slice-site). -/
abbrev schemeEtaleSite (T : Scheme.{u}) :=
  AlgebraicGeometry.OrientedNearbyCycles.EtaleSite.{u, u + 1} T

/-- The forgetful functor from the common-universe étale site.
(blueprint: lem-trf-oriented-affine-slice-site). -/
abbrev schemeEtaleDown (T : Scheme.{u}) : schemeEtaleSite T ⥤ T.Etale :=
  AsSmall.down

/-- Base change on the common-universe étale sites.
(blueprint: lem-trf-oriented-affine-slice-site). -/
abbrev schemeEtaleBaseChange {T B : Scheme.{u}} (h : T ⟶ B) :
    schemeEtaleSite B ⥤ schemeEtaleSite T :=
  AlgebraicGeometry.OrientedNearbyCycles.etaleBaseChange.{u, u + 1} h

/-- The oriented-product site attached to three schemes and two structure maps.
(blueprint: lem-trf-oriented-affine-slice-site). -/
def schemeOrientedProductTopology {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) :
    GrothendieckTopology
      (OrientedProduct.Triples (schemeEtaleBaseChange f)
        (schemeEtaleBaseChange g)) :=
  OrientedProduct.topology (AlgebraicGeometry.OrientedNearbyCycles.etaleTopology X).toPretopology
    (AlgebraicGeometry.OrientedNearbyCycles.etaleTopology Y).toPretopology
    (schemeEtaleBaseChange f)
    (schemeEtaleBaseChange g)

/-- The sheaf represented by a triple in an oriented product site.
(blueprint: lem-trf-oriented-affine-slice-site). -/
noncomputable def orientedTripleRepresentable {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S)
    (Z : OrientedProduct.Triples
      (schemeEtaleBaseChange f)
      (schemeEtaleBaseChange g)) :
    Sheaf (schemeOrientedProductTopology f g) (Type (u + 1)) :=
  (OrientedProduct.associated (schemeOrientedProductTopology f g)).obj Z

/-- The inverse-image functor of the slice projection, on sheaves of sets.
(blueprint: lem-trf-oriented-affine-slice-site). -/
noncomputable def sliceInverseImage {C : Type w} [Category.{v} C]
    [HasFiniteProducts C] (H : C) :
    C ⥤ CostructuredArrow (𝟭 C) H where
  obj F := CostructuredArrow.mk (Limits.prod.snd : F ⨯ H ⟶ H)
  map α := CostructuredArrow.homMk (Limits.prod.map α (𝟙 H)) (by simp)

/-- The underlying projection from the slice category over a sheaf.
This is used only to define the geometric projection below.
(blueprint: lem-trf-oriented-affine-slice-site). -/
def sliceProjection {C : Type w} [Category.{v} C] (H : C) :
    CostructuredArrow (𝟭 C) H ⥤ C :=
  CostructuredArrow.proj (𝟭 C) H

/-- The geometric projection attached to a chosen localization equivalence.
Its value is fixed by that equivalence, rather than chosen independently.
(blueprint: lem-trf-oriented-affine-slice-site). -/
def geometricSliceProjection {C : Type w} [Category.{v} C]
    {D : Type w} [Category.{v} D] (H : C)
    (e : CostructuredArrow (𝟭 C) H ≌ D) : D ⥤ C :=
  e.inverse ⋙ sliceProjection H

/-- The canonical map from the first component of a triple to its middle scheme.
(blueprint: lem-trf-oriented-affine-slice-site). -/
def tripleFirstToMiddle {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S)
    (Z : OrientedProduct.Triples
      (schemeEtaleBaseChange f)
      (schemeEtaleBaseChange g)) :
    ((schemeEtaleDown X).obj Z.left.1).left ⟶ ((schemeEtaleDown S).obj Z.right).left :=
  ((schemeEtaleDown X).map Z.hom.1).left ≫ pullback.fst ((schemeEtaleDown S).obj Z.right).hom f

/-- The canonical map from the second component of a triple to its middle scheme.
(blueprint: lem-trf-oriented-affine-slice-site). -/
def tripleSecondToMiddle {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S)
    (Z : OrientedProduct.Triples
      (schemeEtaleBaseChange f)
      (schemeEtaleBaseChange g)) :
    ((schemeEtaleDown Y).obj Z.left.2).left ⟶ ((schemeEtaleDown S).obj Z.right).left :=
  ((schemeEtaleDown Y).map Z.hom.2).left ≫ pullback.fst ((schemeEtaleDown S).obj Z.right).hom g

/-- The terminal object of the slice category over a sheaf.
(blueprint: lem-trf-oriented-affine-slice-site). -/
def sliceTerminal {C : Type w} [Category.{v} C] (H : C) :
    CostructuredArrow (𝟭 C) H :=
  CostructuredArrow.mk (𝟙 H)

/-- The full category of affine triples over an affine triple `Z`.
(blueprint: lem-trf-oriented-affine-slice-site). -/
def affineTripleProperty {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (Z : OrientedProduct.Triples
      (schemeEtaleBaseChange f)
      (schemeEtaleBaseChange g)) :
    ObjectProperty
      (OrientedProduct.Triples
        (schemeEtaleBaseChange
          (tripleFirstToMiddle f g Z))
        (schemeEtaleBaseChange
          (tripleSecondToMiddle f g Z))) :=
  fun T ↦
    IsAffine ((AsSmall.down : schemeEtaleSite
      ((schemeEtaleDown X).obj
        Z.left.1).left ⥤ _).obj T.left.1).left ∧
    IsAffine ((AsSmall.down : schemeEtaleSite
      ((schemeEtaleDown Y).obj
        Z.left.2).left ⥤ _).obj T.left.2).left ∧
    IsAffine ((AsSmall.down : schemeEtaleSite
      ((schemeEtaleDown S).obj
        Z.right).left ⥤ _).obj T.right).left

/-- The topology on affine triples, induced from the oriented-product topology.
(blueprint: lem-trf-oriented-affine-slice-site). -/
def affineTripleTopology {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (Z : OrientedProduct.Triples
      (schemeEtaleBaseChange f)
      (schemeEtaleBaseChange g)) :
    GrothendieckTopology (affineTripleProperty f g Z).FullSubcategory :=
  (affineTripleProperty f g Z).ι.inducedTopology
    (schemeOrientedProductTopology (tripleFirstToMiddle f g Z)
      (tripleSecondToMiddle f g Z))

/-- A finite family of one of the three generating oriented-product cover types.
Membership in `OrientedProduct.generators` records the factor-cover alternatives
and the singleton base-change alternative, including their structural equations. -/
def affineGeneratorFamily {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (Z : OrientedProduct.Triples
      (schemeEtaleBaseChange f) (schemeEtaleBaseChange g))
    (T : (affineTripleProperty f g Z).FullSubcategory)
    {I : Type (u + 1)} (E : I → (affineTripleProperty f g Z).FullSubcategory)
    (r : ∀ i, E i ⟶ T) : Prop :=
  Sieve.generate (Presieve.ofArrows E r) ∈ affineTripleTopology f g Z T

/-- The canonical evaluation of a slice section at the distinguished triple.
The projection to the first product factor is followed by the sheafification
adjunction and Yoneda evaluation. -/
noncomputable def sliceSectionEvaluation {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (Z : OrientedProduct.Triples
      (schemeEtaleBaseChange f) (schemeEtaleBaseChange g))
    (F : Sheaf (schemeOrientedProductTopology f g) (Type (u + 1)))
    (s : sliceTerminal (orientedTripleRepresentable f g Z) ⟶
      (sliceInverseImage (orientedTripleRepresentable f g Z)).obj F) :
    F.obj.obj (Opposite.op Z) :=
  yonedaEquiv ((sheafificationAdjunction (schemeOrientedProductTopology f g)
    (Type (u + 1))).homEquiv _ _
      (s.left ≫ Limits.prod.fst))

/-- The slice localization and finite affine-site presentation.
(blueprint: lem-trf-oriented-affine-slice-site).

Proof (Illusie--Laszlo--Orgogozo, Exposé XI 1.10(b), pp. 175--176, and XI 2.5,
pp. 179--180): identify the slice site with the relative triple site; construct
the affine full subsite using affine étale bases and affine fibre products; check
the three oriented-product generators and finite refinements; apply the affine
site comparison; and identify the product inverse image and its canonical
evaluation by sheafification adjunction and Yoneda. -/
theorem oriented_affine_slice_site {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (Z : OrientedProduct.Triples
      (schemeEtaleBaseChange f)
      (schemeEtaleBaseChange g))
    [IsAffine ((schemeEtaleDown X).obj Z.left.1).left]
    [IsAffine ((schemeEtaleDown Y).obj Z.left.2).left]
    [IsAffine ((schemeEtaleDown S).obj Z.right).left] :
    ∃ (e : CostructuredArrow (𝟭 (Sheaf (schemeOrientedProductTopology f g) (Type (u + 1))))
        (orientedTripleRepresentable f g Z) ≌
        Sheaf (schemeOrientedProductTopology (tripleFirstToMiddle f g Z)
          (tripleSecondToMiddle f g Z)) (Type (u + 1))),
      Nonempty (e.functor ⋙ geometricSliceProjection
        (orientedTripleRepresentable f g Z) e ≅
        sliceProjection (orientedTripleRepresentable f g Z)) ∧
      HasFiniteLimits (affineTripleProperty f g Z).FullSubcategory ∧
      (∀ (T : (affineTripleProperty f g Z).FullSubcategory)
        (R : Sieve T), R ∈ affineTripleTopology f g Z T →
        ∃ (I : Type (u + 1)) (_ : Finite I) (E : I →
          (affineTripleProperty f g Z).FullSubcategory)
          (r : ∀ i, E i ⟶ T),
          affineGeneratorFamily f g Z T E r ∧
          Sieve.generate (Presieve.ofArrows E r) ∈ affineTripleTopology f g Z T ∧
            Sieve.generate (Presieve.ofArrows E r) ≤ R) ∧
      Nonempty
        (Sheaf (affineTripleTopology f g Z) (Type (u + 1)) ≌
          Sheaf (schemeOrientedProductTopology (tripleFirstToMiddle f g Z)
            (tripleSecondToMiddle f g Z)) (Type (u + 1))) ∧
      (∀ (F : Sheaf (schemeOrientedProductTopology f g) (Type (u + 1))),
        Function.Bijective (sliceSectionEvaluation f g Z F) ∧
        (∀ {G : Sheaf (schemeOrientedProductTopology f g) (Type (u + 1))}
          (α : F ⟶ G)
          (s : sliceTerminal (orientedTripleRepresentable f g Z) ⟶
            (sliceInverseImage (orientedTripleRepresentable f g Z)).obj F),
          sliceSectionEvaluation f g Z G
              (s ≫ (sliceInverseImage (orientedTripleRepresentable f g Z)).map α) =
            α.hom.app (Opposite.op Z) (sliceSectionEvaluation f g Z F s))) := by
  sorry

end CategoryTheory
