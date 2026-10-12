/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import Sheaf.CategoryTheory.ExactCouple
import Sheaf.AlgebraicGeometry.EtaleInverseImageExact
import Sheaf.CategoryTheory.TruncationTriangle
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Exchange on truncation exact couples

Source: Stacks Project, Tag 0DDE, proof, with the truncation construction of Tags
08J5, 0148 and 011Q (blueprint: lem-weil-pbc-truncation-couple-morphism).
-/

@[expose] public section

set_option autoImplicit false

universe u v w u' v' w'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.TruncationExchange

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
variable {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]

/-- Upper truncation in D+, using the standard t-structure.
Source: Stacks 08J5 (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable abbrev trunc (K : DerivedCategory.Plus A) (q : ℤ) :=
  (DerivedCategory.Plus.TStructure.t.truncLE q).obj K

/-- The sheaf H^q(K) placed in degree zero.
Source: Stacks 0DDE (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable abbrev sheaf (K : DerivedCategory.Plus A) (q : ℤ) :=
  (DerivedCategory.Plus.singleFunctor A 0).obj
    ((DerivedCategory.Plus.homologyFunctor A q).obj K)

/-- The layer H^q(K)[-q].
Source: Stacks 08J5 (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable abbrev layer (K : DerivedCategory.Plus A) (q : ℤ) :=
  (sheaf K q)⟦-q⟧

/-- The canonical inclusion of consecutive upper truncations.
Source: Stacks 08J5 (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable def inclusion (K : DerivedCategory.Plus A) (q : ℤ) :
    trunc K (q - 1) ⟶ trunc K q :=
  (DerivedCategory.Plus.TStructure.t.natTransTruncLEOfLE (q - 1) q (by omega)).app K

/-- The canonical identification H^q(H^q(K)[-q]) = H^q(K).
Source: Stacks 08J5 (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable def layerIso (K : DerivedCategory.Plus A) (q : ℤ) :
    (DerivedCategory.Plus.homologyFunctor A q).obj (layer K q) ≅
      (DerivedCategory.Plus.homologyFunctor A q).obj K :=
  ((DerivedCategory.Plus.homologyFunctor A 0).shiftIso (-q) q 0 (by omega)).app
      (sheaf K q) ≪≫
    (DerivedCategory.homologyFunctor A 0).mapIso
      ((DerivedCategory.Plus.singleFunctorιIso A 0).app
        ((DerivedCategory.Plus.homologyFunctor A q).obj K)) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).app
      ((DerivedCategory.Plus.homologyFunctor A q).obj K)

/-- The projection and connecting morphism of the canonical truncation triangle exist.
The projection is characterized by the cohomology of the inclusion into K.
Proof: use the short exact sequence of consecutive smart truncations (08J5),
then transport its cone along the quasi-isomorphism to H^q(K)[-q]. Descend along
Q and restrict to D+. This is lem-weil-pbc-truncation-triangle; its projection
on H^q is the identity after the canonical identifications.
Source: Stacks 08J5 (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
theorem exists_triangle (K : DerivedCategory.Plus A) (q : ℤ) :
    ∃ j : trunc K q ⟶ layer K q,
      ∃ k : layer K q ⟶ (trunc K (q - 1))⟦(1 : ℤ)⟧,
        (DerivedCategory.Plus.homologyFunctor A q).map j ≫ (layerIso K q).hom =
          (DerivedCategory.Plus.homologyFunctor A q).map
            ((DerivedCategory.Plus.TStructure.t.truncLEι q).app K) ∧
        Triangle.mk (inclusion K q) j k ∈ distTriang (DerivedCategory.Plus A) := by
  sorry

/-- The canonical projection in the truncation triangle, chosen by its characterization.
Source: Stacks 08J5 (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable def projection (K : DerivedCategory.Plus A) (q : ℤ) :
    trunc K q ⟶ layer K q :=
  (exists_triangle K q).choose

/-- The connecting arrow in the canonical truncation triangle.
Source: Stacks 08J5 (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable def boundary (K : DerivedCategory.Plus A) (q : ℤ) :
    layer K q ⟶ (trunc K (q - 1))⟦(1 : ℤ)⟧ :=
  (exists_triangle K q).choose_spec.choose

/-- D^{p,q} = H^{p+q}(F tau_{<=q}K).
Source: Stacks 0DDE, 011Q (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable def D (F : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (K : DerivedCategory.Plus A) (p q : ℤ) : B :=
  (DerivedCategory.Plus.homologyFunctor B (p + q)).obj (F.obj (trunc K q))

/-- E^{p,q} = H^{p+q}(F(H^q(K)[-q])).
Source: Stacks 0DDE, 011Q (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable def E (F : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (K : DerivedCategory.Plus A) (p q : ℤ) : B :=
  (DerivedCategory.Plus.homologyFunctor B (p + q)).obj (F.obj (layer K q))

/-- The inclusion map of bidegree (-1,1), with the total degree transported.
Source: Stacks 011Q (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable def alpha (F : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (K : DerivedCategory.Plus A) (p q : ℤ) : D F K p q ⟶ D F K (p - 1) (q + 1) :=
  (DerivedCategory.Plus.homologyFunctor B (p + q)).map
    (F.map (eqToHom (congrArg (trunc K) (by omega : q = (q + 1) - 1)) ≫
      inclusion K (q + 1))) ≫
    eqToHom (congrArg (fun n : ℤ => (DerivedCategory.Plus.homologyFunctor B n).obj
      (F.obj (trunc K (q + 1)))) (by omega : p + q = (p - 1) + (q + 1)))

/-- The projection map of bidegree (0,0).
Source: Stacks 011Q (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable def g (F : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (K : DerivedCategory.Plus A) (p q : ℤ) : D F K p q ⟶ E F K p q :=
  (DerivedCategory.Plus.homologyFunctor B (p + q)).map (F.map (projection K q))

/-- The connecting map of bidegree (2,-1), using F's composite shift isomorphism.
Source: Stacks 0148, 011Q (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable def f (F : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    [F.CommShift ℤ] (K : DerivedCategory.Plus A) (p q : ℤ) :
    E F K p q ⟶ D F K (p + 2) (q - 1) :=
  (DerivedCategory.Plus.homologyFunctor B (p + q)).map
      (F.map (boundary K q) ≫ (F.commShiftIso (1 : ℤ)).hom.app (trunc K (q - 1))) ≫
    ((DerivedCategory.Plus.homologyFunctor B 0).shiftIso
      (1 : ℤ) (p + q) ((p + 2) + (q - 1)) (by omega)).hom.app (F.obj (trunc K (q - 1)))

/-- The canonical comparison E^{p,q} = H^p(F H^q(K)), via the iterated shift isomorphism.
Source: Stacks 0DDE (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable def pageIso (F : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    [F.CommShift ℤ] (K : DerivedCategory.Plus A) (p q : ℤ) :
    E F K p q ≅ (DerivedCategory.Plus.homologyFunctor B p).obj (F.obj (sheaf K q)) :=
  (DerivedCategory.Plus.homologyFunctor B (p + q)).mapIso
      ((F.commShiftIso (-q)).app (sheaf K q)) ≪≫
    ((DerivedCategory.Plus.homologyFunctor B 0).shiftIso (-q) (p + q) p (by omega)).app
      (F.obj (sheaf K q))

/-- Cohomology of a transformation on the truncation terms.
Source: Stacks 0DDE (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable def tD {F G : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    (t : F ⟶ G) (K : DerivedCategory.Plus A) (p q : ℤ) : D F K p q ⟶ D G K p q :=
  (DerivedCategory.Plus.homologyFunctor B (p + q)).map (t.app (trunc K q))

/-- Cohomology of a transformation on the layers.
Source: Stacks 0DDE (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable def tE {F G : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    (t : F ⟶ G) (K : DerivedCategory.Plus A) (p q : ℤ) : E F K p q ⟶ E G K p q :=
  (DerivedCategory.Plus.homologyFunctor B (p + q)).map (t.app (layer K q))

end CategoryTheory.TruncationExchange

namespace AlgebraicGeometry.Etale

open CategoryTheory.TruncationExchange

/-- Phi = g inverse image after Rf pushforward.
Source: Stacks 0DDE (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable abbrev truncationPhi {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) :=
  (lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus ⋙
    (upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryPlus

/-- Psi = Rf' pushforward after g' inverse image.
Source: Stacks 0DDE (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable abbrev truncationPsi {X' X Y' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y') :=
  (upperStar AddCommGrpCat.{u + 1} g').mapDerivedCategoryPlus ⋙
    (lowerStar AddCommGrpCat.{u + 1} f').rightDerivedFunctorPlus

/-- H^p(Phi M) identifies with g inverse image of R^p f_* M.
Source: Stacks 0DDE (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable def truncationSourceIso {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (M : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℤ) :
    (_root_.DerivedCategory.Plus.homologyFunctor
      (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) p).obj
        ((truncationPhi f g).obj ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj M)) ≅
    (upperStar AddCommGrpCat.{u + 1} g).obj
      ((_root_.DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) p).obj
          ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus.obj
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj M))) :=
  ((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryPlusHomologyFunctorIso p).symm.app
    ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus.obj
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj M))

/-- H^p(Psi M) identifies with R^p f'_* of g' inverse image of M.
Source: Stacks 0DDE (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
noncomputable def truncationTargetIso {X' X Y' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (M : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℤ) :
    (_root_.DerivedCategory.Plus.homologyFunctor
      (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) p).obj
        ((truncationPsi g' f').obj ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj M)) ≅
    (_root_.DerivedCategory.Plus.homologyFunctor
      (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) p).obj
        ((lowerStar AddCommGrpCat.{u + 1} f').rightDerivedFunctorPlus.obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
            ((upperStar AddCommGrpCat.{u + 1} g').obj M))) :=
  (_root_.DerivedCategory.Plus.homologyFunctor
    (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) p).mapIso
      ((lowerStar AddCommGrpCat.{u + 1} f').rightDerivedFunctorPlus.mapIso
        (((upperStar AddCommGrpCat.{u + 1} g').mapDerivedCategoryPlusSingleFunctor 0).app M))

/-- The exchange maps give a morphism of the two truncation exact couples, and on
E they identify with the degree-p exchange of H^q(K).

Proof:
1. The truncation triangles are distinguished (lem-weil-pbc-truncation-triangle).
   Exact inverse image and right derived direct image are triangulated with their
   recorded shift isomorphisms; their composites are triangulated, so their images
   of these triangles are distinguished (lem-weil-pbc-triangulated-functor-composite).
2. The long exact cohomology sequence (lem-sf-derived-homology-long-exact) gives
   image(alpha)=kernel(g), image(g)=kernel(f), image(f)=kernel(alpha), in every
   bidegree, including all consecutive-composite zero identities (def-sp-exact-couple).
3. Naturality of exchange gives the first two squares of the triangles.
   Its shift compatibility gives the third (lem-weil-pbc-derived-exchange-triangulated).
4. The cohomology ladder, including its connecting maps, gives the three couple
   squares (lem-weil-pbc-derived-cohomology-ladder), hence a couple morphism.
5. Apply H^{p+q} to shift compatibility for -q. Naturality of the cohomology shift
   identification gives the pageIso square below. Exact inverse image commutes with
   cohomology (lem-weil-pbc-exact-functor-bounded-below), identifying its source with
   g^{-1}R^p f_* H^q(K); its target is R^p f'_* g'^{-1} H^q(K).
Source: Stacks 0DDE, proof, and 011Q (blueprint: lem-weil-pbc-truncation-couple-morphism). -/
theorem truncation_exchange_couple_morphism
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (∃ P Q : BigradedExactCouple (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) 0,
      P.D = D (truncationPhi f g) K ∧ Q.D = D (truncationPsi g' f') K ∧
      P.E = E (truncationPhi f g) K ∧ Q.E = E (truncationPsi g' f') K ∧
      HEq P.alpha (alpha (truncationPhi f g) K) ∧
      HEq Q.alpha (alpha (truncationPsi g' f') K) ∧
      HEq P.f (CategoryTheory.TruncationExchange.f (truncationPhi f g) K) ∧
      HEq Q.f (CategoryTheory.TruncationExchange.f (truncationPsi g' f') K) ∧
      HEq P.g (CategoryTheory.TruncationExchange.g (truncationPhi f g) K) ∧
      HEq Q.g (CategoryTheory.TruncationExchange.g (truncationPsi g' f') K)) ∧
    (∀ p q : ℤ,
      alpha (truncationPhi f g) K p q ≫
          tD (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq)
            K (p - 1) (q + 1) =
        tD (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq) K p q ≫
          alpha (truncationPsi g' f') K p q) ∧
    (∀ p q : ℤ,
      CategoryTheory.TruncationExchange.g (truncationPhi f g) K p q ≫
          tE (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq) K p q =
        tD (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq) K p q ≫
          CategoryTheory.TruncationExchange.g (truncationPsi g' f') K p q) ∧
    (∀ p q : ℤ,
      CategoryTheory.TruncationExchange.f (truncationPhi f g) K p q ≫
          tD (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq)
            K (p + 2) (q - 1) =
        tE (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq) K p q ≫
          CategoryTheory.TruncationExchange.f (truncationPsi g' f') K p q) ∧
    (∀ p q : ℤ,
      tE (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq) K p q ≫
          (pageIso (truncationPsi g' f') K p q ≪≫
            truncationTargetIso g' f'
              ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K) p).hom =
        (pageIso (truncationPhi f g) K p q ≪≫
          truncationSourceIso f g
            ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K) p).hom ≫
        (truncationSourceIso f g
          ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K) p).inv ≫
        (_root_.DerivedCategory.Plus.homologyFunctor
          (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) p).map
            ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app (sheaf K q)) ≫
        (truncationTargetIso g' f'
          ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K) p).hom) := by
  sorry

end AlgebraicGeometry.Etale
