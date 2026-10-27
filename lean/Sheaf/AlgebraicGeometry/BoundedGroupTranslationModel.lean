/-
Copyright (c) 2026 Q89. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q89
-/
module

public import Sheaf.AlgebraicGeometry.BoundedValuedPoints
public import Sheaf.AlgebraicGeometry.FiberwiseBirationalExtension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Smooth models compatible with translations

Source: BLR, Néron Models, 4.3 Proposition 4(iii), pp.106--107
(blueprint: lem-sfb-bounded-group-translation-model).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- The two translations, tested on every scheme over the extension field. This uses
the existing group on the functor of points, so it does not require a second group law
on a chosen pullback. `right = true` means right translation; `false` means left.
Source: BLR 4.3 Proposition 4(iii)
(blueprint: lem-sfb-bounded-group-translation-model). -/
def IsGenericGroupTranslation {K : Scheme.{u}} (G : Over K) [GrpObj G]
    {L : Scheme.{u}} (j : L ⟶ K) (g : Over.mk j ⟶ G)
    (right : Bool) (t : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G) : Prop :=
  ∀ (W : Over L) (x : W ⟶ (Over.pullback j).obj G),
    ((Over.mapPullbackAdj j).homEquiv W G).symm (x ≫ t) =
      if right then
        (((Over.mapPullbackAdj j).homEquiv W G).symm x) * (Over.homMk W.hom ≫ g)
      else (Over.homMk W.hom ≫ g) * (((Over.mapPullbackAdj j).homEquiv W G).symm x)

/-- The canonical comparison from the iterated local generic fibre of a model to the
base-changed generic model. The equality fixes the extension-field structure, and
`Over.pullbackComp` supplies the canonical associativity comparisons.
Source: BLR 4.3 Proposition 4(iii)
(blueprint: lem-sfb-bounded-group-translation-model). -/
def translationModelGenericComparison
    {S K A L : Scheme.{u}} (a : K ⟶ S) (p : A ⟶ S) (q : L ⟶ A) (j : L ⟶ K)
    (h : q ≫ p = j ≫ a) (Y : Over S) (G : Over K)
    (e : (Over.pullback a).obj Y ≅ G) :
    (Over.pullback q).obj ((Over.pullback p).obj Y) ≅ (Over.pullback j).obj G :=
  ((Over.pullbackComp q p).app Y).symm ≪≫
    eqToIso (congrArg (fun f ↦ (Over.pullback f).obj Y) h) ≪≫
    (Over.pullbackComp j a).app Y ≪≫ (Over.pullback j).mapIso e

/-- A bounded smooth algebraic group has a translation-compatible smooth model.
Source: BLR 4.3 Proposition 4(iii), pp.106--107
(blueprint: lem-sfb-bounded-group-translation-model).

Proof:
1. By lem-sfb-invariant-volume-translation-character choose an invariant volume form.
By lem-sfb-weak-neron-family-rational-property choose a finite weak Néron family.
The orders in this family attain a minimum, by
lem-sfb-smooth-model-volume-order-comparison. Choose finitely many representatives
of minimal classes using lem-sfb-minimal-volume-model-smooth-base-change.
Their rational disjointness permits lem-sfb-rationally-disjoint-model-separated-gluing
to glue their opens along the generic group. The result is smooth, separated, of
finite type, with nonempty special fibre, all its components having minimal order.
2. Fix a smooth finite-type Z and a generic point of its special fibre. The weak-family
lemma makes its local ring A a DVR and base changes the weak family to A, giving
boundedness over A. Minimal-class base change gives all minimal classes over A.
Smoothness, separatedness and finite type persist by lem-pc-proper-base-change,
lem-weil-pbc-separated-base-change and lem-sfb-finite-type-composition-base-change.
3. For a left or right translation its volume multiplier is a unit, by the invariant
volume lemma. On each component open the weak rational property extends it to a
weak-family member. Order comparison and minimality force equality of orders, so
the extension is an open immersion and its target is birational to a minimal
component open of the glued model. This gives the desired componentwise map.
4. By lem-sfb-smooth-trait-local-rational-spreading, generic uniqueness glues these
maps. Equal-order comparison makes the map an open immersion on its entire domain.
Apply the construction to the inverse translation. Composing and using generic
uniqueness shows that the two maps permute special components inversely. Their
images and domains are therefore fibrewise dense; intersecting with the inverse
images of the opposite domains exhibits an isomorphism between base-dense opens.
No group structure or Néron mapping property is claimed for Y. -/
theorem exists_bounded_group_translation_model
    (R E : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field E] [Algebra R E] [IsFractionRing R E]
    (G : Over (Spec (.of E))) [GrpObj G] [Smooth G.hom]
    [IsSeparated G.hom] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ Spec (.of R))
    (ht : ∀ x, t x = IsLocalRing.closedPoint R)
    (hb : HasBoundedStrictHenselianPoints R E t G) :
    ∃ (Y : Over (Spec (.of R)))
      (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R E)))).obj Y ≅ G),
      Smooth Y.hom ∧ IsSeparated Y.hom ∧ LocallyOfFiniteType Y.hom ∧ QuasiCompact Y.hom ∧
      Nonempty (Y.hom.fiber (IsLocalRing.closedPoint R)) ∧
      ∀ (Z : Over (Spec (.of R))), Smooth Z.hom → LocallyOfFiniteType Z.hom →
        QuasiCompact Z.hom → ∀ ξ : Z.hom.fiber (IsLocalRing.closedPoint R),
        (∃ C ∈ irreducibleComponents (Z.hom.fiber (IsLocalRing.closedPoint R)),
          IsGenericPoint ξ C) →
        ∃ (hA : IsDomain (Z.left.presheaf.stalk (Z.hom.fiberι _ ξ)))
          (_ : IsDiscreteValuationRing (Z.left.presheaf.stalk (Z.hom.fiberι _ ξ))),
          ∃ (j : Spec (.of (FractionRing (Z.left.presheaf.stalk (Z.hom.fiberι _ ξ)))) ⟶
              Spec (.of E))
            (hj : Spec.map (CommRingCat.ofHom (algebraMap
              (Z.left.presheaf.stalk (Z.hom.fiberι _ ξ))
              (FractionRing (Z.left.presheaf.stalk (Z.hom.fiberι _ ξ))))) ≫
              Z.left.fromSpecStalk (Z.hom.fiberι _ ξ) ≫ Z.hom =
              j ≫ Spec.map (CommRingCat.ofHom (algebraMap R E))),
          ∀ (g : Over.mk j ⟶ G) (right : Bool),
          ∃ τ : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G,
            IsGenericGroupTranslation G j g right τ ∧
            HasFiberwiseBirationalExtension
              (Spec.map (CommRingCat.ofHom (algebraMap
                (Z.left.presheaf.stalk (Z.hom.fiberι _ ξ))
                (FractionRing (Z.left.presheaf.stalk (Z.hom.fiberι _ ξ))))))
              ((Over.pullback (Z.left.fromSpecStalk (Z.hom.fiberι _ ξ) ≫ Z.hom)).obj Y)
              ((translationModelGenericComparison
                (Spec.map (CommRingCat.ofHom (algebraMap R E)))
                (Z.left.fromSpecStalk (Z.hom.fiberι _ ξ) ≫ Z.hom)
                (Spec.map (CommRingCat.ofHom (algebraMap
                  (Z.left.presheaf.stalk (Z.hom.fiberι _ ξ))
                  (FractionRing (Z.left.presheaf.stalk (Z.hom.fiberι _ ξ))))))
                j hj Y G e).hom ≫ τ ≫
                (translationModelGenericComparison
                  (Spec.map (CommRingCat.ofHom (algebraMap R E)))
                  (Z.left.fromSpecStalk (Z.hom.fiberι _ ξ) ≫ Z.hom)
                  (Spec.map (CommRingCat.ofHom (algebraMap
                    (Z.left.presheaf.stalk (Z.hom.fiberι _ ξ))
                    (FractionRing (Z.left.presheaf.stalk (Z.hom.fiberι _ ξ))))))
                  j hj Y G e).inv) := by
  sorry

end AlgebraicGeometry
