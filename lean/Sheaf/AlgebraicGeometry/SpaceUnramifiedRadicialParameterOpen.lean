/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenFactorSchemeTests
import Sheaf.AlgebraicGeometry.SpaceInvariantOpenQuotient
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus

/-! # The unramified and radicial parameter open of algebraic spaces

Source: Stacks Project, More on Morphisms of Spaces, Tag 05X9,
`spaces-more-morphisms-lemma-where-unramified-universally-injective`
(blueprint: lem-sfb-space-unramified-radicial-parameter-open).

The auxiliary constructions bundle the existing sheaf fibre product and its canonical
map under a commutative triangle. Universal injectivity is expanded as injectivity on
point classes after every algebraic-space base change, and closedness of a map on point
spaces as closedness of point images; both are written with the point classes and
representative maps of def-a1-space-point-topology.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The sheaf fibre product, bundled using its established algebraic-space property.
Source: Stacks Project, Tag 05X9, the spaces denoted `X_{Z'}` and `Y_{Z'}`;
closure under fibre products is lem-trf-space-fibre-products-etale-covers
(blueprint: lem-sfb-space-unramified-radicial-parameter-open). -/
def parameterBaseChange {S : Scheme.{u}} {A B T : AlgebraicSpace S}
    (p : A ⟶ B) (h : T ⟶ B) : AlgebraicSpace S :=
  ⟨Limits.pullback p.hom h.hom, (fibreProduct_isAlgebraicSpace A T B p h).1⟩

/-- The canonical base-changed map of a commutative triangle, with components `f` and
identity on the parameter. Its data are the categorical pullback map, without a choice.
Source: Stacks Project, Tag 05X9, the map `f_{Z'}`
(blueprint: lem-sfb-space-unramified-radicial-parameter-open). -/
def parameterBaseChangeMap {S : Scheme.{u}} {A C B T : AlgebraicSpace S}
    (p : A ⟶ B) (q : C ⟶ B) (f : A ⟶ C) (w : f ≫ q = p) (h : T ⟶ B) :
    parameterBaseChange p h ⟶ parameterBaseChange q h :=
  ObjectProperty.homMk
    (pullback.map p.hom h.hom q.hom h.hom f.hom (𝟙 T.obj) (𝟙 B.obj)
      (by simpa using (congrArg (fun k : A ⟶ B ↦ k.hom) w).symm) (by simp))

/-- A single open represents unramifiedness and universal injectivity after arbitrary
algebraic-space parameter change. Closedness is assumed only for the original maps.
Source: Stacks Project, More on Morphisms of Spaces, Tag 05X9
(blueprint: lem-sfb-space-unramified-radicial-parameter-open).

Proof:
1. Apply lem-sfb-space-closed-source-unramified-base-open to obtain the unramified
parameter open B0, using local finite type and closedness of p. The identity test on B0
makes f0 unramified.
2. By lem-trf-space-fibre-products-etale-covers, D0 = A0 ×_{C0} A0 is D ×_B B0,
where D = A ×_C A. The open-factor and point-open calculus nodes identify its points
with the inverse image of B0. The restriction r : D0 → B0 remains closed: write a
relatively closed F as F' intersected with that inverse image; then r(F) = p2(F') ∩ B0.
3. By lem-sfb-space-unramified-diagonal-open the diagonal of f0 is an open J in D0.
Its complement E is closed. Thus O = B0 minus r(E) is open; choose an atlas using
def-trf-algebraic-space and apply lem-a1-space-invariant-open-quotient to obtain the
open subspace V of B0 with point image O. Its composite inclusion in B is open on
all scheme tests (def-a1-space-open-subspace).
4. For h : T → B0, fibre products identify the diagonal of f_T with the pullback of J.
By lem-a1-space-open-factor-scheme-tests its image is the inverse image of J.
By lem-a1-space-point-open-calculus every compatible pair of points lifts to a fibre
product. Thus the diagonal is point-surjective exactly when h(T) avoids r(E), which
is exactly factorization through V. No universal closedness is assumed here.
5. For any g : X → Y, point-surjectivity of its diagonal is equivalent to universal
injectivity. In the forward direction, the point-lifting calculation preserves diagonal
surjectivity under every base change; lift any pair over the same point to the relative
square, then through the diagonal, so the pair is equal. Conversely, injectivity of the
first projection X ×_Y X → X makes each d equal to the diagonal of its first projection.
This is the elementary Tag 040X argument using the fibre-product and point-calculus nodes.
6. For arbitrary h : T → B, unramifiedness first factors h through B0. Steps 4 and 5
then characterize factorization through V by universal injectivity. Conversely a factor
through V factors through B0, giving unramifiedness, and steps 4 and 5 give universal
injectivity. These are the canonical maps defined above, including for empty T. -/
theorem exists_openSubspace_unramified_radicial_parameter {S : Scheme.{u}}
    (A C B : AlgebraicSpace S) (p : A ⟶ B) (q : C ⟶ B) (f : A ⟶ C)
    (w : f ≫ q = p) (hp_lft : MapIsLocally (@LocallyOfFiniteType) p)
    (hp_closed : ∀ Z : Set (Point A.obj.obj), IsClosed Z →
      IsClosed {y : Point B.obj.obj | ∃ a : PointRepresentative A.obj.obj,
        (Quot.mk _ a : Point A.obj.obj) ∈ Z ∧ (Quot.mk _ (a.map p.hom.hom) : Point _) = y})
    (hp2_closed : ∀ Z : Set (Point (Limits.pullback f.hom f.hom).obj), IsClosed Z →
      IsClosed {y : Point B.obj.obj | ∃ d : PointRepresentative (Limits.pullback f.hom f.hom).obj,
        (Quot.mk _ d : Point (Limits.pullback f.hom f.hom).obj) ∈ Z ∧
          (Quot.mk _ (d.map ((pullback.fst f.hom f.hom) ≫ p.hom).hom) : Point _) = y}) :
    ∃ V : OpenSubspace B, ∀ (T : AlgebraicSpace S) (h : T ⟶ B),
      (MapIsLocally (@IsUnramified) (parameterBaseChangeMap p q f w h) ∧
        ∀ (Y : AlgebraicSpace S) (g : Y ⟶ parameterBaseChange q h)
          (a b : PointRepresentative
            (Limits.pullback (parameterBaseChangeMap p q f w h).hom g.hom).obj),
          (Quot.mk _ (a.map (pullback.snd (parameterBaseChangeMap p q f w h).hom g.hom).hom) :
              Point Y.obj.obj) =
            Quot.mk _ (b.map (pullback.snd (parameterBaseChangeMap p q f w h).hom g.hom).hom) →
          (Quot.mk _ a : Point (Limits.pullback (parameterBaseChangeMap p q f w h).hom g.hom).obj) =
            Quot.mk _ b) ↔
      ∃ l : T.obj.obj ⟶ V.val.toFunctor, l ≫ V.val.ι = h.hom.hom := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
