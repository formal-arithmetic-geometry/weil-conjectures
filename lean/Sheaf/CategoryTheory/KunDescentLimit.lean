/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

import Sheaf.AlgebraicGeometry.LimitAffineTransition
import Sheaf.AlgebraicGeometry.AffineEtaleSiteColimitStatement
import WeilConjectures.AlgebraicGeometry.FullAffineEtaleSite
import WeilConjectures.AlgebraicGeometry.FullAffineEtaleTopos
import Sheaf.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.CategoryTheory.ColimitSiteSections

import WeilConjectures.CategoryTheory.SiteFilteredColimitSections
import WeilConjectures.AlgebraicGeometry.FullAffineEtaleTopos
import WeilConjectures.CategoryTheory.ColimitSiteSections
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
/-!
# Descent of torsion étale sheaves along affine inverse limits

Source: Stacks Project, Tag 0EYN (via Tags 0EXJ and 0EYL)
(blueprint: lem-kun-descent-limit).

## Main definitions

* `kunDescentStageTransition`: the canonical adjoint transition between stage sheaves.
* `kunDescentPullPushTransition`: the induced transition on the limit scheme.

## Main statements

* `kun_descent_limit`: stage compatibility and the canonical colimit reconstruction.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- The canonical transition from the inverse image of the stage-i direct image to the
stage-j direct image.  It is the adjoint of the inverse direct-image composition comparison,
so no transition morphism is chosen arbitrarily.

Source: Stacks Project, Tag 0EXJ, first paragraph; Tag 0EYN, part (1)
(blueprint: lem-kun-descent-limit).
-/
noncomputable def kunDescentStageTransition
    {I : Type u} [Preorder I] (X : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone X)
    (F : Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    {i j : I} (f : i ⟶ j) :
    (Etale.upperStar AddCommGrpCat.{u + 1} (X.map f.op)).obj
        ((Etale.lowerStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj F) ⟶
      (Etale.lowerStar AddCommGrpCat.{u + 1} (c.π.app (op j))).obj F :=
  ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
    (X.map f.op)).homEquiv _ _).symm
      ((Etale.lowerStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (X.map f.op)
        (c.π.app (op i)) (c.w f.op).symm).inv.app F)

/-- The canonical transition between the pull-push sheaves on the limit.  First use
inverse-image composition, then pull back the canonical stage transition.

Source: Stacks Project, Tag 0EXJ, transition maps in the statement
(blueprint: lem-kun-descent-limit).
-/
noncomputable def kunDescentPullPushTransition
    {I : Type u} [Preorder I] (X : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone X)
    (F : Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    {i j : I} (f : i ⟶ j) :
    (Etale.upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj
        ((Etale.lowerStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj F) ⟶
      (Etale.upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).obj
        ((Etale.lowerStar AddCommGrpCat.{u + 1} (c.π.app (op j))).obj F) :=
  (Etale.upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (X.map f.op)
    (c.π.app (op i)) (c.w f.op).symm).hom.app
      ((Etale.lowerStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj F) ≫
    (Etale.upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map
      (kunDescentStageTransition X c F f)

/-- The direct images of a torsion abelian étale sheaf along an affine inverse limit form
the canonical compatible system, and the counit cocone of its pulled-back system is a
colimit cocone.  In particular its induced canonical colimit-to-sheaf map is an isomorphism.
The stage identity and composition clauses use the canonical inverse-image comparisons;
the existential diagram is indexed by the directed category `I`, not its opposite.

Source: Stacks Project, Tag 0EYN, via Tags 0EXJ and 0EYL
(blueprint: lem-kun-descent-limit).

1. Affine stages are qcqs and the projections are affine
   (`lem-weil-pbc-affine-scheme-qcqs`, `lem-weil-pbc-limit-affine-transition`).
   The affine-etale-site colimit theorem gives a coherent strict finite-cover site system
   whose colimit is the limit's affine etale site. Restricting to these sites is an
   equivalence on abelian sheaves (`lem-weil-pbc-affine-etale-site-colimit`,
   `lem-weil-pbc-affine-etale-site-topos`).
2. Direct images on an affine object are sections over its base change; these identify
   the geometric and site direct images, naturally in objects and sheaves. By their
   adjunctions the inverse images are identified too, compatibly with units and counits.
3. Define the stage transitions as the adjoints of the direct-image composition
   comparisons. The composite-adjunction counit formula proves the identity and cocycle
   clauses (`lem-cat-right-adjoint-composition`, `lem-weil-pbc-inverse-image-composition`).
   Pulling back gives a functor on `I`; the same formula makes the counits a cocone.
4. Abelian etale sheaves have small colimits
   (`lem-weil-pbc-abelian-etale-sheaves-grothendieck`), transported through the site
   equivalence by its Hom bijections. The counit cocone induces its canonical map to `F`.
5. Descend each affine etale object to a stage. The abelian section formula
   (`lem-weil-pbc-colimit-of-sites-sections`, Tag 09YN) computes sections of that colimit
   over the nonempty directed tail of later stages, with its specified unit maps.
6. On this tail every term identifies with the same group of sections of `F` and every
   transition is the identity, by the adjunction triangle identity. The induced counit
   map is likewise the identity on each term. A constant identity diagram over a
   nonempty directed tail has its value as colimit, hence this particular map is an iso.
7. The sectionwise inverses commute with restrictions, so give an inverse sheaf morphism.
   Transport back through the affine-site equivalences; the comparisons preserve the
   transitions and counits, proving that the displayed counit cocone is colimiting.
-/
theorem kun_descent_limit
    (I : Type u) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (X : Iᵒᵖ ⥤ Scheme.{u})
    (hX : ∀ i : Iᵒᵖ, IsAffine (X.obj i))
    (htransition : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (X.map f))
    (c : Cone X) (hc : IsLimit c)
    (F : Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : CategoryTheory.Sheaf.IsTorsion F) :
    (∀ i : I, kunDescentStageTransition X c F (𝟙 i) =
      eqToHom (congrArg (fun a : X.obj (op i) ⟶ X.obj (op i) ↦
        (Etale.upperStar AddCommGrpCat.{u + 1} a).obj
          ((Etale.lowerStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj F))
        (X.map_id (op i))) ≫
      (Etale.upperStarId AddCommGrpCat.{u + 1} (X.obj (op i))).hom.app
        ((Etale.lowerStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj F)) ∧
    (∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k),
      kunDescentStageTransition X c F (f ≫ g) =
        (Etale.upperStarComp AddCommGrpCat.{u + 1} (X.map g.op) (X.map f.op)
          (X.map (f ≫ g).op) (X.map_comp g.op f.op)).hom.app
            ((Etale.lowerStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj F) ≫
        (Etale.upperStar AddCommGrpCat.{u + 1} (X.map g.op)).map
          (kunDescentStageTransition X c F f) ≫ kunDescentStageTransition X c F g) ∧
    ∃ (D : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
      (e : ∀ i : I, D.obj i ≅
        (Etale.upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj
          ((Etale.lowerStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj F))
      (ι : D ⟶ (Functor.const I).obj F),
      (∀ {i j : I} (f : i ⟶ j),
        (e i).inv ≫ D.map f ≫ (e j).hom = kunDescentPullPushTransition X c F f) ∧
      (∀ i : I, ι.app i = (e i).hom ≫
        (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
          (c.π.app (op i))).counit.app F) ∧
      Nonempty (IsColimit (Cocone.mk F ι)) := by
  sorry

end AlgebraicGeometry
