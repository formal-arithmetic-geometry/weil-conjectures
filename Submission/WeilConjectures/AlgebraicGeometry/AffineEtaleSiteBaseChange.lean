/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.FullAffineEtaleTopos
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Submission.WeilConjectures.AlgebraicGeometry.EtaleSheaves
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
import Submission.WeilConjectures.CategoryTheory.InverseMateEquivalence
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Base change on the full affine étale sites

Source: Stacks Project, Étale Cohomology, Lemma 0EYL and Topologies, Lemma 04HR
(blueprint: lem-weil-pbc-affine-etale-site-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

namespace Scheme

/-- Source: Stacks Project, Étale Cohomology 0EYL, and Topologies 04HR
(blueprint: lem-weil-pbc-affine-etale-site-base-change).
Proof (step 1): the projection to `U` is a base change of the affine morphism `h`,
so it is affine by lem-weil-pbc-affine-morphism-permanence(1). Its target is affine,
so its source is affine by part (2) of that node. Étaleness of the structure map is
already supplied by lem-weil-pbc-etale-base-change-finite-limits(1). -/
theorem affineEtaleBaseChange_isAffine {T T' : Scheme.{u}} (h : T' ⟶ T)
    [IsAffineHom h] (U : T.FullAffineEtale) :
    IsAffine (((MorphismProperty.Over.pullback @Etale ⊤ h).obj
      ((fullAffineEtaleInclusion T).obj U)).left) := by
  let : IsAffine ((𝟭 Scheme).obj U.obj.left) := U.property
  change IsAffine (pullback U.obj.hom h)
  exact AlgebraicGeometry.instIsAffinePullbackSchemeOfIsAffineHom_1 U.obj.hom h

/-- Source: Stacks Project, Étale Cohomology 0EYL, and Topologies 04HR
(blueprint: lem-weil-pbc-affine-etale-site-base-change).
The ordinary étale base-change functor restricted to the full affine subcategories.
Its objects are `U ×_T T' → T'`; its arrows are the ordinary base-change arrows. -/
noncomputable def affineEtaleBaseChange {T T' : Scheme.{u}} (h : T' ⟶ T)
    [IsAffineHom h] : T.FullAffineEtale ⥤ T'.FullAffineEtale :=
  ObjectProperty.lift (fun U : T'.Etale ↦ IsAffine U.left)
    (Scheme.fullAffineEtaleInclusion T ⋙ MorphismProperty.Over.pullback @Etale ⊤ h)
    (affineEtaleBaseChange_isAffine h)

end Scheme

-- The existential continuity witness is used only through instance synthesis.
end AlgebraicGeometry
