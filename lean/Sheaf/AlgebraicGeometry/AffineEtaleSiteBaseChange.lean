/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.FullAffineEtaleTopos
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageExact
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

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
  sorry

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

/--
Source: Stacks Project, Étale Cohomology, Lemma 0EYL, and Topologies,
Lemma 04HR; Sites 00WV, 00WX, 00X1; Étale Cohomology 03Q1(2)
(blueprint: lem-weil-pbc-affine-etale-site-base-change).

Proof:
1. Restrict ordinary étale base change to affine objects using
   lem-weil-pbc-etale-base-change-finite-limits(1) and
   lem-weil-pbc-affine-morphism-permanence(1),(2), as in the definition above.
2. Finite jointly surjective étale covering families remain such after base change
   (lem-weil-pbc-etale-covering-base-change). Their domains are affine by step 1.
   A pullback of affine objects over an affine object is affine: its projection is
   affine by pqf-def-affine-morphism and lem-weil-pbc-affine-morphism-permanence.
   It is étale, and the canonical base-change comparison is an isomorphism, by
   lem-weil-pbc-etale-base-change-finite-limits(2),(3). This proves both covering
   continuity conditions of def-weil-pbc-sites-and-cohomology(3).
3. Precomposition preserves sheaves. The sheafified presheaf left Kan extension
   is left adjoint to it (lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction).
4. Restriction from full small étale sites to the affine sites is an equivalence
   (lem-weil-pbc-affine-etale-site-topos). Full-site direct image and affine-site
   direct image agree under restriction: both evaluate a sheaf at `V ×_T T'`, with
   the same restriction maps (lem-weil-pbc-etale-base-change-continuous(3)).
   Uniqueness of left adjoints therefore identifies affine inverse image with
   full-site inverse image conjugated by these restriction equivalences.
   Full-site inverse image preserves finite limits and colimits
   (lem-weil-pbc-sets-etale-inverse-image-exact), as do equivalences and their
   quasi-inverses. Thus the affine inverse image is exact, giving the morphism
   of sites of def-weil-pbc-sites-and-cohomology(3).
-/
theorem affineEtaleSiteBaseChange {T T' : Scheme.{u}} (h : T' ⟶ T)
    [IsAffineHom h] :
    (∀ (X : T.FullAffineEtale) (R : Presieve X),
      R ∈ Scheme.fullAffineEtalePrecoverage T X →
        R.map (Scheme.affineEtaleBaseChange h) ∈ Scheme.fullAffineEtalePrecoverage T'
          ((Scheme.affineEtaleBaseChange h).obj X)) ∧
    (∀ (X Y Z : T.FullAffineEtale) (R : Presieve X),
      R ∈ Scheme.fullAffineEtalePrecoverage T X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (Scheme.affineEtaleBaseChange h)) ∧
    ∃ (hu : (Scheme.affineEtaleBaseChange h).IsContinuous (Scheme.fullAffineEtaleTopology T)
        (Scheme.fullAffineEtaleTopology T')),
      Nonempty
        (Functor.sheafPullbackConstruction.sheafPullback (Scheme.affineEtaleBaseChange h)
          (Type (u + 1))
          (Scheme.fullAffineEtaleTopology T) (Scheme.fullAffineEtaleTopology T') ⊣
          (Scheme.affineEtaleBaseChange h).sheafPushforwardContinuous (Type (u + 1))
            (Scheme.fullAffineEtaleTopology T) (Scheme.fullAffineEtaleTopology T')) ∧
      (PreservesFiniteLimits
        (Functor.sheafPullbackConstruction.sheafPullback (Scheme.affineEtaleBaseChange h)
          (Type (u + 1))
          (Scheme.fullAffineEtaleTopology T) (Scheme.fullAffineEtaleTopology T'))) ∧
      (PreservesFiniteColimits
        (Functor.sheafPullbackConstruction.sheafPullback (Scheme.affineEtaleBaseChange h)
          (Type (u + 1))
          (Scheme.fullAffineEtaleTopology T) (Scheme.fullAffineEtaleTopology T'))) := by
  sorry

end AlgebraicGeometry
