/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Exact inverse image on abelian sheaves

Source: Stacks Project, Modules on Sites, Lemma 04JC, first assertion;
Sites, Definition 00X1 and Section 00YR; Modules on Sites, Lemma 03DC
(blueprint: lem-weil-pbc-site-pullback-abelian-exact).
-/

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- Source: Stacks Project, Lemma 04JC (first assertion), Definition 00X1,
Section 00YR and Lemma 03DC (blueprint: lem-weil-pbc-site-pullback-abelian-exact).

The precoverage instances encode sites, and `hcover` and `hpullback` encode the two
Stacks continuity conditions. The `IsContinuous` instance is their consequence and
makes the inverse-image construction typeable. The set-valued preservation hypotheses
are precisely the exactness required of a morphism of sites. Inverse image is the
left Kan extension followed by sheafification, left adjoint to continuous pushforward.

Proof:
1. By def-weil-pbc-sites-and-cohomology (3), the set-valued inverse image is exact
   and both set-valued and abelian inverse images are left adjoint to pushforward
   (lem-weil-pbc-site-continuous-pushforward-sheaf and
   lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction).
2. Identify abelian sheaves with abelian group objects
   (lem-weil-pbc-sheaf-algebraic-structures-objects). Lift the set-valued adjunction
   using lem-weil-pbc-adjunction-lifts-group-ring-objects. Its right adjoint is
   sectionwise precomposition, hence abelian pushforward. Uniqueness of left adjoints
   (lem-weil-pbc-conjugate-iso-unit-equation) identifies the lifted left adjoint with
   abelian inverse image, compatibly with the underlying sheaves of sets.
3. Abelian-sheaf limits are sectionwise (lem-weil-pbc-sheafification-exact).
   Underlying sets detect these limits (lem-weil-pbc-site-sheaf-sets-limits-sectionwise).
   Therefore the finite-limit preservation on sets gives finite-limit preservation
   on abelian sheaves.
4. The abelian adjunction gives preservation of colimits, in particular finite
   colimits (lem-weil-pbc-left-adjoint-preserves-colimits). The abelian categories
   have these colimits (lem-weil-pbc-site-sheaves-enough-injectives).
5. Addition of morphisms is addition on the target composed with the pairing of
   the two morphisms. The lifted functor preserves this formula, by its product
   comparison and transported group law, so inverse image is additive.
6. Kernels and cokernels are equalizers and coequalizers with zero. Additivity and
   steps 3 and 4 preserve them, hence preserve short exact sequences. Exactness of
   an adjacent pair means its image-to-kernel comparison is an isomorphism; image
   is the kernel of the cokernel, so this comparison is preserved. Applying this
   to every adjacent pair preserves any finite or infinite exact sequence.

The final universal clause expresses exactness at an arbitrary place of a sequence;
there is no restriction on the number of places. Kernel and cokernel preservation
are included in the finite-limit and finite-colimit clauses, respectively. -/
theorem sitePullback_abelian_exact
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : Precoverage C) (K : Precoverage D)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [K.HasIsos] [K.IsStableUnderComposition] [K.IsStableUnderBaseChange] [K.HasPullbacks]
    (U : C ⥤ D)
    (hcover : ∀ (X : C) (R : Presieve X), R ∈ J X → R.map U ∈ K (U.obj X))
    (hpullback : ∀ (X Y Z : C) (R : Presieve X), R ∈ J X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) U)
    [U.IsContinuous J.toGrothendieck K.toGrothendieck]
    [PreservesFiniteLimits (sheafPullback U (Type u) J.toGrothendieck K.toGrothendieck)]
    [PreservesFiniteColimits (sheafPullback U (Type u) J.toGrothendieck K.toGrothendieck)] :
    ∃ (_ : (sheafPullback U AddCommGrpCat.{u} J.toGrothendieck K.toGrothendieck).Additive),
      PreservesFiniteLimits
        (sheafPullback U AddCommGrpCat.{u} J.toGrothendieck K.toGrothendieck) ∧
      PreservesFiniteColimits
        (sheafPullback U AddCommGrpCat.{u} J.toGrothendieck K.toGrothendieck) ∧
      (∀ S : ShortComplex (Sheaf J.toGrothendieck AddCommGrpCat.{u}),
        S.ShortExact →
          (S.map (sheafPullback U AddCommGrpCat.{u}
            J.toGrothendieck K.toGrothendieck)).ShortExact) ∧
      (∀ S : ShortComplex (Sheaf J.toGrothendieck AddCommGrpCat.{u}),
        S.Exact →
          (S.map (sheafPullback U AddCommGrpCat.{u}
            J.toGrothendieck K.toGrothendieck)).Exact) := by
  sorry

end CategoryTheory
