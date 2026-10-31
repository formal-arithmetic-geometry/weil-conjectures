/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleObjects
public import WeilConjectures.AlgebraicGeometry.Sites.ProetaleToposFunctoriality
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Finite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Finite

/-! # Exact finite direct image on the small pro-étale site

Source: blueprint slopmaster2-20261029-2300, sec-six-functors-basics/
sk-thm-sfb-qlbar-two-colimit, node lem-fd-proetale-finite-pushforward-exact, order 2287,
clauses (1)--(2); Bhatt--Scholze,
The pro-étale topology for schemes, Lemma 6.1.17; Stacks Project, Tag 09A8
(blueprint: lem-fd-proetale-finite-pushforward-exact).

The invertible natural transformation is the canonical unit from termwise direct image
on the homotopy category to the total right derived functor. Thus its assertion includes
all unbounded complexes and specifies the comparison, rather than an arbitrary isomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A finite, finitely presented morphism has exact direct image for sheaves valued in
modules over any ring, and for module objects over any commutative condensed ring.
The canonical comparison with total right derived direct image is invertible on all
unbounded complexes, and all positive higher direct images of modules vanish.

Source: blueprint slopmaster2-20261029-2300, node lem-fd-proetale-finite-pushforward-exact,
order 2287, clauses (1)--(2);
Bhatt--Scholze, Lemma 6.1.17; Stacks Project, Tag 09A8
(blueprint: lem-fd-proetale-finite-pushforward-exact).

Proof plan:
1. Apply lem-zl-finite-fp-proetale-pushforward-exact to the underlying abelian sheaves.
   Its weakly contractible affine basis argument applies because finite presentation
   implies local finite presentation. Direct image evaluates at base change, as in
   def-sfb-finite-lower-star.
2. Forget the action of an arbitrary ring R. The kernel and sheafified cokernel of
   def-weil-sheaf-of-modules-category detect exactness on underlying abelian sheaves,
   and forgetting the action commutes with direct image. Apply step 1 and detect
   exactness again on Y. This includes noncommutative and zero rings.
3. For condensed coefficients, def-sfb-module-lower-star identifies the underlying
   abelian sheaf of direct image with the abelian direct image. The faithful exact
   forgetful functor of det-prop-sfb-module-category detects exact sequences through
   its underlying kernels and cokernels. Step 1 therefore proves module-object exactness.
4. By lem-weil-pbc-exact-functor-derived-factorization the exact functor descends
   termwise to the unbounded derived category. Lemma
   lem-weil-pbc-exact-functor-derived-functor makes its canonical right-derived unit
   invertible. This is the total derivation of the same composite from
   det-def-sfb-module-derived-pushpull. Equivalently, applying direct image to a
   K-injective resolution preserves its quasi-isomorphism, by
   lem-weil-pbc-exact-functor-complex-cohomology. For M in degree zero, the termwise
   image is again concentrated in degree zero, so its positive cohomology is zero.

A finite morphism is affine, hence quasi-compact and quasi-separated; consequently
`IsFinite f` together with `LocallyOfFinitePresentation f` is exactly the stated finite
and finite-presentation hypothesis. The derived unit below has components
`f_* K ⟶ Rf_* K` for every homotopy complex K; its inverse is the asserted comparison.
-/
theorem finitePushforward_exact {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [LocallyOfFinitePresentation f] :
    (∀ (R : Type (u + 1)) [Ring R],
      PreservesFiniteLimits (lowerStar (ModuleCat.{u + 1} R) f) ∧
        PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} R) f)) ∧
    ∀ (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      [MonObj Λ] [IsCommMonObj Λ],
      PreservesFiniteLimits (CondensedRing.lowerStar Λ f) ∧
      PreservesFiniteColimits (CondensedRing.lowerStar Λ f) ∧
      IsIso (CondensedRing.lowerStar Λ f).rightDerivedFunctorUnit ∧
      ∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X)) (q : ℤ), 0 < q →
        IsZero ((DerivedCategory.homologyFunctor
          (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) q).obj
          ((CondensedRing.moduleObjectDerivedPushforward Λ f).obj
            ((DerivedCategory.singleFunctor
              (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
                (condensedRingObj Λ X)) 0).obj M))) := by
  constructor
  · intro R _
    constructor
    · infer_instance
    · exact AlgebraicGeometry.ProEtale.preservesFiniteColimits_lowerStar_of_isFinite R f
  · intro Λ _ _
    have hcol : PreservesFiniteColimits (CondensedRing.lowerStar Λ f) :=
      AlgebraicGeometry.ProEtale.CondensedRing.preservesFiniteColimits_lowerStar_of_isFinite Λ f
    constructor
    · infer_instance
    constructor
    · infer_instance
    constructor
    · exact @Functor.isIso_rightDerivedFunctorUnit _ _ _ _ _ _ _ _ _
        (CondensedRing.lowerStar Λ f) _ _ hcol
    · intro M q hq
      let F := AlgebraicGeometry.ProEtale.CondensedRing.lowerStar Λ f
      have hz : IsZero ((DerivedCategory.homologyFunctor
          (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
            (condensedRingObj Λ Y)) q).obj
          ((DerivedCategory.singleFunctor
            (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
              (condensedRingObj Λ Y)) 0).obj (F.obj M))) := by
        exact DerivedCategory.isZero_of_isLE _ 0 q hq
      exact IsZero.of_iso hz ((DerivedCategory.homologyFunctor
        (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
          (condensedRingObj Λ Y)) q).mapIso
        ((@Functor.singleFunctorCompRightDerivedFunctorIso _ _ _ _ _ _ _ _ _ F _ _ hcol).app M))

end AlgebraicGeometry.ProEtale
