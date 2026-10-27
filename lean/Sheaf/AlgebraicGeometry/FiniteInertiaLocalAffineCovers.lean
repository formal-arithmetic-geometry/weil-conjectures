/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q120
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.ModuliInertia
public import Sheaf.AlgebraicGeometry.FiniteStackSchemeTests
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.ModuliChartNormalization
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.DmStabilizerIsomorphismOpenLocus
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Mathlib.RingTheory.Ideal.Operations

/-! # Stabilizer-preserving étale local finite flat affine covers

Source: Stacks Project, stacks-more-morphisms.tex, Tag 0DUE,
lemma-etale-local-finite-inertia, restricted to Deligne--Mumford stacks;
criteria.tex, Tag 076V; stacks-morphisms.tex, Tag 06N3
(blueprint: lem-sfb-finite-inertia-local-affine-covers).

The finite flat affine cover and the proper relative diagonal are expressed by
scheme tests of the actual projections. Stabilizers are tested on every scheme
fibre, so their bijections express isomorphisms of automorphism sheaves, not just
bijections at geometric points. Equivalently, the canonical inertia comparison
is an equivalence over the base.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- A DM stack with finite inertia has a set-indexed, jointly surjective family
of representable separated étale stabilizer-preserving maps from DM stacks with
finite flat affine covers.
Source: Stacks Project, Tag 0DUE, lemma-etale-local-finite-inertia, restricted to DM
stacks, with Tags 076V and 06N3 for the étale-topology and DM conventions
(blueprint: lem-sfb-finite-inertia-local-affine-covers).

Proof:
1. For each point `x`, lem-sfb-dm-pointed-finite-groupoid-neighbourhood supplies
   a representable étale `Q = [U/R] -> X` and `q` above `x`, preserving the
   stabilizer at `q`. The affine groupoid has finite locally free projections.
2. By lem-sfb-dm-stabilizer-isomorphism-open-locus, finite target inertia gives
   an open `V` containing `q` where the inertia comparison is an isomorphism.
   By lem-sfb-finite-flat-groupoid-quotient-open-geometry its inverse image in
   `U` is invariant. Lift `q` to a point `v` in that open. Its orbit is finite,
   contains `v`, and stays in the open: use def-pc-finite-locally-free and
   invariance to check both endpoints of every arrow in the orbit.
3. Write `U = Spec A`. If `J` cuts out the complement of the invariant open,
   lem-weil-pbc-prime-avoidance gives `a` in `J` outside every orbit prime.
   Thus the finite orbit lies in the affine principal open `D(a)` inside `V`.
   Apply lem-sfb-locally-free-groupoid-invariant-affine to the restricted
   groupoid and this affine neighbourhood, obtaining an invariant affine `W`.
4. The open `W` remains invariant in `U`. By
   lem-sfb-finite-flat-groupoid-quotient-open-geometry its quotient is an open
   substack of `V`, contains `q`, has the finite flat affine cover `W`, and is
   absolutely separated. Restrict the étale atlas to see it is DM. Restrict the
   map to `X` using lem-sfb-stack-chartwise-smooth-etale-calculus.
5. By lem-sfb-stack-separated-source-separated-inertia-target, absolute
   separatedness of this quotient and finite target inertia make its map to
   `X` separated. Fullness of the open substack restricts the stabilizer
   isomorphism from step 2, giving bijections on automorphisms on every test
   scheme, including nonreduced ones. Naturality gives the automorphism-sheaf
   isomorphism, equivalently the canonical inertia-comparison isomorphism.
6. Choose one such neighbourhood for every point, using
   def-weil-size-convention. These maps jointly cover by construction. The
   point set is in `Type (max (u+1) w)`. The quotient presentations can be taken
   in the displayed universes, which include schemes and the target category.
   When the point set is empty, choose the empty family. -/
theorem exists_finite_inertia_local_affine_covers
    {S : Scheme.{u}} (X : BasedCategory.{v, w} (Over S))
    (hX : IsDeligneMumfordModuliStack X)
    (hfinite : IsRepresentableFiniteModuliMap (moduliInertiaProjection X)) :
    ∃ (I : Type (max (u + 1) w))
      (A : I → BasedCategory.{max u v, max (u + 1) w} (Over S))
      (g : ∀ i : I, BasedFunctor (A i) X),
      (∀ i : I, IsDeligneMumfordModuliStack (A i) ∧
        IsRepresentableByAlgebraicSpaces (g i) ∧ IsEtaleModuliMap (g i) ∧
        (∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) X)
          (Z : AlgebraicSpace S) (a : Z.obj.obj ⟶ yoneda.obj T),
          HasSpaceBaseChange (g i) T t Z a →
            AlgebraicSpace.IsRepresentableWith (fun _ _ f ↦ IsProper f.left)
              (pullback.diagonal a)) ∧
        (∃ (U : Over S) (_ : IsAffine U.left)
          (p : BasedFunctor (discreteModuli (yoneda.obj U)) (A i)),
          ModuliSchemeTest (fun _ _ f ↦
            IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f ∧ Surjective f) p) ∧
        (∀ (T : Over S) (x : Functor.Fiber (A i).p T),
          Function.Bijective (fun α : x ≅ x ↦ (moduliFiberMap (g i) T).mapIso α))) ∧
      ∀ x : ModuliPoints X, ∃ (i : I) (y : ModuliPoints (A i)),
        moduliPointMap (g i) y = x := by
  sorry

end CategoryTheory
