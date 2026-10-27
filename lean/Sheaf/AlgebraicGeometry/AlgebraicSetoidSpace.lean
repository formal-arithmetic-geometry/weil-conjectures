/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q139
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Sheaf.AlgebraicGeometry.EtaleSmoothAtlasFppfDescent
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite

/-! # Algebraic stacks in setoids are algebraic spaces

Source: Stacks Project, Algebraic Stacks, Tag 04SZ,
proposition-algebraic-stack-no-automorphisms, (1) implies (3)
(blueprint: lem-sfb-algebraic-setoid-space).

## Main definitions

- `CategoryTheory.moduliSectionClass`: the point-to-class map induced by a based functor.

## Main statements

- `CategoryTheory.exists_algebraicSpace_of_trivial_moduli_automorphisms`: representation
  by an algebraic space and the natural point-to-class bijection.

The point-to-class map below is induced by the representing functor itself.
Naturality is expressed along arbitrary arrows over base morphisms; in a category
fibred in groupoids these arrows identify the source with the pullback of the target.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry Opposite

namespace CategoryTheory

/-- Send a section to the isomorphism class of its image under a functor over the base.
The section is the Yoneda map `h_T → P`, viewed as an object of `discreteModuli P`.
Source: Stacks, Tag 04SZ, representing equivalence and its pointwise class map;
Stacks, Tag 0432, category of elements
(blueprint: lem-sfb-algebraic-setoid-space). -/
def moduliSectionClass {S : Scheme.{u}} {P : (Over S)ᵒᵖ ⥤ Type u}
    {F : BasedCategory.{v, w} (Over S)} (e : BasedFunctor (discreteModuli P) F)
    (T : Over S) (s : P.obj (op T)) : Skeleton (Functor.Fiber F.p T) :=
  toSkeleton ⟨e.obj (CostructuredArrow.mk (yonedaEquiv.symm s)),
    e.w_obj (CostructuredArrow.mk (yonedaEquiv.symm s))⟩

/-- An algebraic stack with only identity automorphisms over every test scheme is
represented by an algebraic space. Its point-to-class map is bijective on every fibre
and commutes with restriction along every base arrow.
Source: Stacks, Tag 04SZ, proposition-algebraic-stack-no-automorphisms, (1) implies (3)
(blueprint: lem-sfb-algebraic-setoid-space).

Proof:
1. Choose a smooth surjective scheme atlas from def-sfb-algebraic-moduli-stack.
   Apply lem-sfb-etale-smooth-atlas-fppf-descent to obtain effective fppf descent
   for objects and the fppf sheaf condition for isomorphisms. No finiteness or
   separation assumption on the base is needed.
2. Any two isomorphisms between fibre objects agree: their quotient is an
   automorphism, hence the identity. Form F(T) from the isomorphism classes of
   the fibre. Pullback along a base arrow sends a class to the class of a
   cartesian lift, independently of that lift. Uniqueness up to isomorphism
   gives the presheaf identities. The class functor to the category of elements
   is fully faithful, because arrows over u are isomorphisms to u-pullbacks,
   and essentially surjective, because every class has a representative.
   Choosing representatives gives its inverse equivalence over the base.
3. This class presheaf is an fppf sheaf. Matching classes give unique overlap
   isomorphisms, whose cocycle condition follows by uniqueness. Effective
   descent from step 1 glues the objects. Locally isomorphic objects are
   globally isomorphic by the sheaf condition for isomorphisms. This also
   applies to the empty cover of the empty scheme.
4. Send the scheme atlas h_U to this class sheaf. For each section over T choose
   its representative x in the fibre. The atlas base change at x is an
   algebraic space P_x over T. On any test scheme its points are triples
   (u,t,alpha), where alpha identifies the two images in the stack. For a
   fixed pair (u,t), such alpha exists exactly when the classes agree and is
   unique by step 2. Forgetting alpha identifies P_x with the sheaf pullback
   h_U ×_F h_T, naturally and compatibly with the projection to h_T.
5. Every étale scheme chart of P_x has smooth composite to T by the atlas
   condition, hence flat and locally finitely presented by lem-pc-smooth-flat.
   The atlas projection is already surjective. Regard U as an algebraic space
   using def-trf-scheme-algebraic-space. The fppf sheaf of step 3 and these
   pullbacks satisfy lem-sfb-fppf-space-atlas-bootstrap. Thus the class sheaf
   is an algebraic space R (def-trf-algebraic-space).
6. Yoneda identifies Hom_S(T,R) with R(T), the very class sheaf of step 2.
   The inverse of its class functor gives the stated based equivalence.
   The displayed map sends s to the class of its image under that functor,
   so it is bijective. An arrow over u is a cartesian pullback identification;
   its source class is therefore the restriction of its target class. This
   proves the final naturality equation, for every base arrow and every lift. -/
theorem exists_algebraicSpace_of_trivial_moduli_automorphisms
    {S : Scheme.{u}} (F : BasedCategory.{v, w} (Over S))
    (hF : IsAlgebraicModuliStack F)
    (hauto : ∀ (T : Over S) (x : Functor.Fiber F.p T), Subsingleton (Aut x)) :
    ∃ (R : AlgebraicSpace S) (e : BasedFunctor (discreteModuli R.obj.obj) F),
      e.toFunctor.IsEquivalence ∧
      (∀ T : Over S, Function.Bijective (moduliSectionClass e T)) ∧
      ∀ (T T' : Over S) (u : T' ⟶ T) (s : R.obj.obj.obj (op T))
        (x : Functor.Fiber F.p T) (y : Functor.Fiber F.p T') (a : y.val ⟶ x.val),
        F.p.IsHomLift u a → moduliSectionClass e T s = toSkeleton x →
          moduliSectionClass e T' (R.obj.obj.map u.op s) = toSkeleton y := by
  sorry

end CategoryTheory
