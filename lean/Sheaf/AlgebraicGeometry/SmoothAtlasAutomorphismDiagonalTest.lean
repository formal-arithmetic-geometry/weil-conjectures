/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import Sheaf.AlgebraicGeometry.ModuliInertia
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus

/-! # Testing an unramified diagonal on atlas automorphisms

Source: Stacks Project, stacks-morphisms.tex, Tags 0CL0(4) and 050Q;
stacks-properties.tex, Tag 04XD; spaces-descent.tex, Tag 042A
(blueprint: lem-sfb-smooth-atlas-automorphism-diagonal-test).

The automorphism space is the pullback of the actual inertia projection to the atlas,
with its specified projection to that scheme. By Tag 050Q this presents exactly the
functor of automorphisms of the atlas object on schemes over the atlas.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- An algebraic stack has unramified relative diagonal if and only if the
space of automorphisms of a smooth surjective scheme atlas is unramified over the atlas.
The hypothesis `hG` identifies `G` over `P` with the inertia pullback, hence with the
sheaf of automorphisms of the atlas object, including over nonreduced test schemes.
Source: Stacks Project, stacks-morphisms.tex, Tags 0CL0(4), 050Q and 04XR;
spaces-groupoids.tex, Tag 0DSK(1); spaces-descent.tex, Tag 042A
(blueprint: lem-sfb-smooth-atlas-automorphism-diagonal-test).

Proof:
1. For objects a,b over a scheme T, the diagonal pullback is Isom_T(a,b).
   On triples (z,alpha:z~a,beta:z~b), send the triple to beta alpha^{-1};
   the inverse sends phi to (a,1,phi). The arrow alpha gives the compatible
   isomorphism back. All formulas commute with pullback. For a=b=p this is G,
   by Tag 050Q and hG. Thus an unramified diagonal implies G -> P unramified.
2. Conversely assume G -> P unramified. For arbitrary T,a,b, put I=Isom_T(a,b)
   and H=Aut_T(b). Both spaces are locally of finite type over T, and composition
   makes H a group space, by lem-sfb-stack-isom-space-locally-finite-type.
3. Form W=T x_{b,F,p} P. Representability of the diagonal makes W a space;
   its projection q:W->T is smooth surjective by base change of the atlas,
   using lem-sfb-stack-chartwise-smooth-etale-calculus. The field-extension
   lifting convention agrees with chartwise surjectivity. Smoothness gives
   flatness and local finite presentation, as required for unramified descent.
4. The tautological theta:b_T~p_P on W identifies W x_T H with W x_P G:
   h maps to theta h theta^{-1}, with inverse g maps to theta^{-1} g theta.
   Composition and inversion commute with all scheme pullbacks, so these are
   inverse morphisms of spaces over W, not a choice of a global lift of b.
5. Base-change permanence makes W x_P G -> W unramified, hence W x_T H -> W
   unramified (lem-sfb-space-unramified-permanence). Descend along q by
   lem-sfb-stack-representable-unramified-descent to get H -> T unramified.
6. Composition gives the H-action on I. The map (h,phi) maps to (h phi,phi)
   from H x_T I to I x_T I, with inverse (psi,phi) maps to (psi phi^{-1},phi).
   The formulas respect pullback and are inverse. Thus I is a pseudo H-torsor;
   no nonempty-fibre or local-isomorphism assumption on a,b is used.
7. Apply lem-sfb-unramified-pseudo-torsor with the local finite type assertions
   from step 2, unramified H from step 5 and the pseudo-torsor isomorphism from
   step 6. Then I -> T is unramified. Since T,a,b were arbitrary, step 1 gives
   unramifiedness of the diagonal, with the two projections retained as in
   HasUnramifiedModuliDiagonal. -/
theorem unramifiedModuliDiagonal_iff_smoothAtlas_automorphismSpace {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsAlgebraicModuliStack F)
    (P : Over S) (p : BasedFunctor (discreteModuli (yoneda.obj P)) F)
    (hp : IsSmoothModuliAtlas F P p)
    (G : AlgebraicSpace S) (π : G.obj.obj ⟶ yoneda.obj P)
    (hG : HasSpaceBaseChange (moduliInertiaProjection F) P p G π) :
    HasUnramifiedModuliDiagonal F ↔ SpaceMapIsUnramified G P π := by
  sorry

end CategoryTheory
