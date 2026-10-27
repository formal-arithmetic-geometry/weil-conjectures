/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import Sheaf.AlgebraicGeometry.SpaceGroupoidQuotientPresentation
public import Sheaf.AlgebraicGeometry.ModuliChartNormalization
public import Sheaf.CategoryTheory.GroupoidStackificationLocalDescription

/-! # Cartesian source squares and quotient stacks

Source: Stacks Project, spaces-groupoids.tex, Tag 04ZN
(blueprint: lem-sfb-groupoid-source-cartesian-quotient-square).

The quotient stacks are specified by their existing local presentation interface.
The comparison with the maps from the object spaces is required to intertwine the
original arrow maps. Thus the specified stack map is the map induced by the groupoid
morphism, including its comparison on the object charts.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A cartesian source square of algebraic-space groupoids gives a 2-cartesian square
of their object spaces and fppf quotient stacks. The conclusion uses the actual
comparison functor, whose projection to `V` is the given object map `f₀`.

Source: Stacks Project, spaces-groupoids.tex, Tag 04ZN and
lemma-quotient-stack-functorial
(blueprint: lem-sfb-groupoid-source-cartesian-quotient-square).

Proof:
1. Put B = V ×_[V/Q] [U/R]. Its objects are triples (v,x,alpha), with alpha an
isomorphism b(v) -> F(x). Glue the V-component using the sheaf axiom, the x-component
using descent in [U/R], and alpha using the isomorphism sheaf in [V/Q]. Arrows glue
uniquely, so B is an fppf stack, including for empty covering sieves. The canonical
comparison sends u to (f₀(u),a(u),theta(u)). These constructions commute with pullback.
2. For two chart objects, arrows in the quotient are exactly sections of R with the
specified endpoints: these endpoint presheaves are sheaves because R and U are
sheaves. The analogous assertion holds for Q and V. This is the arrow-sheafification
clause of lem-sfb-groupoid-stackification-local-description, since sheafification
fixes sheaves (def-weil-pbc-sheafification). The presentation interface records these
identifications and their composition and pullback compatibility.
3. The cartesian source square gives a unique lift in R of a Q-arrow with a prescribed
source in U. An arrow between two comparison images must lie over an identity in V.
Its R-section therefore lifts the same Q-arrow with the same source as the identity
section. Uniqueness forces it to be that identity, and its target to equal its source.
The discrete source U thus maps fully faithfully to B, including empty arrow sets.
4. For (v,x,alpha), locally choose u and theta':a(u) -> x by the local-image clause of
lem-sfb-groupoid-stackification-local-description. The arrow F(theta')⁻¹ alpha is a
Q-section from v to f₀(u), after inserting the specified chart comparison. Lift its
inverse with source u to r:u -> z. Then f₀(z)=v and theta' a(r)⁻¹ identifies the
comparison image of z with (v,x,alpha). The arrow-intertwining hypothesis gives its
required comparison equation. Thus every object of B is locally in the image.
5. U is an fppf stack as a discrete sheaf. Apply
lem-sfb-stack-fully-faithful-local-equivalence to Steps 1, 3 and 4 to get an equivalence
over the site. Its projection to V is f₀, so it is the claimed equivalence over V.
The existing moduliTwoFiberProduct and moduliTwoFiberLift definitions identify this
with the asserted 2-fibre-product square. -/
theorem groupoid_source_cartesian_quotient_square
    {S : Scheme.{u}} {U R V Q : AlgebraicSpace S}
    (s t : R.obj.obj ⟶ U.obj.obj) (e : U.obj.obj ⟶ R.obj.obj)
    (j : R.obj.obj ⟶ R.obj.obj) (c : Limits.pullback s t ⟶ R.obj.obj)
    (s' t' : Q.obj.obj ⟶ V.obj.obj) (e' : V.obj.obj ⟶ Q.obj.obj)
    (j' : Q.obj.obj ⟶ Q.obj.obj) (c' : Limits.pullback s' t' ⟶ Q.obj.obj)
    (A : BasedCategory.{v₁, w₁} (Over S)) (D : BasedCategory.{v₂, w₂} (Over S))
    (a : BasedFunctor (discreteModuli U.obj.obj) A)
    (b : BasedFunctor (discreteModuli V.obj.obj) D)
    (pU : SpaceGroupoidQuotientPresentation s t e j c A a)
    (pV : SpaceGroupoidQuotientPresentation s' t' e' j' c' D b)
    (f₀ : U ⟶ V) (f₁ : R ⟶ Q)
    (hs : s ≫ f₀.hom.hom = f₁.hom.hom ≫ s')
    (ht : t ≫ f₀.hom.hom = f₁.hom.hom ≫ t')
    (he : e ≫ f₁.hom.hom = f₀.hom.hom ≫ e')
    (hj : j ≫ f₁.hom.hom = f₁.hom.hom ≫ j')
    (hc : ∀ (T : Over S) (p : yoneda.obj T ⟶ Limits.pullback s t)
      (q : yoneda.obj T ⟶ Limits.pullback s' t'),
      q ≫ pullback.fst s' t' = p ≫ pullback.fst s t ≫ f₁.hom.hom →
      q ≫ pullback.snd s' t' = p ≫ pullback.snd s t ≫ f₁.hom.hom →
      p ≫ c ≫ f₁.hom.hom = q ≫ c')
    (F : BasedFunctor A D)
    (θ : ((discreteModuliMap f₀.hom.hom).comp b) ≅ a.comp F)
    (hθ : ∀ (T : Over S) (x y : yoneda.obj T ⟶ U.obj.obj)
      (r : {r : yoneda.obj T ⟶ R.obj.obj // r ≫ s = x ∧ r ≫ t = y})
      (q : {q : yoneda.obj T ⟶ Q.obj.obj //
        q ≫ s' = x ≫ f₀.hom.hom ∧ q ≫ t' = y ≫ f₀.hom.hom}),
      q.val = r.val ≫ f₁.hom.hom →
        θ.hom.toNatTrans.app (CostructuredArrow.mk x) ≫
            F.map (spaceGroupoidPresentationArrow s t a pU.arrows x y r) =
          spaceGroupoidPresentationArrow s' t' b pV.arrows
              (x ≫ f₀.hom.hom) (y ≫ f₀.hom.hom) q ≫
            θ.hom.toNatTrans.app (CostructuredArrow.mk y))
    (hcart : IsPullback s f₁.hom.hom f₀.hom.hom s') :
    (moduliTwoFiberLift (discreteModuliMap f₀.hom.hom) a θ).toFunctor.IsEquivalence := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
