/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O4
-/
module

public import Sheaf.AlgebraicGeometry.SpaceGroupoidQuotientPresentation
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.CategoryTheory.GroupoidStackificationLocalDescription

import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.AlgebraicStackFibreProducts
import Sheaf.AlgebraicGeometry.AlgebraicStackSetoidSpace
import Sheaf.AlgebraicGeometry.EtaleSmoothAtlasFppfDescent
import Mathlib.CategoryTheory.Sites.Sheafification

/-! # The quotient of a self-relation embeds in its target stack

Source: Stacks Project, algebraic.tex, Tags 04T4 and 04Y5
(blueprint: lem-sfb-self-relation-quotient-embedding).

The algebraic space R is specified by its points: its arrows with endpoints x,y
are exactly the vertical isomorphisms a(x) -> a(y). Thus it represents the actual
2-fibre product, rather than an arbitrary relation on U. Its composition is fixed
by composition of these isomorphisms. The quotient is any fppf quotient presentation
of this groupoid; algebraicity of that quotient is needed only for representability.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- The self-relation is an algebraic-space groupoid, and its fppf quotient maps
fully faithfully to the original algebraic stack. If the quotient is algebraic,
this map is representable by algebraic spaces.

Source: Stacks Project, algebraic.tex, Tag 04T4, parts (1), (4), (5), (6), and
Tag 04Y5, implication (2) to (3)
(blueprint: lem-sfb-self-relation-quotient-embedding).

The unique-arrow clause identifies R(T) with triples (x,y,alpha), with alpha an
isomorphism in X(T). Its natural comparison eta records alpha itself. The
composition equation specifies c(q,r) = q after r; identities and inverses are
then forced by this equation, the groupoid laws, and the unique-arrow clause.
The last compatibility equation says that the induced quotient map sends these
arrows to alpha, under the specified comparison theta : i q isomorphic to a.
Full faithfulness is stated as bijectivity on every fibre hom set.

Proof:
1. By lem-sfb-stack-diagonal-space-source-representability, a map from U to X
   is representable by algebraic spaces. Applying
   lem-sfb-representable-pullback-over-space gives R = U times_X U. Its
   points are triples (x,y,alpha) by def-sfb-stable-pointed-moduli-groupoids.
   Set s=x, t=y, e(x)=(x,x,1), j(x,y,alpha)=(y,x,alpha inverse), and compose
   consecutive arrows by composition in X. These formulas commute with
   pullback. The groupoid laws are the laws in X, and eta is the tautological
   isomorphism. This gives the unique-arrow and composition clauses below.
2. The groupoid prestack maps to X by x -> a(x), alpha -> alpha.
   lem-sfb-groupoid-stackification-local-description extends this functor to
   its fppf stackification, with the indicated invertible comparison theta.
   SpaceGroupoidQuotientPresentation retains precisely this stackification's
   local representatives and arrow sheaves. The algebraic-stack convention
   uses etale descent; lem-sfb-etale-smooth-atlas-fppf-descent supplies fppf
   descent for X without any extra hypothesis.
3. For original objects, the arrow presheaf is the isomorphism sheaf in X,
   hence is already an fppf sheaf. The arrow-sheafification clause of
   lem-sfb-groupoid-stackification-local-description and the universal
   property def-weil-pbc-sheafification identify it unchanged with the
   quotient's arrow sheaf. This proves the required bijections on original
   objects, compatibly with theta and eta.
4. For arbitrary quotient objects choose a common fppf covering where both
   have original representatives. Conjugate by the local isomorphisms and
   use step 3. An arrow in X lifts uniquely locally. These lifts agree on
   overlaps by local injectivity and glue by the quotient's morphism sheaf
   condition. This proves global surjectivity and injectivity on fibre arrows.
5. Only now suppose the quotient algebraic. Its base change by a scheme
   mapping to X is algebraic by lem-sfb-algebraic-stack-fibre-products;
   the scheme is an algebraic stack by def-trf-scheme-algebraic-space.
   Its objects are (b,phi:x isomorphic to i(b)). An arrow between two such
   pairs is unique by full faithfulness of i. Therefore its fibres are
   setoids. lem-sfb-algebraic-stack-setoid-space represents it by an
   algebraic space. This is the defining scheme test for representability.
-/
theorem self_relation_quotient_embedding {S : Scheme.{u}}
    (X : BasedCategory.{v₁, w₁} (Over S)) (hX : IsAlgebraicModuliStack X)
    (U : AlgebraicSpace S) (a : BasedFunctor (discreteModuli U.obj.obj) X) :
    ∃ (R : AlgebraicSpace S) (s t : R.obj.obj ⟶ U.obj.obj)
      (e : U.obj.obj ⟶ R.obj.obj) (j : R.obj.obj ⟶ R.obj.obj)
      (c : pullback s t ⟶ R.obj.obj)
      (η : ModuliTwoIso ((discreteModuliMap s).comp a)
        ((discreteModuliMap t).comp a)),
      AlgebraicSpace.IsPresheafGroupoid s t e j c ∧
      (∀ (T : Over S) (x y : yoneda.obj T ⟶ U.obj.obj)
        (β : a.obj (CostructuredArrow.mk x) ⟶ a.obj (CostructuredArrow.mk y)),
        X.p.IsHomLift (𝟙 T) β →
          ∃! r : {r : yoneda.obj T ⟶ R.obj.obj // r ≫ s = x ∧ r ≫ t = y},
            spaceGroupoidPresentationArrow s t a η x y r = β) ∧
      (∀ (T : Over S) (x y z : yoneda.obj T ⟶ U.obj.obj)
        (r : {r : yoneda.obj T ⟶ R.obj.obj // r ≫ s = x ∧ r ≫ t = y})
        (q : {q : yoneda.obj T ⟶ R.obj.obj // q ≫ s = y ∧ q ≫ t = z})
        (d : {d : yoneda.obj T ⟶ R.obj.obj // d ≫ s = x ∧ d ≫ t = z})
        (p : yoneda.obj T ⟶ pullback s t),
        p ≫ pullback.fst s t = q.val → p ≫ pullback.snd s t = r.val →
          p ≫ c = d.val →
            spaceGroupoidPresentationArrow s t a η x y r ≫
              spaceGroupoidPresentationArrow s t a η y z q =
                spaceGroupoidPresentationArrow s t a η x z d) ∧
      (∀ (Q : BasedCategory.{v₂, w₂} (Over S))
        (q : BasedFunctor (discreteModuli U.obj.obj) Q)
        (hQ : SpaceGroupoidQuotientPresentation s t e j c Q q),
        ∃ (i : BasedFunctor Q X) (θ : ModuliTwoIso (q.comp i) a),
          (∀ (T : Over S) (r : yoneda.obj T ⟶ R.obj.obj),
            i.map (hQ.arrows.val.hom.app (CostructuredArrow.mk r)) ≫
                θ.val.hom.app (CostructuredArrow.mk (r ≫ t)) =
              θ.val.hom.app (CostructuredArrow.mk (r ≫ s)) ≫
                η.val.hom.app (CostructuredArrow.mk r)) ∧
          (∀ (T : Over S) (b d : Functor.Fiber Q.p T),
            Function.Bijective ((moduliFiberMap i T).map (X := b) (Y := d))) ∧
          (IsAlgebraicModuliStack Q → IsRepresentableByAlgebraicSpaces i)) := by
  sorry

end CategoryTheory
