/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.AlgebraicGeometry.SpaceGroupoidPresheafPresentation
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.CategoryTheory.SiteStackification
import Sheaf.CategoryTheory.GroupoidStackificationLocalDescription
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.AlgebraicSpaceCoproduct
import Mathlib.CategoryTheory.Sites.Sheafification

/-! # The fppf quotient of a smooth algebraic-space groupoid

Source: Stacks Project, algebraic.tex, Tags 04TK, 04WZ and 04X0;
spaces-groupoids.tex, Tags 044V and 04M9
(blueprint: lem-sfb-smooth-groupoid-fppf-quotient).

The original presheaf groupoid is specified up to equivalence over the base, with
its original arrows and their composition. The quotient is its specified fppf
stackification; full faithfulness of its map is not assumed. The atlas is the
composite of the object inclusion and the stackification map. The relation map
is the actual functor sending an arrow to its two endpoints and its image.
-/

@[expose] public section

set_option autoImplicit false

universe u v w v' w'

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory.Limits

namespace CategoryTheory

/-- A smooth groupoid with scheme object space has algebraic fppf quotient, with
its specified smooth surjective atlas and its canonical kernel-pair equivalence.

Source: Stacks Project, algebraic.tex, Tags 04TK, 04WZ, 04X0;
spaces-groupoids.tex, Tags 044V, 04M9
(blueprint: lem-sfb-smooth-groupoid-fppf-quotient).

Proof:
1. For two original objects u,v over T, their arrow presheaf is the fibre product
   T ×_(U ×_S U) R. By lem-trf-space-fibre-products-etale-covers it is an algebraic
   space and hence an fppf sheaf (def-trf-algebraic-space). Apply the arrow clause
   of lem-sfb-groupoid-stackification-local-description and the unit of
   def-weil-pbc-sheafification. Sheafification fixes this sheaf, so i is fully
   faithful on original objects, naturally in T. A space over S with a map to a
   scheme Z is equally a space over Z: test sections, diagonal tests and charts
   agree in the two descriptions.
2. An object of the 2-fibre product of U with U is (u,v,alpha). Step 1 gives
   exactly one original r with s(r)=u, t(r)=v and i(r)=alpha. Both factors have
   discrete fibres, so these bijections give the canonical equivalence, with
   its original arrow orientation. This is spaceGroupoidKernelPairMap.
3. For arbitrary a,b in Q(T), the object clause of
   lem-sfb-groupoid-stackification-local-description gives an fppf cover on
   which both are original objects. Their Isom sheaf is locally the algebraic
   space of step 1. Conjugation by the chosen local identifications gives the
   comparison and its inverse. Refine the cover to one member per point of T.
   Its index is bounded by the point set and its chart coproduct lies in the
   working universe (def-weil-size-convention,
   lem-weil-pbc-scheme-coproduct-family, lem-trf-algebraic-space-coproduct).
   Apply lem-sfb-fppf-local-algebraic-space to obtain the representable diagonal.
4. For q over T, apply the diagonal result over B=T ×_S U to the two objects
   q and the tautological image. Its Isom space F over B, also viewed over S
   and T, has sections (u,alpha:q -> i(u)), with discrete arrows. It therefore
   represents the specified atlas base change, including the projection to T.
5. Fppf locally write q as i(v). Steps 1 and 2 identify the base change of F
   with R ×_(s,U,v) T. Its projection is smooth by base change, and the identity
   e(v) supplies a section, so it is surjective, including over arbitrary fields.
6. Lem-sfb-space-smooth-surjective-fppf-locality descends smoothness and
   surjectivity to F -> T. This proves the atlas clause for every T,q.
   Stackification supplies the fppf stack condition. Restricting descent to
   etale coverings gives the etale stack condition in IsAlgebraicModuliStack.
   Together with step 3 and this atlas these are exactly algebraicity.

The presentation hypothesis concerns P, before stackification. Its full
faithfulness describes the original arrows R(T); none is assumed for i or Q.
All scheme tests have universe u; the two total categories have independent
explicit object and arrow universes, permitting a larger stackification. -/
theorem smooth_groupoid_fppf_quotient
    {S : Scheme.{u}} (U : Over S) (R : AlgebraicSpace S)
    (s t : R.obj.obj ⟶ yoneda.obj U) (e : yoneda.obj U ⟶ R.obj.obj)
    (j : R.obj.obj ⟶ R.obj.obj) (c : pullback s t ⟶ R.obj.obj)
    (P : BasedCategory.{v, w} (Over S))
    (a : BasedFunctor (discreteModuli (yoneda.obj U)) P)
    (hP : SpaceGroupoidPresheafPresentation
      (U := schemeSpace U) (R := R) s t e j c P a)
    (hs : SpaceMapIsSmooth R U s) (ht : SpaceMapIsSmooth R U t)
    (Q : BasedCategory.{v', w'} (Over S)) (i : BasedFunctor P Q)
    (hi : IsFppfStackification i) :
    HasAlgebraicSpaceDiagonal Q ∧
      IsSmoothModuliAtlas Q U (a.comp i) ∧
      (spaceGroupoidKernelPairMap (U := schemeSpace U) (R := R)
        (s := s) (t := t) (a := a) hP.arrows i).toFunctor.IsEquivalence ∧
      IsFppfModuliStack Q ∧ IsAlgebraicModuliStack Q := by
  sorry

end CategoryTheory
