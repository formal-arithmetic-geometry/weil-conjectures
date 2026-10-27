/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q97
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.CategoryTheory.SiteStackification
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Fppf descent from an étale stack with a smooth atlas

Source: Stacks Project, criteria.tex, Tag 076V, lemma-stacks-etale
(blueprint: lem-sfb-etale-smooth-atlas-fppf-descent).

The atlas is specified, so both its projection properties and the diagonal are retained
when the topology used for descent changes. The conclusion supplies the fppf stack
condition; together with the unchanged diagonal and atlas hypotheses it gives precisely
an algebraic stack with this atlas.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry

namespace CategoryTheory

/-- An étale stack with algebraic-space diagonal and a specified smooth surjective
scheme atlas satisfies fppf descent, for both isomorphisms and objects.
Source: Stacks Project, criteria.tex, Tag 076V, lemma-stacks-etale
(blueprint: lem-sfb-etale-smooth-atlas-fppf-descent).

Proof:
1. Put R = U ×_F U. Its two projections are smooth, one by the atlas hypothesis
   and the other by inversion. Identity, inverse and composition of isomorphisms
   make (U,R) a smooth groupoid in algebraic spaces (def-trf-algebraic-space).
   Its presheaf of groupoids P maps fully faithfully to F.
2. By lem-sfb-groupoid-stackification-local-description extend this map to the
   étale stackification E. Its map to F is fully faithful: first for objects of P,
   since sheafifying their isomorphism presheaves changes nothing, then for all
   objects by taking a common étale cover and gluing isomorphisms uniquely.
3. Apply lem-sfb-smooth-space-cover-etale-sections to each atlas pullback over T.
   This gives étale local lifts of every object of F to U, so E → F is locally
   essentially surjective. By lem-sfb-stack-fully-faithful-local-equivalence it is
   an equivalence.
4. By lem-sfb-smooth-groupoid-fppf-quotient, the fppf stackification Q of P is an
   fppf stack with smooth surjective atlas U. It is an étale stack too, since
   étale covering maps are flat and locally finitely presented
   (def-weil-etale-morphism, def-pc-fppf-site). The universal extension of
   lem-sfb-groupoid-stackification-local-description gives E → Q.
5. For objects of P the isomorphism presheaves are algebraic spaces by the diagonal
   hypothesis, hence already fppf sheaves (def-trf-algebraic-space). The local
   description of stackification identifies these isomorphisms in E and Q.
   Étale local presentations of arbitrary objects and unique gluing therefore
   make E → Q fully faithful.
6. The atlas pullbacks in Q are smooth surjective algebraic spaces. Apply
   lem-sfb-smooth-space-cover-etale-sections again, and then
   lem-sfb-stack-fully-faithful-local-equivalence: E → Q is an equivalence.
   Combining with step 3 gives a pullback-compatible equivalence H : F ≃ Q.
7. Full faithfulness transfers the fppf isomorphism-sheaf condition. For object
   descent send a datum (x_i, alpha_ij) through H, glue in Q, and apply an inverse K.
   If eta : 1 ≅ KH, compose the resulting local isomorphisms with eta inverse
   to obtain d_i : K(q)|_Ti ≅ x_i. Naturality of eta and the gluing relation in Q
   give d_j = alpha_ij d_i, hence d_j d_i inverse = alpha_ij, so the original datum
   is effective. Diagonal representability and the given atlas are scheme-test
   properties independent of topology, and retain their original witnesses. -/
theorem isFppfModuliStack_of_etale_smooth_atlas
    {S : Scheme.{u}} (F : BasedCategory.{v, w} (Over S))
    (hstack : IsModuliStack F) (hdiag : HasAlgebraicSpaceDiagonal F)
    (U : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (hatlas : IsSmoothModuliAtlas F U a) :
    IsFppfModuliStack F := by
  sorry

end CategoryTheory
