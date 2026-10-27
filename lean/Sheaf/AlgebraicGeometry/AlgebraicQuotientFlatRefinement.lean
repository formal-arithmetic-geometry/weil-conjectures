/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q102
-/
module

public import Sheaf.AlgebraicGeometry.SpaceGroupoidQuotientPresentation
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.CategoryTheory.GroupoidStackificationLocalDescription
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfFiniteAffineRefinement
import Mathlib.AlgebraicGeometry.Limits

/-! # Flat refinements of algebraic quotient stacks

Source: Stacks Project, criteria.tex, Tag 06PJ, lemma-quotient-algebraic,
necessary implication (blueprint: lem-sfb-algebraic-quotient-flat-refinement).

The quotient is specified by its fppf presentation, without choosing a stackification.
The restricted relation is identified with the actual iterated sheaf pullback, and
its projections retain this identification. The structural map of the new object
space to B is the composite with g. No property of g, s or t is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic quotient of an arbitrary groupoid admits a restriction with flat,
locally finitely presented arrow projections and fppf locally surjective saturation.
Source: Stacks Project, criteria.tex, Tag 06PJ, necessary implication
(blueprint: lem-sfb-algebraic-quotient-flat-refinement).

Proof, following the accepted seven-step split:
1. Choose a scheme W and a smooth surjective atlas W -> X of the algebraic stack X.
   By def-sfb-algebraic-moduli-stack and def-sfb-stable-pointed-moduli-groupoids it
   is an object of X(W); composing with X -> B gives its structural map to B.
2. By lem-sfb-groupoid-stackification-local-description, lift this object fppf locally
   to maps W_i -> U and isomorphisms to its pullback. The isomorphisms force the maps
   to agree over B. Each W_i -> W is flat and locally of finite presentation.
3. Retain one covering member for each point of W. The retained index set belongs to
   the fixed universe (def-weil-size-convention). Form U' as their scheme coproduct
   by lem-weil-pbc-scheme-coproduct-family. Glue the maps to U and their isomorphisms
   on its disjoint open components. The resulting b : U' -> W is flat, locally of
   finite presentation and surjective by open-source locality, including empty W.
4. By lem-sfb-stack-chartwise-smooth-etale-calculus, the composite U' -> W -> X is
   representable, flat, locally of finite presentation and surjective. The glued
   isomorphism identifies it with a : U' -> U -> X, giving the same properties for a.
5. The arrow presheaves of the original space groupoid are already sheaves. The
   isomorphism-sheaf clause of lem-sfb-groupoid-stackification-local-description
   therefore identifies U' x_X U' with U' x_(g,U,t) R x_(s,U,g) U', respecting both
   projections. Use the isomorphism from a(w) to a(v), so t(r)=g(v), s(r)=g(w).
   This is an algebraic space by lem-trf-space-fibre-products-etale-covers.
6. Both projections are base changes of a; the chartwise calculus gives their
   flatness and local finite presentation under the preceding identification.
7. For T -> U, form P = U' x_X T. It is surjective, flat and locally of finite
   presentation over T. On each affine open of T apply
   lem-sfb-space-fppf-finite-affine-refinement to P -> T. Compose its scheme covers
   with these open immersions to obtain an fppf cover of T (def-pc-fppf-site,
   def-weil-flat-morphism, def-sbc-locally-finite-presentation). Each map into P
   supplies v into U' and an isomorphism, hence, by step 5, an arrow r with
   t(r)=g(v) and s(r)=u. This is exactly local lifting for the saturation map.
   The empty test scheme is covered by the empty family. -/
theorem exists_algebraic_quotient_flat_refinement {S : Scheme.{u}}
    (B U R : AlgebraicSpace S) (bU : U ⟶ B) (bR : R ⟶ B)
    (s t : R ⟶ U) (hs : s ≫ bU = bR) (ht : t ≫ bU = bR)
    (e : U.obj.obj ⟶ R.obj.obj) (i : R.obj.obj ⟶ R.obj.obj)
    (c : Limits.pullback s.hom.hom t.hom.hom ⟶ R.obj.obj)
    (X : BasedCategory.{v, w} (Over S))
    (a : BasedFunctor (discreteModuli U.obj.obj) X)
    (hquot : SpaceGroupoidQuotientPresentation s.hom.hom t.hom.hom e i c X a)
    (halg : IsAlgebraicModuliStack X) :
    ∃ (U' : AlgebraicSpace S) (g : U' ⟶ U),
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
        ((Limits.pullback.snd g.hom t.hom).hom ≫ s.hom.hom) ∧
      ∃ (R' : AlgebraicSpace S)
        (ρ : R'.obj ≅ Limits.pullback (Limits.pullback.snd g.hom t.hom ≫ s.hom) g.hom)
        (p q : R' ⟶ U'),
        p.hom = ρ.hom ≫
          Limits.pullback.fst (Limits.pullback.snd g.hom t.hom ≫ s.hom) g.hom ≫
            Limits.pullback.fst g.hom t.hom ∧
        q.hom = ρ.hom ≫
          Limits.pullback.snd (Limits.pullback.snd g.hom t.hom ≫ s.hom) g.hom ∧
        MapIsFlat p ∧ MapIsLocallyOfFinitePresentation p ∧
        MapIsFlat q ∧ MapIsLocallyOfFinitePresentation q := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
