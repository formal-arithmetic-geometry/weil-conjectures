/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFourPropertyFppfDescent
import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfFiniteAffineRefinement
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # Fppf descent of finite algebraic-space morphisms

Source: Stacks Project, Spaces Descent, Tag 0426 (lemma-descending-property-finite),
fppf specialization; Morphisms of Spaces, Tag 03ZQ (lemma-integral-local)
(blueprint: lem-sfb-space-finite-fppf-descent).

Finiteness uses the existing scheme-test representability predicate with the finite
scheme-morphism property. The base change is the canonical second projection from the
sheaf fibre product, which is an algebraic space by the fibre-product closure theorem.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Finiteness on every scheme test is equivalent to finiteness after every member of a
jointly surjective family of flat locally finitely presented algebraic-space morphisms.
Source: Stacks Project, Spaces Descent, Tag 0426; Morphisms of Spaces, Tag 03ZQ
(blueprint: lem-sfb-space-finite-fppf-descent).

Proof, following the accepted six-step split:
1. Scheme testing commutes with arbitrary base change: the iterated sheaf pullback
   is canonically the original scheme test, with the same projection. This follows
   from lem-trf-space-fibre-products-etale-covers and proves the forward implication.
2. For the converse each local finite map is affine by
   def-weil-finite-integral-morphism and lem-weil-pbc-affine-morphism-permanence.
   Apply the affine clause of lem-sfb-space-four-property-fppf-descent. For any
   scheme T mapping to Y, its pullback X_T has affine schematic open subspaces X_U
   over the affine opens U of T. By def-a1-space-open-subspace and
   lem-sfb-space-largest-schematic-open these lie in its largest schematic open A.
   For every scheme W mapping to X_T, the open W times_X_T A contains the covering
   opens W times_T U, hence equals W. Thus A equals X_T, so X_T is a scheme.
   Its projection to T is affine by pqf-def-affine-morphism.
3. For affine T, apply lem-sfb-space-fppf-finite-affine-refinement: a finite family
   of affine V_j mapping through the covering members gives an affine flat
   surjection T' = coproduct V_j to T. The projection from X_T times_T V_j is
   identified, by its pullback projections, with a scheme test of a local finite
   map. It is therefore finite.
4. The coprojections V_j to T' form an open cover by
   lem-weil-pbc-scheme-coproduct-family. Apply the open-cover clause of
   lem-weil-pbc-finite-local-on-target to conclude that X_T times_T T' to T' is
   finite, including the empty coproduct case.
5. The map T' to T is affine by lem-weil-pbc-morphism-affine-schemes-affine and
   quasi-compact by lem-weil-pbc-affine-morphism-permanence. Step 2 supplied the
   scheme sources, so lem-sbc-finite-morphism-fpqc-descent applies and proves the
   scheme test over affine T finite.
6. For general T, finiteness on its affine open cover implies finiteness over T
   by lem-weil-pbc-finite-local-on-target. The empty scheme and empty original
   covering are included: joint surjectivity of an empty family forces empty Y. -/
theorem finite_fppf_descent {S : Scheme.{u}} {I : Type w}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (Yᵢ : I → AlgebraicSpace S) (g : ∀ i : I, Yᵢ i ⟶ Y)
    (hflat : ∀ i : I, MapIsFlat (g i))
    (hlfp : ∀ i : I, MapIsLocallyOfFinitePresentation (g i))
    (hsurj : IsJointlySurjective (fun i : I ↦ (g i).hom.hom)) :
    IsRepresentableWith (fun _ _ p ↦ IsFinite p.left) f.hom.hom ↔
      ∀ i : I, IsRepresentableWith (fun _ _ p ↦ IsFinite p.left)
        (Limits.pullback.snd f.hom (g i).hom).hom := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
