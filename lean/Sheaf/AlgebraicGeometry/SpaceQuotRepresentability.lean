/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q83
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor
import Sheaf.AlgebraicGeometry.SpaceCoherentStackGeneral
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
import Sheaf.AlgebraicGeometry.RepresentableSourceAlgebraic
import Sheaf.AlgebraicGeometry.AlgebraicSetoidSpace
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest

/-! # Representability of the proper-support Quot presheaf

Source: Stacks Project, quot.tex, Tag 09TU, proposition-quot
(blueprint: lem-sfb-space-quot-representability).

The representing bijections range over every scheme mapping to B. Their compatibility
with the actual tensor-pullback transitions is stated explicitly. Finite presentation
of the source module is required only for local finite presentation of the representing map.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The proper-support Quot presheaf of any quasi-coherent module along a separated
finitely presented algebraic-space morphism is represented by an algebraic space over B.
The displayed subtype is Hom_B(T,R), since spaces are a full subcategory of sheaves.
Source: Stacks Project, quot.tex, Tag 09TU, proposition-quot
(blueprint: lem-sfb-space-quot-representability).

Proof:
1. Use lem-sfb-space-coherent-stack-general to obtain the algebraic stack of finitely
   presented quasi-coherent modules flat over the base with proper support. Form the
   fibred groupoid of admissible quotient maps of F, with pullback isomorphisms
   intertwining the maps; forget the quotient map to obtain a morphism to that stack.
2. Over a scheme T with a module G in the coherent stack, the fibre groupoid has objects
   (q, theta : target(q) ≅ G). Sending this to theta q identifies it with the discrete
   functor of surjections F_T → G. Its inverse uses the identity isomorphism. Every
   arrow is forced to be theta₂⁻¹ theta₁, and these formulas commute with pullback.
   By lem-sfb-space-flat-proper-fp-locality and
   lem-sfb-space-module-pullback-quasicoherent, the hypotheses of
   lem-sfb-space-module-hom-affine apply and supply an affine Hom space over T.
3. The surjective locus in this Hom space is open by
   lem-sfb-space-module-surjectivity-open on every scheme test. The module G is of
   finite type since it is finitely presented; all its proper-support conditions persist
   under base change. Thus def-a1-space-open-subspace makes the locus an algebraic
   space. Apply lem-sfb-stack-representable-source-algebraic to the forgetful morphism.
4. An automorphism of a quotient fixes its surjection, so it is identity: sections locally
   lift through a sheaf surjection. Apply lem-sfb-algebraic-setoid-space. The resulting
   space R has sections (b,[q]); projection to b defines r. Taking fibres at each b
   gives the displayed bijections, compatible with every pullback transition of
   def-sfb-space-proper-quot-functor.
5. If F is finitely presented, so are its tensor pullbacks, by pulling back its finite
   local presentation. The Hom spaces in step 2 are now finitely presented. Their open
   surjection loci are locally finitely presented, hence so is the forgetful morphism,
   by lem-sfb-space-separated-fp-composition. After an etale scheme chart V → B,
   lem-sfb-space-coherent-stack-general makes the coherent stack locally finitely
   presented over V. The local-finite-presentation clause of
   lem-sfb-stack-representable-source-algebraic gives a smooth surjective atlas W of
   R ×_B V with W → V locally finitely presented. Apply
   lem-sfb-smooth-cover-flat-lfp-descent and lem-sfb-space-local-properties-chart-test
   to descend local finite presentation to r. No finite presentation of F is used earlier.
-/
theorem exists_properQuot_representing_space {S : Scheme.{u}} {A B : AlgebraicSpace S}
    (a : A ⟶ B) (ha : ProperQuotFinitePresentation a) (hsep : MapIsSeparated a)
    (F : A.QCoh) :
    ∃ (R : AlgebraicSpace S) (r : R ⟶ B)
      (e : ∀ T : ProperQuotTest B,
        { f : yoneda.obj T.left ⟶ R.obj.obj // f ≫ r.hom.hom = T.hom } ≃
          (properQuotFunctor a ha F).obj (op T)),
      (∀ (T' T : ProperQuotTest B) (h : T' ⟶ T)
        (f : { f : yoneda.obj T.left ⟶ R.obj.obj // f ≫ r.hom.hom = T.hom })
        (f' : { f : yoneda.obj T'.left ⟶ R.obj.obj // f ≫ r.hom.hom = T'.hom }),
        yoneda.map h.left ≫ f.val = f'.val →
          e T' f' = (properQuotFunctor a ha F).map h.op (e T f)) ∧
      (F.obj.IsFinitePresentation → MapIsLocallyOfFinitePresentation r) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
