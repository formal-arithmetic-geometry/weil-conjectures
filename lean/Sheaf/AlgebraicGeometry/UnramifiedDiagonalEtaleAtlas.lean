/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import WeilConjectures.AlgebraicGeometry.DensePoints
import Sheaf.RingTheory.SmoothOverFieldRegularLocal
import Sheaf.AlgebraicGeometry.UnramifiedMaximalIdealResidueCriterion
import Mathlib.RingTheory.LocalRing.Module
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import Mathlib.AlgebraicGeometry.Limits

/-! # An unramified diagonal is equivalent to an etale scheme atlas

Source: Stacks Project, stacks-morphisms.tex, Tag 06N3 (theorem-DM), (1)--(3),
and Tag 050N (lemma-separated-implies-morphism-separated), (1), for the relative base
(blueprint: lem-sfb-unramified-diagonal-etale-atlas).

The smooth atlas hypothesis is written using every scheme base change and every
etale scheme chart of the resulting algebraic space. The relative diagonal and
Deligne--Mumford convention are the existing project definitions.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- An algebraic stack over a scheme has unramified relative diagonal exactly when
it has a representable surjective etale scheme atlas, equivalently when it is DM.
Source: Stacks Project, stacks-morphisms.tex, Tags 06N3 and 050N(1)
(blueprint: lem-sfb-unramified-diagonal-etale-atlas).

Proof, following the eleven steps of the DAG node:
1. Every scheme map to F is representable by algebraic spaces: its scheme tests
   are base changes of the representable diagonal. Their objects are triples of
   two objects and an isomorphism, with no residual automorphisms fixing the pair.
2. For an etale atlas W, put R = W x_F W. The projection R -> W is etale, hence
   unramified. Cancellation gives unramified R -> W x_S W, and descent along
   the flat locally finitely presented cover W x_S W -> F x_S F gives the claim
   [lem-sfb-stack-chartwise-smooth-etale-calculus, lem-sfb-space-unramified-permanence,
   lem-sfb-stack-representable-unramified-descent].
3. Conversely take a finite-type point and its locally finite type field
   representative a with etale self-relation, and a fixed smooth scheme atlas U.
   Then F_a = U x_F Spec k is nonempty, smooth over k, and locally finite type over U
   [lem-sfb-finite-type-point-etale-self-relation].
4. The triple descriptions identify F_a x_U F_a with the product of F_a and the
   self-relation of a. Its projections are etale. Its diagonal is etale by
   cancellation, and is a monomorphism, hence open. The open-diagonal criterion
   makes F_a -> U unramified [lem-trf-space-chartwise-etale-permanence,
   lem-sfb-space-etale-monomorphism-open, lem-sfb-space-unramified-open-diagonal].
5. Choose a nonempty affine etale chart V of F_a. It is smooth over k and
   unramified over U. Choose v closed with finite separable residue field over k
   [lem-pc-dense-separable-points]. Write u for its image in U.
6. Put A = O_(U,u), B = O_(V,v). Smoothness makes B regular local, and
   unramifiedness gives m_A B = m_B. Choose germs from m_A forming a basis of
   m_B / m_B^2. Nakayama gives minimal generators of m_B; regularity makes them
   a regular sequence. Represent them on an open U_0 about u, including the empty
   list when B is a field [lem-weil-pbc-smooth-over-field-regular-local,
   lem-trf-unramified-maximal-ideal-residue-criterion,
   lem-weil-pbc-nakayama-local-generators,
   lem-weil-pbc-regular-local-generators-regular-sequence].
7. Use the etale chart V_0 = V x_U U_0 of the field fibre. The fibrewise regular
   slice lemma, after shrinking U_0 about u, makes the zero scheme Z of these
   functions flat and locally finitely presented over F
   [lem-sfb-stack-fibre-regular-slice-flat].
8. The zero scheme T = Z x_(U_0) V_0 has local ring B / m_B = kappa(v).
   It is locally finite type over k and unramified near v by the local criterion
   [lem-trf-unramified-maximal-ideal-residue-criterion].
9. The cartesian description gives an etale chart T -> Z x_F Spec k. The
   fibrewise etale-locus lemma supplies an open W_x of Z, containing u, etale
   over F. The retained field-fibre point shows its image contains x
   [lem-sfb-stack-fibre-unramified-etale].
10. Use the fixed atlas U to bound the set of finite-type points and the sizes of
    these locally closed W_x. Their coproduct W is a scheme in the same universe.
    Stack descent glues the maps to F, and chartwise locality makes W -> F etale.
    Its image contains every finite-type point, so it is surjective. The empty
    stack uses the empty coproduct [lem-weil-pbc-scheme-coproduct-family,
    lem-sfb-stack-chartwise-smooth-etale-calculus,
    lem-sfb-stack-flat-lfp-finite-type-surjectivity, def-weil-size-convention].
11. The stack and representable diagonal were assumed; by the definition of
    IsDeligneMumfordModuliStack, the remaining atlas condition is precisely the
    same representable surjective etale scheme atlas. -/
theorem unramifiedModuliDiagonal_iff_etaleAtlas {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S))
    (hstack : IsModuliStack F) (hdiag : HasAlgebraicSpaceDiagonal F)
    (hatlas : ∃ (U : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj U)) F),
      ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) F),
        ∃ (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
          HasSpaceBaseChange a T t Z p ∧ SpaceMapIsSurjective Z T p ∧
          ∀ (V : Over S) (b : yoneda.obj V ⟶ Z.obj.obj), AlgebraicSpace.IsEtale b →
            AlgebraicGeometry.Smooth ((yoneda.preimage (b ≫ p)).left)) :
    (HasUnramifiedModuliDiagonal F ↔
      ∃ (W : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj W)) F),
        ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) F),
          ∃ (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
            HasSpaceBaseChange a T t Z p ∧
              SpaceMapIsEtale Z T p ∧ SpaceMapIsSurjective Z T p) ∧
    (HasUnramifiedModuliDiagonal F ↔ IsDeligneMumfordModuliStack F) := by
  sorry

end CategoryTheory
