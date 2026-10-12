/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FormallySmooth
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.FormallyUnramifiedConormal
import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.AlgebraicGeometry.Thickening
import Sheaf.AlgebraicGeometry.UniversalFirstOrderThickening
import Sheaf.AlgebraicGeometry.UniversalFirstOrderThickeningExists
import Sheaf.AlgebraicGeometry.UniversalThickeningFlatBaseChange
import Sheaf.AlgebraicGeometry.UniversalThickeningOpenRestriction

/-!
# Flat unramified morphisms are formally étale

Source: Stacks Project, More on Morphisms, Lemma 04FF and Definitions 02HG, 02H0
(blueprint: lem-weil-pbc-flat-unramified-formally-etale).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An unramified flat morphism has a unique lift across every affine first-order
thickening; in particular it is formally smooth and formally étale.
Source: Stacks Project, More on Morphisms, Lemma 04FF and Definitions 02HG, 02H0
(blueprint: lem-weil-pbc-flat-unramified-formally-etale).
Proof (Stacks 04FF, with 04FE (3) implies (1)), following the node's seven steps:
1. By lem-weil-pbc-unramified-formally-unramified, `f` is formally unramified,
   giving uniqueness. Choose its universal first order thickening `X ⊆ X'`
   (lem-weil-pbc-universal-first-order-thickening-exists), with square-zero ideal
   `I` and conormal sheaf `C = I` pulled back to `X`.
2. Let `p, q : X ×[S] X ⟶ X` be the projections and let `D` be the open image
   of the diagonal. Then `q` is formally unramified by
   lem-weil-pbc-formally-unramified-base-change, and `p` is flat by
   lem-weil-pbc-flat-morphism-base-change. Both projections compose with the
   diagonal to the identity.
3. By lem-weil-pbc-universal-thickening-flat-base-change, `p* C ≅ C_q`.
4. On `D`, `q` is an isomorphism. By
   lem-weil-pbc-universal-thickening-open-restriction, `C_q` restricted to `D`
   is the conormal sheaf of this isomorphism, hence zero: its universal first
   order thickening is the identity with zero ideal, by the universal property
   and uniqueness of universal first order thickenings.
5. Pull the isomorphism of step 3 back along the diagonal. Functoriality of
   module pullback and lem-weil-pbc-open-immersion-module-pullback-restriction,
   together with step 4 and `p` composed with the diagonal being the identity,
   give `C ≅ 0`.
6. The defining ideal `I` of `X ⊆ X'` has square zero, so its pullback to `X`
   is `I/I² = I` under the homeomorphism of underlying spaces. Thus `C = 0`
   forces `I = 0`, and the immersion `X ⟶ X'` is an isomorphism. For the given
   square, the universal property of `X'` gives a map `T' ⟶ X'`; composing
   with the inverse immersion gives the desired lift to `X`, with both
   triangles commuting. Step 1 gives its uniqueness.
7. Unique lifting is Definition 02HG; forgetting uniqueness gives
   `FormallySmooth f` by Definition 02H0 (def-sbc-formally-smooth).
-/
theorem flat_unramified_formally_etale {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    (h_unramified : LocallyOfFiniteType f ∧ IsOpenImmersion (pullback.diagonal f)) :
    (∀ {T T' : Scheme.{u}} (i : T ⟶ T') [IsAffine T] [IsAffine T'] [T'.Over S],
      IsFirstOrderThickening i →
        ∀ (a : T ⟶ X), a ≫ f = i ≫ (T' ↘ S) →
          ∃! a' : T' ⟶ X, i ≫ a' = a ∧ a' ≫ f = T' ↘ S) ∧
      FormallySmooth f := by
  sorry

end AlgebraicGeometry
