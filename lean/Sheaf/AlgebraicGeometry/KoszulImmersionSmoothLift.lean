/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import Sheaf.AlgebraicGeometry.KoszulRegularImmersionNear

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.SmoothSectionRegularImmersion
import WeilConjectures.RingTheory.RegularSequenceKoszulRegular

/-!
# Lifting a Koszul-regular immersion to a smooth ambient scheme

Source: Stacks Project, Divisors, Tag 067S, lemma-lift-regular-immersion-to-smooth,
Koszul-regular case (blueprint: lem-sfb-koszul-immersion-smooth-lift).

Koszul regularity is expressed by the existing near-point predicate at every source
point. In its closed charts the ideal has finite Koszul-regular generators, with
length allowed to vary and with the empty sequence allowed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A compatible immersion into a smooth ambient scheme is Koszul-regular when
its composite to the base is Koszul-regular. No Noetherian, separation,
quasi-compactness or constant-codimension assumption is made.

Source: Stacks Project, Divisors, Tag 067S, lemma-lift-regular-immersion-to-smooth
(blueprint: lem-sfb-koszul-immersion-smooth-lift).

Proof:
1. Form W = Z ×_S P using j and p (def-pc-fibre-product). The equation i ≫ p = j
   gives a graph s = (id, i) : Z → W with s ≫ a = id and s ≫ b = i.
2. The projection a : W → Z is smooth by smooth base change
   (lem-pc-proper-base-change, clause 2). Apply
   lem-sfb-smooth-section-regular-immersion to its section s. This gives immersion
   and closed affine charts with finite regular generators, allowing varying length.
3. Apply lem-weil-pbc-regular-sequence-koszul-regular to these generators with
   R = M = A. Injectivity on successive quotients gives Koszul regularity, including
   the empty sequence. Thus s is Koszul-regular locally at each source point.
4. Smoothness makes p flat (lem-pc-smooth-flat). The projection b : W → P is the
   base change of j along p, so clause 1 of
   lem-sfb-koszul-immersion-flat-ascent-etale-descent makes b Koszul-regular.
5. Apply lem-sfb-koszul-immersion-composition to s and b. Their composite is i,
   so i is Koszul-regular. For empty Z the pointwise assertions are vacuous. -/
theorem koszulRegularImmersion_of_smooth_ambient
    {Z P S : Scheme.{u}} (i : Z ⟶ P) (p : P ⟶ S) (j : Z ⟶ S)
    (hcomm : i ≫ p = j) [Smooth p] [IsImmersion i] [IsImmersion j]
    (hj : ∀ z : Z, IsKoszulRegularImmersionNear j z) :
    ∀ z : Z, IsKoszulRegularImmersionNear i z := by
  sorry

end AlgebraicGeometry
