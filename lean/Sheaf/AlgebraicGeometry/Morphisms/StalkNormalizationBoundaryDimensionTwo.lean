/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import Mathlib.AlgebraicGeometry.Normalization

public import Sheaf.RingTheory.Depth

public import Mathlib.RingTheory.KrullDimension.Basic

import Mathlib.RingTheory.IntegralClosure.GoingDown
import Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationNormalDense
import Sheaf.RingTheory.SmoothNormalRing
import Sheaf.RingTheory.FlatLocalDepthFormula
import Sheaf.RingTheory.DepthLeSupportDimension

/-!
# Boundary dimensions of the localized relative normalization

Source: Stacks Project, Tags 0EYJ, 0337, 00LK, 033C and 00H8.
(blueprint: lem-sbc-stalk-normalization-boundary-dimension-two)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Boundary stalks of the finite localized normalization have dimension at least two.

Source: Stacks Project, Tag 0EYJ, the depth calculation before the formal test;
Tags 0337, 00LK, 033C and 00H8 (going down over a normal domain).
(blueprint: lem-sbc-stalk-normalization-boundary-dimension-two)

Proof: Put A = O(S,s), L = C times_S Spec A and N = the localized normalization.
Every point of Spec A specializes to its closed point. By minimality of s,
a point of L outside the inverse image of C_U maps to the closed point of Spec A.
The closed-point stalk of Spec A is A. Smoothness of L over Spec A makes its
stalk maps flat and local. The flat local depth formula gives depth at least two
at each such target point; depth is at most Krull dimension.
Smoothness over the normal base makes L normal. The localized normalization N
is normal, and its inverse image of C_U is dense. On normal affine components,
the finite map N to L is given by integral extensions of normal domains:
normalization of the finite etale cover on C_U has each component dominating
its corresponding component of L, so the ring map is injective. Going down
lifts a strict prime chain of length two ending at the target prime to a
strict chain ending at any source prime over it. Localizing these chains
proves that every source stalk above the boundary has dimension at least two.
An empty cover has no source points and the conclusion is vacuous. No formal
test, power-series ring or coproduct is involved in this dimension assertion. -/
theorem stalk_normalization_boundary_dimension_two {S C : Scheme.{u}}
    [IsNoetherian S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c]
    (U : S.Opens) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s)
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth
      (R := S.presheaf.stalk s) (S.presheaf.stalk s)) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let a := S.fromSpecStalk s
    let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
    IsFinite n → ∀ z : (pullback
      (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a) : Scheme.{u}),
      n z ∉ (pullback.fst c a) ⁻¹ᵁ (c ⁻¹ᵁ U) →
      (2 : WithBot ℕ∞) ≤ ringKrullDim
        ((pullback (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
          (pullback.fst c a) : Scheme.{u}).presheaf.stalk z) := by sorry

end AlgebraicGeometry.Scheme
