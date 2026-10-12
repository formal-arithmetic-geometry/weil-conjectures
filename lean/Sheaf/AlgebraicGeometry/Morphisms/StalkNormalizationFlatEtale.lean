/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import Mathlib.AlgebraicGeometry.Normalization

public import Sheaf.RingTheory.Depth

import Sheaf.RingTheory.NormalLocalDepthTwo
import Sheaf.RingTheory.FlatLocalDepthFormula

/-!
# Purity turns flatness of a depth-two normalization into etaleness

Source: Stacks Project, Tag 0EY6, assertion (3), applied to the local
normalization in the proof of Tag 0EYJ.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- On the finite local normalization, every flat source open is etale.
No section, group action, or generic rational point is assumed.

Source: Stacks Project, Tag 0EY6, assertions (2) and (3); Tag 0EYJ,
proof of the local claim, paragraph starting with depth(A) at least two.
(blueprint: lem-sbc-stalk-normalization-flat-etale)

Proof: Write A = O(S,s), L = C times_S Spec A and L° for the inverse image
of U. Every point of Spec A maps to a generalization of s; minimality says
its complement over U consists exactly of the closed point. Thus L minus
L° is the closed fibre. Smoothness makes L flat over A. At each point y of
the closed fibre, the flat local depth formula gives
  depth(O(L,y)) = depth(A) + depth(O(L,y)/m_A O(L,y)) >= 2.
The scheme L is Noetherian and normal: these properties follow respectively
from finite type over A and smoothness over the normal local domain A.
The generic-point condition makes L° dense, and the finite etale model on
L° is normal. The normalization N is normal, and the pullback in the
statement is its localization at s, hence normal too. At a point z over
the closed fibre, going down over the normal base and incomparability for the integral
normalization give equal heights of z and n(z), componentwise. The local
rings therefore have equal dimension. This dimension is at least
two, so normality gives depth(O(N,z)) >= 2. Over L° the normalization
recovers the finite etale model, by integral closure of a normal finite
algebra. Consequently N is the unique depth-two finite extension in
Tag 0EY6(2). By Tag 0EY6(3), it is etale at a point exactly when it is flat
there. If V to L is flat, N to L is flat at every point of V, since the
open immersion V to N induces stalk isomorphisms. Therefore N to L is
etale at every point of V. Etaleness is local on the source, and hence
V to L is etale. Empty V gives the empty etale map; no connectedness of
the finite cover is required. -/
theorem finiteEtale_stalk_normalization_etale_of_flat {S C : Scheme.{u}}
    [IsNoetherian S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c]
    (U : S.Opens) (hηU : genericPoint S ∈ U)
    (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
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
    IsFinite n → ∀ V : (pullback (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
      (pullback.fst c a)).Opens, Flat (V.ι ≫ n) → Etale (V.ι ≫ n) := by sorry

end AlgebraicGeometry.Scheme
