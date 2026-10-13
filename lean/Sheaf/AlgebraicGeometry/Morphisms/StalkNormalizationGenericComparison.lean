/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Comparison of stalk normalization with normalization of the local generic torsor

Source: Stacks Project, Tags 0EYJ, 0307 and 035I.
(blueprint: lem-sbc-stalk-normalization-generic-comparison)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The concrete stalk pullback is the normalization of a generic Galois cover of the
smooth local total space, with the comparison commuting with the maps to that space.

Source: Stacks Project, Tag 0EYJ, local reduction; Tag 0307, localization of integral closure.
(blueprint: lem-sbc-stalk-normalization-generic-comparison)

Proof: Put A = O_{S,s} and K = k(S), which is a fraction field of A. The map Spec A
has image the generalizations of s. Minimality of s outside U says all its other points
lie in U. A DVR has only its generic and closed points, so the inverse image of U is
exactly Spec K. Pulling back the given generic-fibre square identifies the generic
fibre of L = C times_S Spec A with the base change of C_eta. Pull back Z and its action
along this identification: its total space is the fibre product, and each action map
is induced by the action on Z and the identity on the new base. Finiteness, etaleness,
surjectivity and the simply transitive action identity are preserved by base change.
This constructs W. The comparison square hψ identifies W with the restriction to the
punctured local base of PA. Choose an affine neighbourhood V = Spec B of s in S,
and cover c⁻¹(V) by affine opens E = Spec R. If the prime of s in B is q, the
corresponding base change of E has ring R localized at the image of B \ q.
The inverse image of E in PA is qcqs: PA is finite over C_U and C_U is a
quasi-compact open of C. Its sections therefore commute with this flat localization
base change. Relative normalization on E is the spectrum of the integral closure
of R in these sections. Tag 0307 identifies its localization with the integral
closure for the generic cover W. The affine comparison isomorphisms preserve the
algebra maps from the base and agree on intersections by the universal property of
relative normalization (035I). Gluing them gives β with the asserted equality over L.
This works also for an empty total space. Invertibility of the group order and
ramification theory are not used in this comparison. -/
theorem GaloisCover.stalk_normalization_generic_comparison {S C : Scheme.{u}}
    [IsNoetherian S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c]
    (G : Type (u + 1)) [Group G] [Finite G]
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (Z : GaloisCover G Cη)
    (U : S.Opens) (hηU : genericPoint S ∈ U)
    (jU : Cη ⟶ (c ⁻¹ᵁ U).toScheme) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (ψ : Z.P ⟶ PA.obj.left) (hjU : jU ≫ (c ⁻¹ᵁ U).ι = j)
    (hψ : IsPullback ψ Z.π PA.obj.hom jU)
    (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s)
    (hdvr : IsDiscreteValuationRing (S.presheaf.stalk s)) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let a := S.fromSpecStalk s
    let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
    letI : IsDiscreteValuationRing (S.presheaf.stalk s) := hdvr
    ∃ W : GaloisCover G (pullback (pullback.snd c a)
        (Spec.map (CommRingCat.ofHom
          (algebraMap (S.presheaf.stalk s) S.functionField)))),
      letI : IsFinite W.π := W.isFinite
      ∃ β : pullback (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a) ≅
        (W.π ≫ pullback.fst (pullback.snd c a)
          (Spec.map (CommRingCat.ofHom
            (algebraMap (S.presheaf.stalk s) S.functionField)))).normalization,
        β.hom ≫ (W.π ≫ pullback.fst (pullback.snd c a)
          (Spec.map (CommRingCat.ofHom
            (algebraMap (S.presheaf.stalk s) S.functionField)))).fromNormalization = n := by sorry

end AlgebraicGeometry.Scheme
