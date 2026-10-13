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
import Sheaf.AlgebraicGeometry.Morphisms.GaloisCoverBaseChange
import Sheaf.AlgebraicGeometry.Morphisms.NormalizationStalkBaseChange
import Sheaf.AlgebraicGeometry.Morphisms.StalkGenericOpenPullback

/-!
# Comparison of stalk normalization with normalization of the local generic torsor

Source: Stacks Project, Tags 0EYJ, 0307 and 035I.
(blueprint: lem-sbc-stalk-normalization-generic-comparison)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem normalization_iso_of_iso_over {X Y T : Scheme.{u}}
    (f : X ⟶ T) (g : Y ⟶ T) [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g] (e : X ≅ Y) (he : e.hom ≫ g = f) :
    ∃ E : f.normalization ≅ g.normalization,
      E.hom ≫ g.fromNormalization = f.fromNormalization := by
  have hi : e.inv ≫ f = g := by rw [← he]; simp
  let a := f.normalizationDesc (e.hom ≫ g.toNormalization) g.fromNormalization
    (by simp [he])
  let b := g.normalizationDesc (e.inv ≫ f.toNormalization) f.fromNormalization
    (by simp [hi])
  have hab : a ≫ b = 𝟙 _ := by
    apply Hom.normalization.hom_ext _ _ _ f.fromNormalization
    · simp [a, b]
    · simp [a, b]
    · simp
  have hba : b ≫ a = 𝟙 _ := by
    apply Hom.normalization.hom_ext _ _ _ g.fromNormalization
    · simp [a, b]
    · simp [a, b]
    · simp
  exact ⟨⟨a, b, hab, hba⟩, by simp [a]⟩

-- The retained normality and generic-open hypotheses are unnecessary for this comparison.
set_option linter.unusedVariables false in
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
            (algebraMap (S.presheaf.stalk s) S.functionField)))).fromNormalization = n := by
  let : IsFinite PA.obj.hom := PA.property
  let : QuasiCompact (c ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
      (inferInstance : QuasiCompact U.ι)
  let a := S.fromSpecStalk s
  let d := pullback.snd c a
  let g := pullback.fst c a
  let b := Spec.map (CommRingCat.ofHom
    (algebraMap (S.presheaf.stalk s) S.functionField))
  let p := pullback.fst d b
  let v := pullback.snd d b
  have hb : b ≫ a = S.fromSpecStalk (genericPoint S) := by
    exact SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec S).specializes trivial)
  have hv : v ≫ S.fromSpecStalk (genericPoint S) = (p ≫ g) ≫ c := by
    calc
      v ≫ S.fromSpecStalk (genericPoint S) = (v ≫ b) ≫ a := by
        rw [Category.assoc, hb]
      _ = (p ≫ d) ≫ a := by rw [← pullback.condition]
      _ = (p ≫ g) ≫ c := by
        dsimp [d, g]
        rw [Category.assoc, ← pullback.condition, Category.assoc]
  let γ := hCη.lift v (p ≫ g) hv
  have hγ : γ ≫ j = p ≫ g := hCη.lift_snd _ _ _
  have hk : (γ ≫ jU) ≫ (c ⁻¹ᵁ U).ι = p ≫ g := by
    rw [Category.assoc, hjU, hγ]
  have hU := stalk_generic_open_isPullback c U s hs hmin hdvr (γ ≫ jU) hk
  obtain ⟨W, ρ, hW⟩ := GaloisCover.exists_baseChange G Z γ
  let : IsFinite W.π := W.isFinite
  have hP : IsPullback (ρ ≫ ψ) (W.π ≫ p)
      (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι) g :=
    (hW.paste_horiz hψ).paste_vert hU
  let f := PA.obj.hom ≫ (c ⁻¹ᵁ U).ι
  let : IsIso (f.normalizationPullback g) :=
    Hom.isIso_normalizationPullback_stalk c f s
  obtain ⟨E, hE⟩ := normalization_iso_of_iso_over
    (W.π ≫ p) (pullback.snd f g) hP.isoPullback hP.isoPullback_hom_snd
  let β := (asIso (f.normalizationPullback g)).symm ≪≫ E.symm
  refine ⟨W, β, ?_⟩
  have hi : E.inv ≫ (W.π ≫ p).fromNormalization = (pullback.snd f g).fromNormalization := by
    rw [← hE]; simp
  change β.hom ≫ (W.π ≫ p).fromNormalization = pullback.snd f.fromNormalization g
  dsimp [β]
  rw [Category.assoc, hi]
  exact (IsIso.inv_comp_eq (f.normalizationPullback g)).mpr (Hom.normalizationPullback_snd f g).symm

end AlgebraicGeometry.Scheme
