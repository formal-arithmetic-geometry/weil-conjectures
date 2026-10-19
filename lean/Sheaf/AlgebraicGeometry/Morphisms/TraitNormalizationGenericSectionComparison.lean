/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.RingTheory.DiscreteValuationRing.Basic


import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ExtendOverInertia

/-! Generic section comparison for a normalization over a local trait. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option linter.unusedVariables false in
/-- The normalization over the local trait agrees with the original cover on a generic section.

Source: Stacks Project, Tag 0EYJ, local trait reduction, and Tag 0EYI.
(blueprint: lem-sbc-trait-normalization-generic-section-comparison)

Proof: Compose delta with the fraction-field inclusion and extend this injection
uniquely from O_(S,s) to its fraction field k(S). Applying Spec gives b and the
identity t followed by a = b followed by the generic-point inclusion. The section
compatibility then identifies t followed by tau and the projection to C with
b followed by seta, jU and the open inclusion. The existing normalization-over-an-open
isomorphism identifies PA with the normalization over C pulled back to C_U; PA is
finite and therefore equals its relative normalization over C_U. Paste this square
with hpsi and the pullback along b followed by seta. Paste the defining square of
n with the pullback along t followed by tau. Their bottom morphisms agree by the
section identity, so uniqueness of pullbacks gives beta with the asserted projection
equality. This proof uses no ramification, smooth ascent of normality, or split fibre. -/
theorem GaloisCover.trait_normalization_generic_section_comparison {S C : Scheme.{u}}
    [IsNoetherian S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S)
    (G : Type (u + 1)) [Group G] [Finite G]
    (hG : IsUnit (Nat.card G : Γ(S, ⊤)))
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (sη : Spec S.functionField ⟶ Cη) (hsq : sη ≫ q = 𝟙 _)
    (hsj : sη ≫ j = S.fromSpecStalk (genericPoint S) ≫ σ)
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
    let τ : Spec (S.presheaf.stalk s) ⟶ pullback c a :=
      pullback.lift (a ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])
∀ (A : CommRingCat.{u}) (_ : IsDomain A)
      (K : Type u) (_ : Field K) (_ : Algebra A K) (_ : IsFractionRing A K)
      (δ : S.presheaf.stalk s →+* A), Function.Injective δ →
      ∃ (b : Spec (CommRingCat.of K) ⟶ Spec S.functionField)
        (β : pullback n
          (Spec.map (CommRingCat.ofHom ((algebraMap A K).comp δ)) ≫ τ) ≅
            pullback Z.π (b ≫ sη)),
        β.hom ≫ pullback.snd Z.π (b ≫ sη) =
          pullback.snd n
            (Spec.map (CommRingCat.ofHom ((algebraMap A K).comp δ)) ≫ τ)  := by
  classical
  let : IsFinite PA.obj.hom := PA.property
  let : QuasiCompact (c ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
      (inferInstance : QuasiCompact U.ι)
  dsimp only
  intro A hAd K hK hAK hfrac δ hδ
  let := hAd
  let := hK
  let := hAK
  let := hfrac
  let a := S.fromSpecStalk s
  let i := (c ⁻¹ᵁ U).ι
  let f := PA.obj.hom ≫ i
  let l := pullback.fst c a
  let n := pullback.snd f.fromNormalization l
  let τ : Spec (S.presheaf.stalk s) ⟶ pullback c a :=
    pullback.lift (a ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])
  let t := Spec.map (CommRingCat.ofHom ((algebraMap A K).comp δ))
  let ε : S.functionField →+* K :=
    IsFractionRing.lift (g := (algebraMap A K).comp δ)
      ((IsFractionRing.injective A K).comp hδ)
  let b := Spec.map (CommRingCat.ofHom ε)
  have ht : t ≫ a = b ≫ S.fromSpecStalk (genericPoint S) := by
    have hε : ε.comp (algebraMap (S.presheaf.stalk s) S.functionField) =
        (algebraMap A K).comp δ := by
      ext r
      exact IsFractionRing.lift_algebraMap (g := (algebraMap A K).comp δ)
        ((IsFractionRing.injective A K).comp hδ) r
    rw [show t = b ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (S.presheaf.stalk s) S.functionField)) by
        simp only [b, t, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hε]]
    rw [Category.assoc]
    congr 1
    exact SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec S).specializes trivial)
  have hbase : (t ≫ τ) ≫ l = ((b ≫ sη) ≫ jU) ≫ i := by
    simp only [τ, l, Category.assoc, pullback.lift_fst]
    rw [← Category.assoc, ht, Category.assoc, ← hsj]
    simpa only [Category.assoc, i] using
      congrArg (fun z ↦ b ≫ sη ≫ z) hjU.symm
  let ν := Hom.pullbackFromNormalizationIso PA.obj.hom i
  have ha : ν.inv ≫ pullback.snd f.fromNormalization i = PA.obj.hom := by
    apply (cancel_epi ν.hom).mp
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    exact (Hom.pullbackFromNormalizationIso_hom_comp PA.obj.hom i).symm
  have hν : IsPullback (ν.inv ≫ pullback.fst f.fromNormalization i)
      PA.obj.hom f.fromNormalization i :=
    IsPullback.of_iso_pullback
      ⟨by rw [Category.assoc, pullback.condition, ← Category.assoc, ha]⟩ ν.symm rfl ha
  have hZ := ((IsPullback.of_hasPullback Z.π (b ≫ sη)).paste_horiz hψ).paste_horiz hν
  have hN := (IsPullback.of_hasPullback n (t ≫ τ)).paste_horiz
    (IsPullback.of_hasPullback f.fromNormalization l)
  have hZ' : IsPullback
      ((pullback.fst Z.π (b ≫ sη) ≫ ψ) ≫
        (ν.inv ≫ pullback.fst f.fromNormalization i))
      (pullback.snd Z.π (b ≫ sη)) f.fromNormalization ((t ≫ τ) ≫ l) := by
    rw [hbase]
    exact hZ
  let β := hN.isoIsPullback _ _ hZ'
  exact ⟨b, β, hN.isoIsPullback_hom_snd _ _ hZ'⟩



end AlgebraicGeometry.Scheme
