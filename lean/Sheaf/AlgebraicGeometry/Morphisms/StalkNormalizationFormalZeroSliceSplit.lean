/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
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

public import Mathlib.RingTheory.MvPowerSeries.Basic

import Sheaf.AlgebraicGeometry.Morphisms.GenericFibreActionExtension
import Sheaf.AlgebraicGeometry.Morphisms.NormalIntegralGenericHomFull
import Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFormalPuncturedRestriction

/-! # Splitting the zero slice of the fixed formal test

Source: Stacks Project, Tags 0EYJ and 0EY9.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option autoImplicit false

/-- The normalization test is split on the zero slice of its punctured open.
This only gives an isomorphism after pulling back to the zero slice.

Source: Stacks Project, Tag 0EYJ (the rational section point and extended action);
Tag 0BQM (full faithfulness over a normal integral base).
(blueprint: lem-sbc-stalk-normalization-formal-zero-slice-split)

Proof: Minimality identifies the inverse image of U with the punctured spectrum
of the normal local ring A = O_{S,s}. On this open relative normalization
agrees with PA: PA is finite, hence integral, over C_U, and normalization
commutes with smooth base change along the open inclusion.
Extend the generic G-action to PA using generic-fibre full faithfulness.
Pull back along the given section on this punctured local base. The rational
point over the generic section and its G-translates give an isomorphism of
its generic fibre with the constant G-indexed cover: simple transitivity
makes the translates distinct and exhaustive. On the normal integral
punctured local base, extend that generic isomorphism and its inverse using
full faithfulness of finite etale restriction to the generic point (0BQM).
Uniqueness checks both inverse identities. The base compatibility of t and
its entire zero-section compatibility identify the zero slice of V with
this punctured base, and identify the pulled-back normalization cover with
the section pullback of PA. Pullback of the constant coproduct commutes with
this restriction. Transport the section-cover isomorphism through these
canonical pullback comparisons to get the displayed finite etale isomorphism.
This argument applies to zero variables and to disconnected torsors; it
makes no assertion about the cover away from the zero slice. -/
theorem GaloisCover.stalk_normalization_formal_zero_slice_split {S C : Scheme.{u}}
    [IsNoetherian S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S)
    (G : Type (u + 1)) [Group G] [Finite G]
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (sη : Spec S.functionField ⟶ Cη) (hsq : sη ≫ q = 𝟙 _)
    (hsj : sη ≫ j = S.fromSpecStalk (genericPoint S) ≫ σ)
    (Z : GaloisCover G Cη) (hZ : ∃ z : Spec S.functionField ⟶ Z.P, z ≫ Z.π = sη)
    (U : S.Opens) (hηU : genericPoint S ∈ U)
    (jU : Cη ⟶ (c ⁻¹ᵁ U).toScheme) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (ψ : Z.P ⟶ PA.obj.left) (hjU : jU ≫ (c ⁻¹ᵁ U).ι = j)
    (hψ : IsPullback ψ Z.π PA.obj.hom jU)
    (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s)
    :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let a := S.fromSpecStalk s
    let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
    let τ : Spec (S.presheaf.stalk s) ⟶ pullback c a :=
      pullback.lift (a ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])
    ∀ (d : ℕ)
      (t : Spec (.of (MvPowerSeries (Fin d) (S.presheaf.stalk s))) ⟶ pullback c a),
      t ≫ pullback.snd c a =
        Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin d))) →
      Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d))) ≫ t = τ →
      let T := Spec (.of (MvPowerSeries (Fin d) (S.presheaf.stalk s)))
      let F : Scheme.{u} := pullback n t
      let E : Scheme.{u} := ∐ (fun _ : G ↦ T)
      let V := (t ≫ pullback.fst c a) ⁻¹ᵁ (c ⁻¹ᵁ U)
      let r : F ⟶ T := pullback.snd n t
      let p : E ⟶ T := Sigma.desc (fun _ : G ↦ 𝟙 T)
      let z := (Spec.map (CommRingCat.ofHom
        (MvPowerSeries.constantCoeff (σ := Fin d)))) ∣_ V
      ∃ e : pullback (p ∣_ V) z ≅ pullback (r ∣_ V) z,
        e.hom ≫ pullback.snd (r ∣_ V) z = pullback.snd (p ∣_ V) z := by sorry

end AlgebraicGeometry.Scheme
