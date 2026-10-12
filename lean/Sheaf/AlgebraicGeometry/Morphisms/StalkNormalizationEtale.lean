/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
public import Mathlib.AlgebraicGeometry.Normalization

/-!
# Etaleness of the finite normalization over a stalk

Source: Stacks Project, Tag 0EYJ, proof of the local claim.
(blueprint: lem-sbc-stalk-normalization-etale)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Local affine-chart form of the stalk normalization claim.

Source: Stacks Project, Tag 0EYJ, local claim.  The missing argument is the
identification of the normalization with the split extension on every affine
chart of the stalk; once that identification is available, the `Etale`
structure is obtained by checking its defining affine ring maps.
(blueprint: lem-sbc-stalk-normalization-etale-local-charts)
-/
theorem GaloisCover.stalk_normalization_etale_local_charts {S C : Scheme.{u}} [IsNoetherian S]
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
    (Z : GaloisCover G Cη) (hZ : ∃ z : Spec S.functionField ⟶ Z.P, z ≫ Z.π = sη)
    (U : S.Opens) (hηU : genericPoint S ∈ U)
    (jU : Cη ⟶ (c ⁻¹ᵁ U).toScheme) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (ψ : Z.P ⟶ PA.obj.left) (hjU : jU ≫ (c ⁻¹ᵁ U).ι = j)
    (hψ : IsPullback ψ Z.π PA.obj.hom jU)
    (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    IsFinite (pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
      (pullback.fst c (S.fromSpecStalk s))) →
    ∀ {V : (pullback c (S.fromSpecStalk s)).Opens} (_ : IsAffineOpen V)
      {W : (pullback (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
        (pullback.fst c (S.fromSpecStalk s))).Opens} (_ : IsAffineOpen W)
      (e : W ≤ (pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
        (pullback.fst c (S.fromSpecStalk s))) ⁻¹ᵁ V),
      ((pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
        (pullback.fst c (S.fromSpecStalk s))).appLE V W e).hom.Etale := by sorry

/-- Etaleness of the finite normalization at a generic boundary point.

Source: Stacks Project, Tag 0EYJ (pione-lemma-extend-covering), local claim;
Tags 0EYI, 0EYE, 0EY9 and 0EYB.
(blueprint: lem-sbc-stalk-normalization-etale)

Proof: Localize at s. Its minimality makes U the punctured local spectrum.
The finite model in the premise is the actual integral closure of the local
total space in the given punctured finite etale algebra; localization commutes
with this construction. Generic full faithfulness extends the G-action and
identifies the section fibre on the punctured base with the split G-cover:
the rational generic point and its translates give that splitting generically,
and normal generic full faithfulness extends it.
In dimension one the local base is a DVR. The tame normal form and split
section test 0EYI give etaleness near the section. The smooth connected special
fibre is geometrically integral, so this neighbourhood contains its generic
point. Purity across its regular Cartier divisor, 0EYE, gives etaleness on the
whole fibre. The finite normalization agrees with this etale extension.
In dimension at least two, normality and flatness give depth at least two
along the missing fibre. The normalization is the unique depth-two extension
of 0EY6. Complete an affine smooth neighbourhood of the section in its section
ideal. This is a power series ring over the local base, and completion is flat.
The section splitting and power series full faithfulness 0EY9 split the cover
on the punctured completion. Uniqueness and flat base change for the depth-two
extension split the completed finite model. Flat descent gives etaleness at
the generic point of the special fibre, and the fibre criterion 0EYB gives
etaleness on the entire special fibre. It was already etale off this fibre.
For disconnected torsors apply the argument to stabilizer covers and induce
back to G; stabilizer orders divide the invertible order of G. -/
theorem GaloisCover.stalk_normalization_etale {S C : Scheme.{u}} [IsNoetherian S]
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
    (Z : GaloisCover G Cη) (hZ : ∃ z : Spec S.functionField ⟶ Z.P, z ≫ Z.π = sη)
    (U : S.Opens) (hηU : genericPoint S ∈ U)
    (jU : Cη ⟶ (c ⁻¹ᵁ U).toScheme) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (ψ : Z.P ⟶ PA.obj.left) (hjU : jU ≫ (c ⁻¹ᵁ U).ι = j)
    (hψ : IsPullback ψ Z.π PA.obj.hom jU)
    (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    IsFinite (pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
      (pullback.fst c (S.fromSpecStalk s))) →
    Etale (pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
      (pullback.fst c (S.fromSpecStalk s))) := by
  let : IsFinite PA.obj.hom := PA.property
  let : QuasiCompact (c ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
      (inferInstance : QuasiCompact U.ι)
  intro hfin
  refine ⟨?_⟩
  exact GaloisCover.stalk_normalization_etale_local_charts hS c σ hσ G hG q j hCη sη hsq hsj Z hZ
    U hηU jU PA ψ hjU hψ s hs hmin hfin

end AlgebraicGeometry.Scheme
