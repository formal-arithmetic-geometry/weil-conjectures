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
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import Mathlib.AlgebraicGeometry.Normalization

import Sheaf.RingTheory.NormalLocalDepthTwo
import Sheaf.RingTheory.FlatLocalDepthFormula
import Sheaf.AlgebraicGeometry.Morphisms.NormalIntegralGenericHomFull
import Sheaf.AlgebraicGeometry.Morphisms.GenericFibreActionExtension

/-!
# Etaleness near the local section of a normalization

Source: Stacks Project, Tag 0EYJ, local computation; Tags 0EYI and 0EY9.
(blueprint: lem-sbc-stalk-normalization-section-neighbourhood)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The section meets an open over which the finite local normalization is etale.

Source: Stacks Project, Tag 0EYJ (pione-lemma-extend-covering), formal section
calculation; Tag 0EYI (split-section trait test), Tag 0EY9 (power series
full faithfulness), and Tag 0EY6 (flat base change for the depth-two extension).
(blueprint: lem-sbc-stalk-normalization-section-neighbourhood)

Proof: After localization at s, the complement is the closed point of the
normal Noetherian local base A. Smoothness makes the total space normal.
Extend the action on the punctured cover by generic full faithfulness.
The rational point and the torsor action split its generic section fibre;
normal generic full faithfulness extends this splitting over the punctured
section. If A has dimension one, A is a DVR. Tame normalization gives the
standard local ramification forms, and the split-section test forces their
exponents to be one near the section. If A has dimension at least two,
normality gives depth at least two, and flatness propagates it to the total
space. The finite normalization is the unique depth-two extension: its normal
finite algebra equals the pushforward of the punctured algebra. Complete a
smooth affine chart at the section ideal; its completion is a power series
ring over A. Full faithfulness on the punctured power series scheme identifies
the cover with the split cover, because their restrictions to the section
are split. For relative dimension zero this identification is immediate.
Uniqueness and flat base change of the depth-two extension identify the
completed normalization with the split finite algebra. Completion is flat
and faithfully flat at the section point, so etaleness descends there.
As the normalization is finite over a Noetherian scheme, its non-etale locus
has closed image. The complementary target open is the required W.
The argument applies to each component, with stabilizer orders dividing |G|;
an empty finite algebra gives an empty etale cover and causes no exception. -/
theorem GaloisCover.stalk_normalization_section_neighbourhood {S C : Scheme.{u}} [IsNoetherian S]
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
    let a := S.fromSpecStalk s
    let τ : Spec (S.presheaf.stalk s) ⟶ pullback c a :=
      pullback.lift (a ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])
    ∃ W : (pullback c a).Opens,
      τ (IsLocalRing.closedPoint (S.presheaf.stalk s)) ∈ W ∧
      Etale ((pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
        (pullback.fst c a)) ∣_ W) := by sorry

end AlgebraicGeometry.Scheme
