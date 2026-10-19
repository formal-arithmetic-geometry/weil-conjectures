/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
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

public import WeilConjectures.RingTheory.Depth

public import Mathlib.RingTheory.MvPowerSeries.Basic

import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoFiniteExtensionUniqueness
import WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationFormalBoundaryDepths
import WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationFormalPuncturedSplit
import Mathlib.RingTheory.MvPowerSeries.Equiv
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Splitting the normalization on a compatible power-series test

Source: Stacks Project, Tag 0EYJ, final splitting paragraphs; Tags 0EY6 and 0EY9.
(blueprint: lem-sbc-stalk-normalization-formal-split)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A fixed flat power-series test, compatible with the local base and the entire
section, splits the finite normalization. This does not construct the test.

Source: Stacks Project, Tag 0EYJ, final splitting paragraphs; Tags 0EY6 and 0EY9.
https://stacks.math.columbia.edu/tag/0EYJ
(blueprint: lem-sbc-stalk-normalization-formal-split)

Proof: Let A be the base stalk and L the local total space. Minimality identifies
its base open with Spec A minus the closed point. Normality of the base and
smoothness make L normal. The normalization restricts to PA on this open.
Going down over normal domains and the flat local depth formula put its boundary
points in codimension at least two. Normal S2 then gives boundary depth at least
two. Tag 0EY6(2) identifies it with the unique finite depth-two extension of PA.
Extend the generic G-action to PA by generic-fibre full faithfulness. The given
rational point and its translates split the generic section cover into exactly
G copies. Normal generic full faithfulness extends the isomorphism and its
inverse over the punctured local base. The base compatibility of t identifies
the inverse image V of that open with the punctured-base open of Spec A[[X]].
The entire-section compatibility identifies its zero slice with the section on
the punctured base, so the cover is split on that slice. For d positive, Tag
0EY9 lifts both directions of this splitting to V; faithfulness shows the two
composites are identities. For d zero the slice is already V. Flat base change
preserves the unique depth-two extension by 0EY6(a). The split finite cover of
the whole power-series spectrum has boundary depth at least two, by flatness
over A and the depth hypothesis. Uniqueness in 0EY6(2) extends the splitting
from V to the whole test and gives the displayed equation over the test.
No choice of chart or arbitrary witness is used to define data. The trivial
group gives one copy; disconnected torsors and zero variables are included. -/
theorem GaloisCover.exists_stalk_normalization_formal_split {S C : Scheme.{u}}
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
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth
      (R := S.presheaf.stalk s) (S.presheaf.stalk s)) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let a := S.fromSpecStalk s
    let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
    let τ : Spec (S.presheaf.stalk s) ⟶ pullback c a :=
      pullback.lift (a ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])
    IsFinite n → ∀ (d : ℕ)
      (t : Spec (.of (MvPowerSeries (Fin d) (S.presheaf.stalk s))) ⟶ pullback c a),
      Flat t →
      t ≫ pullback.snd c a =
        Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin d))) →
      Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d))) ≫ t = τ →
      ∃ e : pullback n t ≅
        ∐ (fun _ : G ↦ Spec (.of (MvPowerSeries (Fin d) (S.presheaf.stalk s)))),
        e.hom ≫ Sigma.desc (fun _ : G ↦ 𝟙 _) = pullback.snd n t := by
  let : IsFinite PA.obj.hom := PA.property
  let : QuasiCompact (c ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
      (inferInstance : QuasiCompact U.ι)
  dsimp only
  intro hn d t ht hb hz
  let : IsFinite (pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
      (pullback.fst c (S.fromSpecStalk s))) := hn
  obtain ⟨hr, hp⟩ := GaloisCover.stalk_normalization_formal_boundary_depths
    hS c G U PA s hmin hdepth hn d t ht hb
  obtain ⟨e, he⟩ := GaloisCover.exists_stalk_normalization_formal_punctured_split
    hS c σ hσ G q j hCη sη hsq hsj Z hZ U hηU jU PA ψ hjU hψ
    s hs hmin hdepth hn d t ht hb hz
  exact iso_of_finite_depth_two_extensions _ _ _ hr hp e he

end AlgebraicGeometry.Scheme
