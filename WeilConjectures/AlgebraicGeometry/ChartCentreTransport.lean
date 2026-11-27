/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.ConormalAlgebraFlatBaseChange
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalRegularPureCodimension
public import WeilConjectures.AlgebraicGeometry.Purity.PurityNormalProjection
public import WeilConjectures.AlgebraicGeometry.RelativeTangentBundle.RelativeTangentBundle
public import WeilConjectures.AlgebraicGeometry.ChartNormalDifferential.ChartNormalDifferential
public import WeilConjectures.AlgebraicGeometry.DiagonalConormalDifferentials
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
import all WeilConjectures.AlgebraicGeometry.ChartNormalDifferential.ChartNormalDifferential
import all WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.ConormalAlgebraFlatBaseChange
import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator

/-!
# Centred diagonal neighbourhood and its differential under an étale source map

## Implementation details

The graded, normal and tangent comparisons come from the chart comparison of
`ChartNormalDifferential`. Its difference and normal/tangent identifications live on the
full diagonal; they are moved to the open neighbourhood `O` along the canonical degree-one
conormal comparison of the open immersion `O.ι`, which is invertible because `O.ι` is flat.

## References

* Stacks Project, Tags 02GE, 0473, 0635 and 08S2
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ChartNormalDifferential

attribute [local irreducible] Scheme.Modules.tensorPullback
  ConormalGradedAlgebra.presentation PurityNormalBundle.normalCone
  RelativeTangentBundle.scheme PurityNormalBundle.projection
  RelativeTangentBundle.projection PurityNormalBundle.zeroSection
  RelativeTangentBundle.zeroSection Scheme.Hom.relativeDifferentials

namespace AlgebraicGeometry

attribute [local instance] ChartNormalDifferential.Comparison.closed

open Scheme.Modules ConormalGradedAlgebra in
/-- The canonical degree-one conormal comparison along an open neighbourhood. -/
private theorem restrictionPiece {U P : Scheme.{u}} (O : P.Opens) (Δ : U ⟶ P)
    (δ : U ⟶ O.toScheme) [IsClosedImmersion Δ] [IsClosedImmersion δ]
    (hδ : δ ≫ O.ι = 𝟙 U ≫ Δ) (hcart : IsLimit (PullbackCone.mk δ (𝟙 U) hδ)) :
    ∃ ε : piece Δ 1 ≅ piece δ 1, ∀ (V : U.Opens) (x : (piece Δ 1).val.obj (op V)),
      ε.hom.app V x = pullbackSection (𝟙 U) _ _ (Classical.choose ((Classical.choose_spec
        (closedImmersion_conormal_functorial δ Δ O.ι (𝟙 U) hδ).2).2)) V x := by
  let D := Classical.choose ((Classical.choose_spec
    (closedImmersion_conormal_functorial δ Δ O.ι (𝟙 U) hδ).2).2)
  have hN := normalizedPieceComparison δ Δ O.ι (𝟙 U) hδ hcart
    (presentation δ) (presentation Δ)
  have hiso := hN.choose_spec.2.2.1
  have hone := hN.choose_spec.2.2.2.2
  have : IsIso D := by
    have h1 := hiso inferInstance 1
    rw [hone] at h1
    exact h1
  let adj := Classical.choose (exists_tensorPullbackAdjunction (𝟙 U))
  have : (tensorPullback (𝟙 U)).IsEquivalence :=
    Functor.isEquivalence_of_iso (Classical.choice (nonempty_tensorPullbackId U)).symm
  let e := adj.unit.app (piece Δ 1) ≫ (pushforward (𝟙 U)).map D ≫
    (pushforwardId U).hom.app _
  have : IsIso e := by infer_instance
  exact ⟨asIso e, fun V x ↦ rfl⟩

open Scheme.Modules ConormalGradedAlgebra in
/-- Representatives are compatible with restriction of ideal-power sections. -/
private theorem representative_restrict {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (n : ℕ) {T T' : X.Opens} (hle : T' ≤ T)
    (a : (power i n).val.obj (op T)) (V : Z.Opens) (hV : V ≤ i ⁻¹ᵁ T') :
    (piece i n).presheaf.map (homOfLE (hV.trans (i.preimage_mono hle))).op
        (representative i n T a) =
      (piece i n).presheaf.map (homOfLE hV).op
        (representative i n T' ((power i n).presheaf.map (homOfLE hle).op a)) := by
  have hn := Hom.app_presheaf_map ((Classical.choose
    (exists_tensorPullbackAdjunction i)).unit.app (power i n)) (homOfLE hle) a
  change _ = (piece i n).presheaf.map (homOfLE hV).op
    (((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app (power i n)).app T'
      ((power i n).presheaf.map (homOfLE hle).op a))
  erw [hn]
  change _ = ((piece i n).presheaf.map (homOfLE (i.preimage_mono hle)).op ≫
    (piece i n).presheaf.map (homOfLE hV).op) (representative i n T a)
  rw [← Functor.map_comp]
  rfl

open Scheme.Modules ConormalGradedAlgebra in
/-- The difference identification restricts to an open neighbourhood of the diagonal. -/
private theorem restrictionDifference {U Y : Scheme.{u}} (h : U ⟶ Y) [IsSeparated h]
    (O : (pullback h h).Opens) (δ : U ⟶ O.toScheme) [IsClosedImmersion δ]
    (hδ : δ ≫ O.ι = 𝟙 U ≫ pullback.diagonal h)
    (ω : h.relativeDifferentials ≅ piece (pullback.diagonal h) 1)
    (hω : IsDifferenceIdentification h (pullback.diagonal h)
      (pullback.fst h h) (pullback.snd h h) ω)
    (ε : piece (pullback.diagonal h) 1 ≅ piece δ 1)
    (hε : ∀ (V : U.Opens) (x : (piece (pullback.diagonal h) 1).val.obj (op V)),
      ε.hom.app V x = pullbackSection (𝟙 U) _ _ (Classical.choose ((Classical.choose_spec
        (closedImmersion_conormal_functorial δ (pullback.diagonal h) O.ι (𝟙 U) hδ).2).2))
          V x) :
    IsDifferenceIdentification h δ (O.ι ≫ pullback.fst h h) (O.ι ≫ pullback.snd h h)
      (ω ≪≫ ε) := by
  intro V T h₁ h₂ hV a s hs
  let Δ := pullback.diagonal h
  let W := (pullback.fst h h) ⁻¹ᵁ V ⊓ (pullback.snd h h) ⁻¹ᵁ V
  have hU : V ≤ Δ ⁻¹ᵁ W := by
    simp only [W, Δ, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage,
      pullback.diagonal_fst, pullback.diagonal_snd, Scheme.Hom.id_preimage, inf_idem, le_refl]
  obtain ⟨sU, hsU⟩ := differenceRepresentative h V a
  have hd := hω V W inf_le_left inf_le_right hU a sU hsU
  have hδW : V ≤ δ ⁻¹ᵁ (O.ι ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, hδ, Category.id_comp]
    exact hU
  obtain ⟨bU, hbU, hcU⟩ := conormalRepresentativeLocal δ Δ O.ι (𝟙 U) hδ _ rfl W sU V
    hδW hU
  let T₀ := T ⊓ O.ι ⁻¹ᵁ W
  have hV₀ : V ≤ δ ⁻¹ᵁ T₀ := by
    simp only [T₀, Scheme.Hom.preimage_inf]
    exact le_inf hV hδW
  have hres : (power δ 1).presheaf.map (homOfLE (inf_le_right : T₀ ≤ O.ι ⁻¹ᵁ W)).op bU =
      (power δ 1).presheaf.map (homOfLE (inf_le_left : T₀ ≤ T)).op s := by
    apply δ.ker.injective_toModulesι_app T₀
    change (powerInclusion δ 1).app T₀ _ = (powerInclusion δ 1).app T₀ _
    rw [Hom.app_presheaf_map, Hom.app_presheaf_map]
    change O.toScheme.presheaf.map _ ((powerInclusion δ 1).app _ bU) =
      O.toScheme.presheaf.map _ ((powerInclusion δ 1).val.app _ s)
    rw [hbU, hs, hsU, map_sub, map_sub, map_sub]
    congr 1
    · rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        ← ConcreteCategory.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE_assoc,
        Scheme.Hom.appLE_map, Scheme.Hom.appLE_map]
    · rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        ← ConcreteCategory.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE_assoc,
        Scheme.Hom.appLE_map, Scheme.Hom.appLE_map]
  have hL : (ω ≪≫ ε).hom.app V (h.relativeDifferentialsDerivation.d a) =
      ε.hom.app V (ω.hom.app V (h.relativeDifferentialsDerivation.d a)) := rfl
  erw [hL, hd, Hom.app_presheaf_map, hε, hcU,
    representative_restrict δ 1 (inf_le_right : T₀ ≤ O.ι ⁻¹ᵁ W) bU V hV₀,
    representative_restrict δ 1 (inf_le_left : T₀ ≤ T) s V hV₀, hres]

open Scheme.Modules ConormalGradedAlgebra in
/-- The normal/tangent identification restricts to an open neighbourhood of the diagonal. -/
private theorem restrictionNormalTangent {U Y : Scheme.{u}} (h : U ⟶ Y) [Smooth h]
    [IsSeparated h] (O : (pullback h h).Opens) (δ : U ⟶ O.toScheme) [IsClosedImmersion δ]
    (hδ : δ ≫ O.ι = 𝟙 U ≫ pullback.diagonal h)
    (ω : h.relativeDifferentials ≅ piece (pullback.diagonal h) 1)
    (tU : PurityNormalBundle.normalCone (pullback.diagonal h) ≅
      RelativeTangentBundle.scheme h)
    (htU : IsNormalTangentIdentification h (pullback.diagonal h) ω tU)
    (cR : (tensorPullback (𝟙 U)).obj
        (presentation (pullback.diagonal h)).algebra.toModule ≅
      (presentation δ).algebra.toModule)
    (hcR : IsBaseChangeMap δ (pullback.diagonal h) O.ι (𝟙 U) hδ (presentation δ)
      (presentation (pullback.diagonal h)) cR.hom)
    (r : PurityNormalBundle.normalCone δ ≅
      PurityNormalBundle.normalCone (pullback.diagonal h))
    (hr : IsSpecMap (𝟙 U) (presentation δ).algebra
      (presentation (pullback.diagonal h)).algebra
      (PurityNormalBundle.projection δ) (PurityNormalBundle.projection (pullback.diagonal h))
      (normalAlgebraIso δ) (normalAlgebraIso (pullback.diagonal h)) r.hom
      (pullbackSection (𝟙 U) _ _ cR.hom))
    (hzero : PurityNormalBundle.zeroSection δ ≫ r.hom =
      PurityNormalBundle.zeroSection (pullback.diagonal h))
    (ε : piece (pullback.diagonal h) 1 ≅ piece δ 1)
    (hε : ∀ (V : U.Opens) (x : (piece (pullback.diagonal h) 1).val.obj (op V)),
      ε.hom.app V x = pullbackSection (𝟙 U) _ _ (Classical.choose ((Classical.choose_spec
        (closedImmersion_conormal_functorial δ (pullback.diagonal h) O.ι (𝟙 U) hδ).2).2))
          V x) :
    IsNormalTangentIdentification h δ (ω ≪≫ ε) (r ≪≫ tU) := by
  obtain ⟨hproj, hz, βU, hβU, hspec⟩ := htU
  have hρ := hcR.choose_spec.choose_spec.1
  have hsec := hcR.choose_spec.choose_spec.2.1
  have hgr := hcR.choose_spec.choose_spec.2.2.1
  have hone := hcR.choose_spec.choose_spec.2.2.2.2.2
  obtain ⟨θ, hθ⟩ := identityAlgebraIso _ _ cR hcR.choose hρ hsec
  refine ⟨?_, ?_, βU ≪≫ θ, ?_, ?_⟩
  · rw [Iso.trans_hom, Category.assoc, hproj]
    simpa using hr.1
  · rw [Iso.trans_hom, ← Category.assoc, hzero, hz]
  · intro V a
    change θ.hom.right.hom.app (op V) (βU.hom.right.hom.app (op V) _) = _
    erw [hβU, hθ, gradedSection (𝟙 U) _ _ cR.hom _ (hgr 1), hone]
    change _ = ((presentation δ).inclusion 1).val.app (op V) (ε.hom.app V (ω.hom.app V a))
    erw [hε]
    rfl
  · obtain ⟨hw, hs⟩ := hspec
    obtain ⟨hwr, hsr⟩ := hr
    refine ⟨by simpa [hw] using hwr, ?_⟩
    intro V a
    have h1 := hs V a
    have h2 := hsr V (βU.hom.right.hom.app (op V) a)
    change (normalAlgebraIso δ).hom.right.hom.app _
      (θ.hom.right.hom.app (op V) (βU.hom.right.hom.app (op V) a)) = _
    rw [hθ]
    erw [h2, h1]
    exact ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE r.hom tU.hom _ _ _ _ _) _

private theorem restrictionIdentification {U A Y : Scheme.{u}} {d : ℕ} {p : A ⟶ Y}
    {e : U ⟶ A} [IsSeparated p] [IsSeparated (e ≫ p)] [Smooth p] [Smooth (e ≫ p)]
    (C : Comparison d p e) :
    ∃ ωV : (e ≫ p).relativeDifferentials ≅ ConormalGradedAlgebra.piece C.δ 1,
      IsDifferenceIdentification (e ≫ p) C.δ (C.O.ι ≫ pullback.fst (e ≫ p) (e ≫ p))
        (C.O.ι ≫ pullback.snd (e ≫ p) (e ≫ p)) ωV ∧
      IsNormalTangentIdentification (e ≫ p) C.δ ωV (C.r ≪≫ C.tU) := by
  have hrcart : IsPullback C.δ (𝟙 U) C.O.ι (pullback.diagonal (e ≫ p)) := by
    apply IsOpenImmersion.isPullback
    · exact C.restriction_square.symm
    · rw [Scheme.Opens.opensRange_ι]
      change (pullback.diagonal (e ≫ p)) ⁻¹ᵁ C.O = (𝟙 U : U ⟶ U).opensRange
      rw [← C.diagonal_factorization, Scheme.Hom.comp_preimage]
      ext x
      simp
  obtain ⟨ε, hε⟩ := restrictionPiece C.O _ C.δ C.restriction_square hrcart.isLimit
  exact ⟨C.ωU ≪≫ ε, restrictionDifference (e ≫ p) C.O C.δ C.restriction_square C.ωU
    C.difference_U ε hε, restrictionNormalTangent (e ≫ p) C.O C.δ C.restriction_square C.ωU
    C.tU C.tangent_U C.restriction C.graded_restriction C.r C.restriction_spec
    C.restriction_zero ε hε⟩

/-- The canonical centred-neighbourhood transport, including its graded and tangent maps.
(Stacks, Tags 02GE, 0473, 0635 and 08S2). -/
theorem chart_centre_transport (k : Type u) [Field k]
    {X Y V : Scheme.{u}}
    (aX : X ⟶ Spec (CommRingCat.of k))
    (aY : Y ⟶ Spec (CommRingCat.of k))
    (aV : V ⟶ Spec (CommRingCat.of k))
    [IsSeparated aX] [IsSeparated aY] [IsSeparated aV]
    [LocallyOfFiniteType aX] [LocallyOfFiniteType aY] [LocallyOfFiniteType aV]
    [QuasiCompact aX] [QuasiCompact aY] [QuasiCompact aV]
    (g : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d g]
    (hgk : g ≫ aY = aX)
    (uV : V ⟶ X) [Etale uV]
    (huVk : uV ≫ aX = aV)
    (h : V ⟶ Y) (hh : h = uV ≫ g) :
    ∃ (a : pullback h g ⟶ pullback.diagonalObj g)
      (_ : a = pullback.map h g g g uV (𝟙 X) (𝟙 Y) (by simp [hh]) (by simp))
      (b : pullback.diagonalObj h ⟶ pullback h g)
      (_ : b = pullback.map h h h g (𝟙 V) uV (𝟙 Y) (by simp) (by simp [hh]))
      (s : V ⟶ pullback h g)
      (_ : s = pullback.lift (𝟙 V) uV (by simp [hh])),
      IsPullback a (pullback.fst h g) (pullback.fst g g) uV ∧
      IsPullback s uV a (pullback.diagonal g) ∧
      ∃ (O : (pullback.diagonalObj h).Opens) (iO : V ⟶ O.toScheme)
          (hIO : IsClosedImmersion iO)
          (_ : iO ≫ O.ι = pullback.diagonal h),
        O.1 =
          (Set.range (pullback.map uV uV h h (𝟙 V) (𝟙 V) g
            (by simp [hh]) (by simp [hh])) \ Set.range (pullback.diagonal h))ᶜ ∧
        Set.range (pullback.diagonal h) ⊆ O.1 ∧
        IsClosedImmersion
          (pullback.map uV uV h h (𝟙 V) (𝟙 V) g (by simp [hh]) (by simp [hh])) ∧
        IsOpenImmersion (pullback.diagonal uV) ∧
        IsClosedImmersion (pullback.diagonal uV) ∧
        IsPullback iO (𝟙 V) (O.ι ≫ b) s ∧
        IsPullback iO uV (O.ι ≫ b ≫ a) (pullback.diagonal g) ∧
        Etale (O.ι ≫ b) ∧ IsSeparated (O.ι ≫ b) ∧
        Etale (O.ι ≫ b ≫ a) ∧ IsSeparated (O.ι ≫ b ≫ a) ∧
        ∃ (hg : IsSeparated g),
          letI : IsSeparated g := hg
          letI : IsClosedImmersion (pullback.diagonal g) := inferInstance
          letI : IsClosedImmersion iO := hIO
          letI : Smooth g := SmoothOfRelativeDimension.smooth d g
          letI : Smooth (uV ≫ g) := inferInstance
          let Ag := ConormalGradedAlgebra.presentation (pullback.diagonal g)
          let Ah := ConormalGradedAlgebra.presentation iO
          ∃ (hcomp : iO ≫ O.ι ≫ b ≫ a = uV ≫ pullback.diagonal g)
            (c : (Scheme.Modules.tensorPullback uV).obj Ag.algebra.toModule ≅
              Ah.algebra.toModule),
            ConormalGradedAlgebra.IsBaseChangeMap iO (pullback.diagonal g)
              (O.ι ≫ b ≫ a) uV hcomp Ah Ag c.hom ∧
            ∃ (ωV : (uV ≫ g).relativeDifferentials ≅ ConormalGradedAlgebra.piece iO 1)
              (ωX : g.relativeDifferentials ≅
                ConormalGradedAlgebra.piece (pullback.diagonal g) 1)
              (tV : PurityNormalBundle.normalCone iO ≅
                RelativeTangentBundle.scheme (uV ≫ g))
              (tX : PurityNormalBundle.normalCone (pullback.diagonal g) ≅
                RelativeTangentBundle.scheme g)
              (ν : PurityNormalBundle.normalCone iO ⟶
                PurityNormalBundle.normalCone (pullback.diagonal g))
              (du : RelativeTangentBundle.scheme (uV ≫ g) ⟶
                RelativeTangentBundle.scheme g),
              IsDifferenceIdentification (uV ≫ g) iO
                (O.ι ≫ pullback.fst h h) (O.ι ≫ pullback.snd h h) ωV ∧
              IsDifferenceIdentification g (pullback.diagonal g)
                (pullback.fst g g) (pullback.snd g g) ωX ∧
              IsNormalTangentIdentification (uV ≫ g) iO ωV tV ∧
              IsNormalTangentIdentification g (pullback.diagonal g) ωX tX ∧
              IsSpecMap uV Ah.algebra Ag.algebra
                (PurityNormalBundle.projection iO)
                (PurityNormalBundle.projection (pullback.diagonal g))
                (normalAlgebraIso iO) (normalAlgebraIso (pullback.diagonal g)) ν
                (pullbackSection uV Ah.algebra.toModule Ag.algebra.toModule c.hom) ∧
              IsPullback ν (PurityNormalBundle.projection iO)
                (PurityNormalBundle.projection (pullback.diagonal g)) uV ∧
              PurityNormalBundle.zeroSection iO ≫ ν =
                uV ≫ PurityNormalBundle.zeroSection (pullback.diagonal g) ∧
              IsDifferential g uV du ∧
              IsPullback du (RelativeTangentBundle.projection (uV ≫ g))
                (RelativeTangentBundle.projection g) uV ∧
              RelativeTangentBundle.zeroSection (uV ≫ g) ≫ du =
                uV ≫ RelativeTangentBundle.zeroSection g ∧
              ν ≫ tX.hom = tV.hom ≫ du := by
  classical
  subst hh
  have : IsSeparated (g ≫ aY) := hgk ▸ inferInstance
  have : IsSeparated g := IsSeparated.of_comp g aY
  have : LocallyOfFiniteType (g ≫ aY) := hgk ▸ inferInstance
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g aY
  have : QuasiCompact (g ≫ aY) := hgk ▸ inferInstance
  have : QuasiCompact g := QuasiCompact.of_comp g aY
  have : IsSeparated (uV ≫ aX) := huVk ▸ inferInstance
  have : IsSeparated uV := IsSeparated.of_comp uV aX
  have : QuasiCompact (uV ≫ aX) := huVk ▸ inferInstance
  have : QuasiCompact uV := QuasiCompact.of_comp uV aX
  have : IsSeparated ((uV ≫ g) ≫ aY) := by
    rw [Category.assoc, hgk, huVk]
    infer_instance
  have : IsSeparated (uV ≫ g) := IsSeparated.of_comp (uV ≫ g) aY
  have : SmoothOfRelativeDimension d (uV ≫ g) := by
    simpa using (inferInstance : SmoothOfRelativeDimension (0 + d) (uV ≫ g))
  have : Smooth g := SmoothOfRelativeDimension.smooth d g
  have : Smooth (uV ≫ g) := inferInstance
  have := LocallyOfFiniteType.isLocallyNoetherian aY
  have := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := {}
  have := LocallyOfFiniteType.isLocallyNoetherian aX
  have := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := {}
  have := LocallyOfFiniteType.isLocallyNoetherian aV
  have := QuasiCompact.compactSpace_of_compactSpace aV
  have : IsNoetherian V := {}
  obtain ⟨C⟩ := comparisonOfChart aY d g uV
  obtain ⟨ωV, hωV, htV⟩ := restrictionIdentification C
  let a := pullback.map (uV ≫ g) g g g uV (𝟙 X) (𝟙 Y) (by simp) (by simp)
  let b := pullback.map (uV ≫ g) (uV ≫ g) (uV ≫ g) g (𝟙 V) uV (𝟙 Y) (by simp) (by simp)
  let s : V ⟶ pullback (uV ≫ g) g := pullback.lift (𝟙 V) uV (by simp)
  have ha : IsPullback a (pullback.fst (uV ≫ g) g) (pullback.fst g g) uV :=
    (isPullback_pullback_map_left uV g g).flip
  have hsq : IsPullback s uV a (pullback.diagonal g) :=
    (pullback_lift_diagonal_isPullback uV g).flip
  have hb : IsPullback b (pullback.snd _ _) (pullback.snd _ _) uV :=
    isPullback_pullback_map (uV ≫ g) (uV ≫ g) g uV rfl
  have hba :
      pullback.map (uV ≫ g) (uV ≫ g) g g uV uV (𝟙 Y) (by simp) (by simp) = b ≫ a := by
    ext <;> simp [a, b]
  have hq : C.q = C.O.ι ≫ b ≫ a := by rw [C.q_eq, hba]
  have hcomp : C.δ ≫ C.O.ι ≫ b ≫ a = uV ≫ pullback.diagonal g := by
    rw [← hq]
    exact C.square
  have hout : IsPullback C.δ uV (C.O.ι ≫ b ≫ a) (pullback.diagonal g) := by
    rw [← hq]
    exact IsPullback.of_isLimit C.cartesian
  have hds : pullback.diagonal (uV ≫ g) ≫ b = s := by
    ext <;> simp [b, s]
  have : Etale b := MorphismProperty.of_isPullback hb.flip inferInstance
  have : IsSeparated b := MorphismProperty.of_isPullback hb.flip inferInstance
  have : IsSeparated a := MorphismProperty.of_isPullback ha.flip inferInstance
  have hEt : Etale (C.O.ι ≫ b ≫ a) := by
    rw [← hq]
    exact C.etale
  have hbc : ∀ (q' : C.O.toScheme ⟶ pullback g g) (_ : q' = C.q)
      (hs' : C.δ ≫ q' = uV ≫ pullback.diagonal g),
      ConormalGradedAlgebra.IsBaseChangeMap C.δ (pullback.diagonal g) q' uV hs'
        (ConormalGradedAlgebra.presentation C.δ)
        (ConormalGradedAlgebra.presentation (pullback.diagonal g)) C.c.hom := by
    rintro q' rfl hs'
    exact C.graded_comparison
  have hzero : RelativeTangentBundle.zeroSection (uV ≫ g) ≫ C.de =
      uV ≫ RelativeTangentBundle.zeroSection g := by
    have h1 := C.tangent_U.2.1
    have h2 := C.tangent_A.2.1
    have h3 := C.restriction_zero
    have h4 := C.zero_section
    have h5 := C.normal_is_differential
    rw [← h1, Category.assoc, ← h5, ← h3, Category.assoc, Iso.hom_inv_id_assoc,
      reassoc_of% h4, h2]
  refine ⟨a, rfl, b, rfl, s, rfl, ha, hsq, C.O, C.δ, C.closed,
    C.diagonal_factorization, C.open_set, ?_, ?_, inferInstance, inferInstance,
    IsPullback.of_bot (by simpa using hout) (by
      rw [← Category.assoc, C.diagonal_factorization, hds, Category.id_comp]) hsq,
    hout, inferInstance, inferInstance, hEt, inferInstance, inferInstance, ?_⟩
  · rintro _ ⟨x, rfl⟩
    rw [← C.diagonal_factorization]
    exact (C.δ x).2
  · exact MorphismProperty.of_isPullback
      (pullback_map_diagonal_isPullback uV uV g).flip.flip inferInstance
  · refine ⟨hcomp, C.c, hbc _ hq.symm _, ωV, C.ωA, C.r ≪≫ C.tU, C.tA,
      C.ν, C.de, hωV, C.difference_A, htV, C.tangent_A, C.normal_spec,
      C.normal_cartesian, C.zero_section, C.differential, C.differential_cartesian,
      hzero, ?_⟩
    rw [Iso.trans_hom, Category.assoc, ← C.normal_is_differential, Iso.hom_inv_id_assoc]

end AlgebraicGeometry
