/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
import WeilConjectures.AlgebraicGeometry.QuasiCompactOpenQuasiAffineChartDescent
import WeilConjectures.AlgebraicGeometry.QcOpenPullbackQuasiAffineEnlargement
import WeilConjectures.AlgebraicGeometry.SeparatedAffinePairNeighbourhoods

/-!
# Permanence and separation for ind-quasi-affine morphisms

Source: Stacks Project, More on Morphisms, Tags 0AP6, 0F1U and 0AP7
(blueprint: lem-a1-ind-quasi-affine-permanence).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- The condition that every quasi-compact open over an affine target open is quasi-affine.

Source: Stacks Project, More on Morphisms, Tags 0AP6 and 0F1U
(blueprint: lem-a1-ind-quasi-affine-permanence).
-/
def indQuasiAffineProperty {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ (U : Y.Opens), IsAffineOpen U →
    ∀ (K : (Limits.pullback f U.ι).Opens),
      IsCompact (K : Set (Limits.pullback (C := Scheme.{u}) f U.ι)) →
        IsQuasiAffineHom (K.ι ≫ Limits.pullback.snd f U.ι)

private def qcOpensQuasiAffine (X : Scheme.{u}) : Prop :=
  ∀ K : X.Opens, IsCompact (K : Set X) → K.toScheme.IsQuasiAffine

private theorem qcOpensQuasiAffine_of_openImmersion {X Y : Scheme.{u}} (i : X ⟶ Y)
    [IsOpenImmersion i] (hY : qcOpensQuasiAffine Y) : qcOpensQuasiAffine X := by
  intro K hK
  have : (i ''ᵁ K).toScheme.IsQuasiAffine :=
    hY (i ''ᵁ K) (hK.image i.continuous)
  exact Scheme.IsQuasiAffine.of_isIso (i.isoImage K).hom

private def qcOpensAffineProperty : AffineTargetMorphismProperty.{u} :=
  fun X _ _ _ ↦ qcOpensQuasiAffine X

private instance qcOpensAffineProperty_respectsIso :
    qcOpensAffineProperty.toProperty.RespectsIso := by
  apply AffineTargetMorphismProperty.respectsIso_mk
  · intro X Y Z e f _ h
    exact qcOpensQuasiAffine_of_openImmersion e.hom h
  · intro X Y Z e f _ h
    exact h

private theorem qcOpensQuasiAffine_of_affine_charts {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) {I : Type v} (U : I → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)
    (hlocal : ∀ i, qcOpensQuasiAffine (f ⁻¹ᵁ U i).toScheme) :
    qcOpensQuasiAffine X := by
  have : IsAffine (⊤ : Y.Opens).toScheme := isAffineOpen_top Y
  have htop : qcOpensQuasiAffine (f ⁻¹ᵁ (⊤ : Y.Opens)).toScheme := by
    intro K hK
    exact (isQuasiAffineHom_quasiCompact_open_of_affine_charts f U hU hcover
      hlocal ⊤ isCompact_univ K hK).2 (isAffineOpen_top Y)
  let e : (f ⁻¹ᵁ (⊤ : Y.Opens)).toScheme ≅ X :=
    X.isoOfEq (by simp) ≪≫ X.topIso
  exact qcOpensQuasiAffine_of_openImmersion e.inv htop

private instance qcOpensAffineProperty_isLocal : qcOpensAffineProperty.IsLocal where
  respectsIso := inferInstance
  to_basicOpen {X Y} _ f r h := qcOpensQuasiAffine_of_openImmersion (f ⁻¹ᵁ _).ι h
  of_basicOpenCover {X Y} _ f s hs h := by
    apply qcOpensQuasiAffine_of_affine_charts f (fun r : s ↦ Y.basicOpen r.1)
    · intro r
      exact (isAffineOpen_top Y).basicOpen r.1
    · exact (isAffineOpen_top Y).iSup_basicOpen_eq_self_iff.mpr hs
    · exact h

private theorem indQuasiAffineProperty_iff (X Y : Scheme.{u}) (f : X ⟶ Y) :
    indQuasiAffineProperty f ↔ targetAffineLocally qcOpensAffineProperty f := by
  constructor
  · intro hf U
    have : IsAffine U.1.toScheme := U.2
    apply qcOpensQuasiAffine_of_openImmersion (pullbackRestrictIsoRestrict f U.1).inv
    intro K hK
    have := hf U.1 U.2 K hK
    exact Scheme.IsQuasiAffine.of_isQuasiAffineHom (K.ι ≫ pullback.snd f U.1.ι)
  · intro hf U hU K hK
    have : IsAffine U.toScheme := hU
    have h := qcOpensQuasiAffine_of_openImmersion
      (pullbackRestrictIsoRestrict f U).hom (hf ⟨U, hU⟩) K hK
    have : K.toScheme.IsQuasiAffine := h
    infer_instance

private instance indQuasiAffineProperty_hasAffineProperty :
    HasAffineProperty @indQuasiAffineProperty qcOpensAffineProperty where
  isLocal_affineProperty := inferInstance
  eq_targetAffineLocally' := by
    ext X Y f
    exact indQuasiAffineProperty_iff X Y f

private theorem qcOpensAffineProperty_baseChange :
    qcOpensAffineProperty.IsStableUnderBaseChange := by
  apply AffineTargetMorphismProperty.IsStableUnderBaseChange.mk
  intro B X A _ _ b a hX
  have h : qcOpensQuasiAffine (pullback a b) := by
    intro L hL
    obtain ⟨n, Wj, W, _, _, _, _, _, h, _⟩ :=
      qc_open_pullback_quasi_affine_enlargement a b hX L hL
    exact h
  exact qcOpensQuasiAffine_of_openImmersion (pullbackSymmetry b a).hom h

/-- Ind-quasi-affineness is stable under arbitrary base change, local on an affine open
cover of the target, and implies quasi-affineness of quasi-compact opens and separatedness
when the target is affine.

Source: Stacks Project, More on Morphisms, Tags 0AP6, 0F1U and 0AP7
(blueprint: lem-a1-ind-quasi-affine-permanence).

Proof:
1. Translate between quasi-affine morphisms to affine schemes and quasi-affine source schemes,
   using the recorded quasi-affine morphism definition and affine-scheme compactness.
2. For an affine open cover of the target, restrict a quasi-compact open to affine members of
   the cover and apply the affine-cover criterion for ordinary quasi-affineness.
3. For an arbitrary base change, cover the base by affine opens, enlarge each projected
   quasi-compact open to a finite union of affine opens, and apply ordinary quasi-affine
   base-change stability.
4. Over an affine target, quasi-compact opens are quasi-affine; unions of affine opens are
   quasi-affine and separated, and the absolute diagonal is checked on the resulting target
   cover. Separatedness implies quasi-separatedness.
-/
theorem indQuasiAffineProperty_permanence {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (∀ (T : Scheme.{u}) (g : T ⟶ Y),
      indQuasiAffineProperty f → indQuasiAffineProperty (Limits.pullback.snd f g)) ∧
    (∀ {I : Type v} (U : I → Y.Opens), (∀ i, IsAffineOpen (U i)) →
      iSup U = ⊤ →
      (indQuasiAffineProperty f ↔
        ∀ i, indQuasiAffineProperty (Limits.pullback.snd f (U i).ι))) ∧
    (∀ (_hY : IsAffine Y), indQuasiAffineProperty f →
      (∀ (K : X.Opens), IsCompact (K : Set X) → K.toScheme.IsQuasiAffine) ∧
        Scheme.IsSeparated X ∧ QuasiSeparatedSpace X) := by
  have hbc : (MorphismProperty.IsStableUnderBaseChange @indQuasiAffineProperty) :=
    HasAffineProperty.isStableUnderBaseChange qcOpensAffineProperty_baseChange
  refine ⟨?_, ?_, ?_⟩
  · intro T g hf
    exact MorphismProperty.pullback_snd f g hf
  · intro I U hU hcover
    constructor
    · intro hf i
      exact MorphismProperty.pullback_snd f (U i).ι hf
    · intro hf
      apply HasAffineProperty.of_iSup_eq_top (fun i ↦ ⟨U i, hU i⟩) hcover
      intro i
      have : IsAffine (U i).toScheme := hU i
      have h := HasAffineProperty.iff_of_isAffine.mp (hf i)
      exact qcOpensQuasiAffine_of_openImmersion
        (pullbackRestrictIsoRestrict f (U i)).inv h
  · intro hY hf
    have hX : qcOpensQuasiAffine X := HasAffineProperty.iff_of_isAffine.mp hf
    have hsep := Scheme.separated_of_affine_pair_neighbourhoods X (by
      intro A B hA hB
      have : (A ⊔ B).toScheme.IsQuasiAffine := hX (A ⊔ B) (hA.isCompact.union hB.isCompact)
      exact ⟨A ⊔ B, le_rfl, inferInstance⟩)
    exact ⟨hX, hsep.2.1, (quasiSeparatedSpace_iff_quasiSeparated X).mpr hsep.2.2⟩

end AlgebraicGeometry
