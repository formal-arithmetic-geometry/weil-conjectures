/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q88
-/
module

public import WeilConjectures.Blowup.FlatBaseChange
public import WeilConjectures.Compactification.StrictTransform
public import WeilConjectures.Compactification.FiniteTypeExtension
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Topology.Sober
import Sheaf.AlgebraicGeometry.FiniteCenterOpenClosureKernelData
import WeilConjectures.AlgebraicGeometry.FiniteTypeIdealModule
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Strict transform under flat base change

Source: Stacks Project, Tag 081I, `lemma-flat-base-change-scheme-theoretic-image`,
and Tag 080D, `definition-strict-transform`
(blueprint: lem-trf-strict-transform-flat-etale-base-change).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

private theorem openKernel_baseChange
    {Y Y' P P' : Scheme.{u}} {f : Y ⟶ P} {f' : Y' ⟶ P'}
    {p : Y' ⟶ Y} {q : P' ⟶ P} (H : IsPullback p f' f q)
    (U : P.Opens) [Flat q] [QuasiCompact f] [QuasiCompact (f ⁻¹ᵁ U).ι] :
    ((f ⁻¹ᵁ U).ι ≫ f).ker.comap q =
      ((f' ⁻¹ᵁ (q ⁻¹ᵁ U)).ι ≫ f').ker := by
  have h := (isPullback_morphismRestrict p (f ⁻¹ᵁ U)).paste_vert H
  have heq : p ⁻¹ᵁ (f ⁻¹ᵁ U) = f' ⁻¹ᵁ (q ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, H.w, Scheme.Hom.comp_preimage]
  have : QuasiCompact ((f ⁻¹ᵁ U).ι ≫ f) := inferInstance
  exact (Scheme.Hom.ker_of_isPullback _ q h).symm.trans
    (congrArg (fun V : Y'.Opens ↦ (V.ι ≫ f').ker) heq)

private theorem finiteCenter_qc {X Y : Scheme.{u}} (I : X.IdealSheafData)
    (hI : I.ofFiniteType) (f : Y ⟶ X) :
    QuasiCompact (f ⁻¹ᵁ I.support.compl).ι := by
  have : I.toModules.IsFiniteType := I.isFiniteType_toModules_sheaf hI
  exact (finiteCenterOpen_closure_kernel_data f I).1

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- Strict transform of a closed subscheme commutes with flat base change, with the
specified generic-point hypothesis. The first equality uses the canonical blowup comparison;
the second identifies the same ideal with the scheme-theoretic closure of the common open
inverse image of the complement of the center. Ideals, rather than supports, retain nilpotents.
An etale base change is included since an etale morphism is flat.

Source: Stacks Project Tags 081I and 080D
(blueprint: lem-trf-strict-transform-flat-etale-base-change).

Proof:
1. Convert finite type of the ideal to finite type of its module using
   `lem-pqf-finite-type-ideal-module`. The quasi-compactness clause of
   `lem-trf-finite-center-open-closure-kernel-data` applies to each structure map.
   Thus `ker_strictTransformMap` identifies the strict-transform ideals with the
   kernels of the preserved-open maps into their ambient blowups.
2. Construct the map from `Z_W ×_W (Bl_I X)_W` to `Z ×_X Bl_I X` by its projections.
   Pasting and cancellation of pullback squares prove that its ambient square is
   cartesian. Restrict to the preserved opens and paste again. The ambient projection
   is flat by `lem-weil-pbc-flat-morphism-base-change`, so the proved
   `Scheme.Hom.ker_of_isPullback` (`lem-sfb-scheme-image-flat-base-change`) gives the
   second equality. The two preserved opens agree by the pullback equation.
3. Apply the same open-kernel comparison to the cartesian square induced by the
   canonical blowup isomorphism (`thm-nagata-blowup-flat-base-change`). The support
   of an extended ideal is the inverse image of its support; together with the
   equation for the blowup comparison over `W`, this identifies the preserved opens.
   Pull the kernel equality back along the inverse isomorphism and cancel the two
   pullbacks to obtain the first equality. The generic-point hypothesis is retained
   although the kernel argument does not use it. -/
theorem strictTransform_flat_baseChange
    {X Z W : Scheme.{u}} (I : X.IdealSheafData) (_hI : I.ofFiniteType)
    (i : Z ⟶ X) [IsClosedImmersion i] (v : W ⟶ X) [Flat v]
    (_hgeneric : ∀ C ∈ irreducibleComponents ↥(pullback i v),
      ∀ ξ : ↥(pullback i v), IsGenericPoint ξ C →
        ∃ D ∈ irreducibleComponents Z, IsGenericPoint (pullback.fst i v ξ) D) :
    (AlgebraicGeometry.strictTransformMap i I.blowupMap I.support.compl).ker.comap
        (pullback.fst I.blowupMap v) =
      (AlgebraicGeometry.strictTransformMap (pullback.snd i v) (I.comap v).blowupMap
        (I.comap v).support.compl).ker.comap (I.blowupFlatBaseChangeIso v).inv ∧
    (AlgebraicGeometry.strictTransformMap i I.blowupMap I.support.compl).ker.comap
        (pullback.fst I.blowupMap v) =
      ((AlgebraicGeometry.strictTransformOpen (pullback.snd i v)
          (pullback.snd I.blowupMap v) (v ⁻¹ᵁ I.support.compl)).ι ≫
        pullback.snd (pullback.snd i v) (pullback.snd I.blowupMap v)).ker := by
  let π := I.blowupMap
  let U := I.support.compl
  let π' := pullback.snd π v
  let i' := pullback.snd i v
  let q := pullback.fst π v
  let a := pullback.snd i π
  let b := pullback.snd i' π'
  let p : pullback i' π' ⟶ pullback i π :=
    pullback.lift (pullback.fst i' π' ≫ pullback.fst i v) (b ≫ q) (by
      simp only [Category.assoc, pullback.condition]
      rw [← Category.assoc, pullback.condition, Category.assoc, pullback.condition])
  have H : IsPullback p b a q := by
    apply IsPullback.of_right (t := IsPullback.of_hasPullback i π)
    · simpa only [p, pullback.lift_fst, π', q, pullback.condition] using
        (IsPullback.of_hasPullback i' π').paste_horiz (IsPullback.of_hasPullback i v)
    · exact pullback.lift_snd _ _ _
  have hqc : QuasiCompact (strictTransformOpen i π U).ι :=
    finiteCenter_qc I _hI (a ≫ π)
  have hqc' : QuasiCompact (strictTransformOpen i' π' (v ⁻¹ᵁ U)).ι :=
    finiteCenter_qc I _hI (b ≫ π' ≫ v)
  have : QuasiCompact (a ⁻¹ᵁ (π ⁻¹ᵁ U)).ι := hqc
  have : QuasiCompact (b ⁻¹ᵁ (π' ⁻¹ᵁ (v ⁻¹ᵁ U))).ι := hqc'
  have hbase :
      (strictTransformMap i π U).ker.comap q =
        ((strictTransformOpen i' π' (v ⁻¹ᵁ U)).ι ≫ b).ker := by
    rw [ker_strictTransformMap]
    have heq : q ⁻¹ᵁ (π ⁻¹ᵁ U) = π' ⁻¹ᵁ (v ⁻¹ᵁ U) := by
      rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage]
    exact (openKernel_baseChange H (π ⁻¹ᵁ U)).trans
      (congrArg (fun V : (pullback i' π').Opens ↦ (V.ι ≫ b).ker)
        (congrArg (fun V ↦ b ⁻¹ᵁ V) heq))
  refine ⟨?_, hbase⟩
  let e := I.blowupFlatBaseChangeIso v
  let c := pullback.snd i' (I.comap v).blowupMap
  let r := pullback.map i' (I.comap v).blowupMap i' π'
    (𝟙 _) e.hom (𝟙 _) (by simp)
    (by simpa only [Category.comp_id] using
      (I.blowupFlatBaseChangeIso_hom_snd v).symm)
  have Hr : IsPullback r c b e.hom :=
    IsPullback.of_horiz_isIso ⟨by simp [r, c, b]⟩
  have hsupp : (I.comap v).support.compl = v ⁻¹ᵁ U := by
    ext x
    simp [U, support_comap]
  have heq : e.hom ⁻¹ᵁ (π' ⁻¹ᵁ (v ⁻¹ᵁ U)) =
      (I.comap v).blowupMap ⁻¹ᵁ (I.comap v).support.compl := by
    rw [← Scheme.Hom.comp_preimage, show e.hom ≫ π' = (I.comap v).blowupMap from
      I.blowupFlatBaseChangeIso_hom_snd v, hsupp]
  have hcqc : QuasiCompact
      (strictTransformOpen i' (I.comap v).blowupMap (I.comap v).support.compl).ι :=
    finiteCenter_qc (I.comap v) (_hI.comap v) (c ≫ (I.comap v).blowupMap)
  have ht : (((strictTransformOpen i' π' (v ⁻¹ᵁ U)).ι ≫ b).ker).comap e.hom =
      (strictTransformMap i' (I.comap v).blowupMap (I.comap v).support.compl).ker := by
    rw [ker_strictTransformMap]
    exact (openKernel_baseChange Hr (π' ⁻¹ᵁ (v ⁻¹ᵁ U))).trans
      (congrArg (fun V : (pullback i' (I.comap v).blowupMap).Opens ↦ (V.ι ≫ c).ker)
        (congrArg (fun V ↦ c ⁻¹ᵁ V) heq))
  rw [hbase, ← ht, ← comap_comp, e.inv_hom_id, comap_id]

end AlgebraicGeometry.Scheme.IdealSheafData
