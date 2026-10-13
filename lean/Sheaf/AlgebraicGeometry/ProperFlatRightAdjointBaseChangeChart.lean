/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M4
-/
module

public import Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap
public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeHbeta
import Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison

/-! # Proper-flat right-adjoint base change on one affine chart

Source: Stacks Project, Tag 0AAB and Remark 48.6.1, Tag 0E9S.
(blueprint: lem-sc-proper-flat-right-adjoint-basechange-chart)
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The global canonical mate becomes invertible on the preimage of an affine chart
`W` of `Y'` mapping into an affine chart `V` of `Y`.
Source: Stacks Project, duality.tex, Tag 0AAB and Remark 48.6.1 (Tag 0E9S).
(blueprint: lem-sc-proper-flat-right-adjoint-basechange-chart)

Proof: Put U = f inverse(V) and U' = f' inverse(W). Properness makes the restricted
morphisms qcqs; properness, flatness and finite presentation survive restriction and
base change. The restricted direct images admit right adjoints. Tag 0E4J gives the
canonical identifications between restriction of a and a' and those right adjoints.
The open restriction of ordinary base change is the ordinary base-change map of
U' -> U over W -> V; this follows by restricting the pullback/direct-image
adjunctions defining that map. Consequently hβ supplies the chart's witness.
Remark 48.6.1 identifies the restriction of the canonical mate with the chart mate,
conjugated by these identifications: compose the open squares horizontally and use
compatibility of units and counits, including the inverse conjugate of β.
Apply haffine to U -> V and W -> V, to their right adjoints and to K restricted to V.
The chart mate is invertible, hence so is the original mate restricted to U'.
This assertion concerns only one chart, with no covering or descent conclusion.
It holds also for empty charts; restriction then has values in the zero category.
-/
theorem proper_flat_rightAdjoint_baseChange_chart
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y Y' : Scheme.{u}}
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (g : Y' ⟶ Y) (f : X ⟶ Y) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (a' : schemeDerivedQCohCategory Y' ⥤ schemeDerivedQCohCategory (pullback f g))
    (adjf : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y
          (QuasiCompact.compactSpace_of_compactSpace f)
          (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _ f _ _).fst E.obj E.property) ⊣ a)
    (adjf' : (schemeDerivedQCohProperty Y').lift
      ((schemeDerivedQCohProperty (pullback f g)).ι ⋙
        schemeDerivedDirectImage (pullback.snd f g)) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
          (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
          (pullback.snd f g) _ _).fst E.obj E.property) ⊣ a')
    (hβ : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition E.obj))
    (haffine : ∀ {X Y Y' : Scheme.{u}} [IsAffine Y] [IsAffine Y']
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (g : Y' ⟶ Y) (f : X ⟶ Y)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (a' : schemeDerivedQCohCategory Y' ⥤
      schemeDerivedQCohCategory (pullback f g))
    (adjf : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
      (fun E ↦ (schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y f).fst E.obj E.property) ⊣ a)
    (adjf' : (schemeDerivedQCohProperty Y').lift
      ((schemeDerivedQCohProperty (pullback f g)).ι ⋙
        schemeDerivedDirectImage (pullback.snd f g))
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
        (pullback.snd f g) _ _).fst E.obj E.property) ⊣ a')
    (hβ : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g
        (pullback.fst f g) pullback.condition E.obj))
    (K : schemeDerivedQCohCategory Y),
    IsIso (dualityEquationBaseChangeMap f g a a' adjf adjf' hβ K))
    (K : schemeDerivedQCohCategory Y)
    (V : Y.Opens) (hV : IsAffineOpen V)
    (W : Y'.Opens) (hW : IsAffineOpen W) (hWV : W ≤ g ⁻¹ᵁ V) :
    IsIso ((schemeOpenRestriction (pullback f g) ((pullback.snd f g) ⁻¹ᵁ W)).mapDerivedCategory.map
      ((schemeDerivedQCohProperty (pullback f g)).ι.map
        (@dualityEquationBaseChangeMap _ X Y Y'
          (QuasiCompact.compactSpace_of_compactSpace f)
          (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _
          f g a a' adjf adjf' hβ K))) := by
  classical
  let : IsAffine V.toScheme := hV
  let : IsAffine W.toScheme := hW
  let fV := f ∣_ V
  let gW := g.resLE V W hWV
  let : CompactSpace (f ⁻¹ᵁ V).toScheme :=
    QuasiCompact.compactSpace_of_compactSpace fV
  let : QuasiSeparatedSpace (f ⁻¹ᵁ V).toScheme :=
    quasiSeparatedSpace_of_quasiSeparated fV
  have hUV : (pullback.snd f g) ⁻¹ᵁ W ≤
      (pullback.fst f g) ⁻¹ᵁ (f ⁻¹ᵁ V) := by
    calc
      _ ≤ (pullback.snd f g) ⁻¹ᵁ (g ⁻¹ᵁ V) :=
        (pullback.snd f g).preimage_mono hWV
      _ = _ := by
        rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]
  let r := (pullback.fst f g).resLE (f ⁻¹ᵁ V) ((pullback.snd f g) ⁻¹ᵁ W) hUV
  let s := pullback.snd f g ∣_ W
  have hrs : r ≫ fV = s ≫ gW := by
    apply (cancel_mono V.ι).mp
    simp only [Category.assoc, fV, gW, r, s, morphismRestrict_ι,
      Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc]
    simp only [← Category.assoc, pullback.condition]
    simp only [morphismRestrict_ι]
  let q := pullback.lift r s hrs
  let FV := (schemeDerivedQCohProperty V.toScheme).lift
    ((schemeDerivedQCohProperty (f ⁻¹ᵁ V).toScheme).ι ⋙ schemeDerivedDirectImage fV)
    (fun E ↦ (schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ fV).fst E.obj E.property)
  have : FV.IsLeftAdjoint :=
    (schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ fV).choose_spec
  let b := FV.rightAdjoint
  let adjb := Adjunction.ofIsLeftAdjoint FV
  let : QuasiSeparatedSpace (pullback fV gW : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd fV gW)
  let FV' := (schemeDerivedQCohProperty W.toScheme).lift
    ((schemeDerivedQCohProperty (pullback fV gW)).ι ⋙
      schemeDerivedDirectImage (pullback.snd fV gW))
    (fun E ↦ (schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _
      (pullback.snd fV gW)).fst E.obj E.property)
  have : FV'.IsLeftAdjoint :=
    (schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ (pullback.snd fV gW)).choose_spec
  let b' := FV'.rightAdjoint
  let adjb' := Adjunction.ofIsLeftAdjoint FV'
  have hβV := proper_flat_rightAdjoint_baseChange_hβ gW fV
  let KV : schemeDerivedQCohCategory V.toScheme :=
    ⟨(derivedPullback V.ι).obj K.obj,
      (derivedPullback_tensor_preserve_QCoh V.ι).1 K.obj K.property⟩
  have : IsIso (dualityEquationBaseChangeMap fV gW b b' adjb adjb' hβV KV) :=
    haffine gW fV b b' adjb adjb' hβV KV
  obtain ⟨c⟩ := proper_flat_rightAdjoint_chart_mate_comparison g f a a' adjf adjf' hβ
    K V W hWV b b' adjb adjb' hβV q
    (by
      change q ≫ pullback.fst fV gW ≫ _ = _
      simp [q, r])
    (by
      change q ≫ pullback.snd fV gW ≫ _ = _
      simp [q, s])
  exact (Arrow.isIso_iff_isIso_of_isIso c.hom).mpr (by infer_instance)

end AlgebraicGeometry
