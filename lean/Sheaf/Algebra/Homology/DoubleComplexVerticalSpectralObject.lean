/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.Algebra.Homology.DoubleComplexVerticalWindow
public import Mathlib.Algebra.Homology.TotalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.ComplexShapeSigns
public import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
import Sheaf.Algebra.Homology.DoubleComplexVerticalTowerComparison
import Mathlib.Algebra.Homology.HomotopyCategory.SpectralObject
import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.SpectralObject

/-!
# The vertical truncation spectral object of a first-quadrant double complex

Source: the construction and graded-piece calculation of blueprint
thm-sp-double-complex-spectral-sequences; Stacks, Homology, Section 12.25.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

section

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def reextensionIso (L : CochainComplex C ℕ) :
    (L.extend ComplexShape.embeddingUpNat).restriction ComplexShape.embeddingUpNat ≅ L :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (L.extend ComplexShape.embeddingUpNat).restrictionXIso
      ComplexShape.embeddingUpNat (i := n) rfl ≪≫
      L.extendXIso ComplexShape.embeddingUpNat rfl)
    (by
      intro i j hij
      dsimp only [verticalReextension, Functor.comp_obj,
        ComplexShape.Embedding.extendFunctor_obj,
        ComplexShape.Embedding.restrictionFunctor_obj, Iso.trans_hom]
      rw [HomologicalComplex.restriction_d_eq _ _ rfl rfl,
        HomologicalComplex.extend_d_eq _ _ rfl rfl]
      simp)
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def reextensionFunctorIso : verticalReextension (C := C) ≅ 𝟭 _ :=
  NatIso.ofComponents reextensionIso (by
    intro L M f
    change HomologicalComplex.restrictionMap
      (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat)
      ComplexShape.embeddingUpNat ≫ (reextensionIso M).hom =
        (reextensionIso L).hom ≫ f
    ext n
    dsimp only [reextensionIso, HomologicalComplex.comp_f,
      HomologicalComplex.Hom.isoOfComponents_hom_f, Iso.trans_hom]
    rw [HomologicalComplex.restrictionMap_f' _ _ rfl,
      HomologicalComplex.extendMap_f _ _ rfl]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id])
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open scoped ZeroObject in
private noncomputable def coneIsoOfZeroSource {F G : CochainComplex C ℤ} (f : F ⟶ G)
    (hF : IsZero F) : CochainComplex.mappingCone f ≅ G := by
  have hi (n : ℤ) : IsIso ((CochainComplex.mappingCone.inr f).f n) := by
    have hz : IsZero (F.X (n + 1)) := (HomologicalComplex.eval C _ (n + 1)).map_isZero hF
    have hb : IsIso (biprod.inr : G.X n ⟶ F.X (n + 1) ⊞ G.X n) := by
      refine ⟨⟨biprod.snd, by simp, ?_⟩⟩
      apply biprod.hom_ext
      · exact hz.eq_of_tgt _ _
      · simp
    have he := HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom f (n + 1) n
      (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl)
    change IsIso (HomologicalComplex.homotopyCofiber.inrX f n)
    exact IsIso.of_isIso_fac_right he
  have : IsIso (CochainComplex.mappingCone.inr f) := HomologicalComplex.Hom.isIso_of_components _
  exact (asIso (CochainComplex.mappingCone.inr f)).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open scoped ZeroObject in
private lemma interval_zeroX (a : ℤ) (j : EInt) (L : CochainComplex C ℕ) (q : ℕ)
    (hq : (q : ℤ) < a) : IsZero (((verticalInterval a j).obj L).X q) := by
  induction j using WithBotTop.rec with
  | bot =>
    have hz : IsZero ((verticalInterval (C := C) a ⊥).obj L) :=
      ((evaluation (CochainComplex C ℕ) (CochainComplex C ℕ)).obj L).map_isZero
        (isZero_zero _)
    exact (HomologicalComplex.eval C _ q).map_isZero hz
  | coe b =>
    change IsZero (((((L.extend ComplexShape.embeddingUpNat).truncGE
      (ComplexShape.embeddingUpIntGE a)).truncLE
      (ComplexShape.embeddingUpIntLE (b - 1))).X (q : ℤ)))
    exact CochainComplex.isZero_of_isStrictlyGE _ a (q : ℤ) hq
  | top =>
    change IsZero (((L.extend ComplexShape.embeddingUpNat).truncGE
      (ComplexShape.embeddingUpIntGE a)).X (q : ℤ))
    exact CochainComplex.isZero_of_isStrictlyGE _ a (q : ℤ) hq

private noncomputable def towerTopIso
    [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ),
      L.HasTotal (ComplexShape.up ℕ)]
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)) :
    verticalTowerTop K ≅ (K.total (ComplexShape.up ℕ)).extend
    ComplexShape.embeddingUpNat := by
  let e : ((verticalReextension (C := C)).mapHomologicalComplex (ComplexShape.up ℕ)).obj K ≅
      K :=
    (NatIso.mapHomologicalComplex reextensionFunctorIso (ComplexShape.up ℕ)).app K ≪≫
      (Functor.mapHomologicalComplexIdIso (CochainComplex C ℕ) (ComplexShape.up ℕ)).app K
  exact (ComplexShape.embeddingUpNat.extendFunctor C).mapIso
    ((totalFunctor C (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)).mapIso e)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma towerFiniteZero
    [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ),
      L.HasTotal (ComplexShape.up ℕ)]
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (b : ℤ) (hb : b ≤ 0) : IsZero (verticalTowerTerm K (b : EInt)) := by
  let M := ((verticalCutoff (C := C) b).mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  have hz (p q : ℕ) : IsZero ((M.X p).X q) := by
    change IsZero ((((K.X p).extend ComplexShape.embeddingUpNat).truncLE
      (ComplexShape.embeddingUpIntLE (b - 1))).X (q : ℤ))
    exact CochainComplex.isZero_of_isStrictlyLE _ (b - 1) (q : ℤ) (by omega)
  have hM : IsZero (total M (ComplexShape.up ℕ)) := by
    rw [IsZero.iff_id_eq_zero]
    apply HomologicalComplex.Hom.ext
    funext n
    apply total.hom_ext
    intro p q hpq
    exact (hz p q).eq_of_src _ _
  exact (ComplexShape.embeddingUpNat.extendFunctor C).map_isZero hM
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open scoped ZeroObject in
private lemma towerTermZero
    [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ),
      L.HasTotal (ComplexShape.up ℕ)]
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (i : EInt) (hi : i ≤ (0 : ℤ)) : IsZero ((verticalTower K).obj i) := by
  induction i using WithBotTop.rec with
  | bot => exact isZero_zero _
  | coe b => exact towerFiniteZero K b (WithBotTop.coe_le_coe.mp hi)
  | top => simp at hi
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open scoped ZeroObject in
private lemma towerConeZero
    [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ),
      L.HasTotal (ComplexShape.up ℕ)]
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (i j : EInt) (hij : i ≤ j) (hj : j ≤ (0 : ℤ)) (n : ℤ) :
    IsZero ((CochainComplex.mappingCone
      ((verticalTower K).map (homOfLE hij))).homology n) := by
  let f := (verticalTower K).map (homOfLE hij)
  have hF := towerTermZero K i (hij.trans hj)
  have hG := towerTermZero K j hj
  have hcone : IsZero (CochainComplex.mappingCone f) := by
    rw [IsZero.iff_id_eq_zero]
    ext m
    have hX : IsZero ((CochainComplex.mappingCone f).X m) := by
      rw [CochainComplex.mappingCone.isZero_X_iff]
      exact ⟨(HomologicalComplex.eval C _ (m + 1)).map_isZero hF,
        (HomologicalComplex.eval C _ m).map_isZero hG⟩
    exact hX.eq_of_src _ _
  exact (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n).map_isZero hcone

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma interval_total_zero_homology
    [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ),
      L.HasTotal (ComplexShape.up ℕ)]
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (a : ℤ) (j : EInt) (n : ℤ) (hn : n < a) :
    IsZero (((total (((verticalInterval a j).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K) (ComplexShape.up ℕ)).extend
      ComplexShape.embeddingUpNat).homology n) := by
  let M := ((verticalInterval (C := C) a j).mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  let T := total M (ComplexShape.up ℕ)
  have hX (i : ℤ) (hi : i < a) : IsZero ((T.extend ComplexShape.embeddingUpNat).X i) := by
    by_cases h : ∃ m, ComplexShape.embeddingUpNat.f m = i
    · obtain ⟨m, hm⟩ := h
      refine IsZero.of_iso ?_ (T.extendXIso ComplexShape.embeddingUpNat hm)
      rw [IsZero.iff_id_eq_zero]
      apply total.hom_ext
      intro p q hpq
      have hq : (q : ℤ) < a := by
        change p + q = m at hpq
        change (m : ℤ) = i at hm
        omega
      exact (interval_zeroX a j (K.X p) q hq).eq_of_src _ _
    · exact T.isZero_extend_X ComplexShape.embeddingUpNat i (by simpa using h)
  have : CochainComplex.IsStrictlyGE (T.extend ComplexShape.embeddingUpNat) a :=
    (CochainComplex.isStrictlyGE_iff _ a).2 hX
  exact CochainComplex.isZero_of_isGE (T.extend ComplexShape.embeddingUpNat) a n hn

end

/-- The smart vertical truncations determine a first-quadrant spectral object.
Source: blueprint thm-sp-double-complex-spectral-sequences, construction in proof step 1;
Stacks, Homology, Section 12.25, the filtration construction.
(blueprint: lem-sp-double-complex-vertical-spectral-object).

Proof: regard the transpose of K, extended by zero in the vertical direction, as a
bounded-below complex in the abelian category of nonnegative horizontal complexes.
Evaluation in a horizontal degree is exact, so its smart truncations are the columnwise
smart truncations used in verticalWindow. Totalization of bounded-below complexes in
this category takes values in integer cochain complexes and preserves triangles.
It also preserves vertical quasi-isomorphisms. Indeed their cones have acyclic columns;
in each degree the diagonal has finite support, and a cycle is eliminated one horizontal
component at a time using vertical exactness. The remaining horizontal component moves
one step to the right and one step down, so the uniform lower bound makes this procedure
terminate. This is the ordinary finite diagonal chase, equivalently a chase of kernels
and images in the abelian category. Hence totalization descends to a triangulated functor
on the bounded-below derived category of horizontal complexes.

Apply the standard t-structure spectral-object construction to the transpose of K,
then the descended totalization functor and the homology functor. This supplies the
interval functors, natural connecting maps and exactness axioms. Finite intervals are
the total complexes of verticalWindow; infinite endpoints use one-sided truncations;
the whole interval is the original total complex. Intervals ending at or below zero
vanish, while those starting at a have no total terms below a. These give the two
first-quadrant conditions. The displayed comparisons are the construction identifications.
No second-page calculation or convergence assertion is part of this lemma. -/
theorem exists_verticalSpectralObject
    [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ),
      L.HasTotal (ComplexShape.up ℕ)]
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)) :
    ∃ Y : CategoryTheory.Abelian.SpectralObject C EInt,
      Y.IsFirstQuadrant ∧
      (∀ (a b : ℤ) (hab : a ≤ b) (n : ℕ),
        Nonempty ((Y.H n).obj (mk₁ (homOfLE
          (show (a : EInt) ≤ (b : EInt) from WithBotTop.coe_le_coe.mpr hab))) ≅
          (HomologicalComplex₂.total
            (((verticalWindow a b).mapHomologicalComplex (ComplexShape.up ℕ)).obj K)
            (ComplexShape.up ℕ)).homology n)) ∧
      (∀ n : ℕ, Nonempty ((Y.H n).obj (mk₁ (homOfLE
        (bot_le : (⊥ : EInt) ≤ ⊤))) ≅ (K.total (ComplexShape.up ℕ)).homology n)) := by
  let : Zero (CochainComplex C ℤ) := HasZeroObject.zero' _
  let X := (HomotopyCategory.spectralObjectMappingCone C).precomp (verticalTower K)
  let Y := X.mapHomologicalFunctor (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0)
  have e (i j : EInt) (hij : i ≤ j) (n : ℤ) :
      (Y.H n).obj (mk₁ (homOfLE hij)) ≅
        (CochainComplex.mappingCone ((verticalTower K).map (homOfLE hij))).homology n := by
    exact (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n).app _
  refine ⟨Y, ?_, ?_, ?_⟩
  · constructor
    · intro i j hij hj n
      exact (towerConeZero K i j hij hj n).of_iso
        (e i j hij n)
    · intro i j hij n hi
      induction i using WithBotTop.rec with
      | bot => simp at hi
      | coe a =>
        obtain ⟨f⟩ := verticalTower_interval_homology_iso K a j hij n
        exact ((interval_total_zero_homology K a j n (WithBotTop.coe_lt_coe.mp hi)).of_iso
          f).of_iso (e a j hij n)
      | top =>
        obtain rfl := top_le_iff.mp hij
        have : IsIso (homOfLE hij : (⊤ : EInt) ⟶ ⊤) := by
          rw [show homOfLE hij = 𝟙 (⊤ : EInt) from Subsingleton.elim _ _]
          infer_instance
        exact Y.isZero_H_map_mk₁_of_isIso n (homOfLE hij)
  · intro a b hab n
    obtain ⟨f⟩ := verticalTower_interval_homology_iso K a b
      (WithBotTop.coe_le_coe.mpr hab) n
    exact ⟨e a b (WithBotTop.coe_le_coe.mpr hab) n ≪≫ f ≪≫
      (total (((verticalWindow a b).mapHomologicalComplex (ComplexShape.up ℕ)).obj K)
        (ComplexShape.up ℕ)).extendHomologyIso ComplexShape.embeddingUpNat rfl⟩
  · intro n
    let f := (verticalTower K).map (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))
    have hz : IsZero ((verticalTower K).obj ⊥) := by
      change IsZero (0 : CochainComplex C ℤ)
      exact isZero_zero _
    exact ⟨e ⊥ ⊤ bot_le n ≪≫ HomologicalComplex.homologyMapIso
      (coneIsoOfZeroSource f hz ≪≫ towerTopIso K) (n : ℤ) ≪≫
        (K.total (ComplexShape.up ℕ)).extendHomologyIso ComplexShape.embeddingUpNat rfl⟩

end HomologicalComplex₂
