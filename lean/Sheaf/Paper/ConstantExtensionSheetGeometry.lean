/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A7
-/
module

public import Sheaf.Paper.ConstantExtensionSheetHeartData
import Sheaf.Paper.ConstantExtensionSheetTensorSplitting
import Sheaf.Paper.ConstantExtensionCyclicSheetPartition
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # The clopen geometry of cyclic constant-extension sheets

Source: Deligne, Weil II, (1.1.7) and paragraph after (1.1.10), pp. 150--152.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)
variable (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]

private theorem sheetPositivePower {S : Scheme.{u}} (g : Aut S) (n : ℕ) :
    localPositivePower g.hom n = (g ^ (n + 1)).hom := by
  induction n with
  | zero => simp [localPositivePower]
  | succ n ih =>
    rw [localPositivePower, ih]
    exact (congrArg (fun b : Aut S ↦ b.hom) (pow_succ' g (n + 1))).symm

private theorem sheetSuccessor (i : Fin m) (h : i.val + 1 < m) :
    constantExtensionCyclicSheet D m hm X₀ i ≫
        (D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)).hom =
      constantExtensionCyclicSheet D m hm X₀ ⟨i.val + 1, h⟩ := by
  let H := D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)
  have hstep : (H ^ i.val).hom ≫ H.hom = (H ^ (i.val + 1)).hom := by
    rw [pow_succ']
    rfl
  simpa only [constantExtensionCyclicSheet, Category.assoc] using
    congrArg (fun f ↦ (constantExtensionFiberIso D m hm X₀).inv ≫
      constantExtensionSheet D m hm X₀ ≫ f) hstep

private theorem sheetReturn (i : Fin m) (h : ¬ i.val + 1 < m) :
    constantExtensionCyclicSheet D m hm X₀ i ≫
        (D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)).hom =
      localPositivePower (D.geometricFrobenius X₀).hom (m - 1) ≫
        constantExtensionCyclicSheet D m hm X₀ ⟨0, hm⟩ := by
  have hi : i.val + 1 = m := by omega
  have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
  let e := constantExtensionFiberIso D m hm X₀
  let j := constantExtensionSheet D m hm X₀
  let F := (constantExtensionDatum D m hm).geometricFrobenius
    (constantExtensionModel D m hm X₀)
  let H := D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)
  let g := D.geometricFrobenius X₀
  have hF : F.hom ≫ j = j ≫ (H ^ m).hom := by
    simpa only [sheetPositivePower, hm'] using constantExtensionSheet_return D m hm X₀
  have hg : F.hom ≫ e.hom = e.hom ≫ (g ^ m).hom := by
    simpa only [sheetPositivePower, hm'] using constantExtensionFiber_return D m hm X₀
  have hinv : e.inv ≫ F.hom = (g ^ m).hom ≫ e.inv := by
    rw [← cancel_mono e.hom]
    simp only [Category.assoc, hg, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  have hstep : (H ^ i.val).hom ≫ H.hom = (H ^ m).hom := by
    calc
      (H ^ i.val).hom ≫ H.hom = (H ^ (i.val + 1)).hom := by
        rw [pow_succ']
        rfl
      _ = (H ^ m).hom := congrArg (fun n : ℕ ↦ (H ^ n).hom) hi
  change (e.inv ≫ j ≫ (H ^ i.val).hom) ≫ H.hom = _
  rw [Category.assoc, Category.assoc, hstep, ← hF, ← Category.assoc, hinv]
  have hone : (1 : Aut
      (D.geometricFiber (constantExtensionOriginalModel D m hm X₀)).left).hom = 𝟙 _ := rfl
  simp only [constantExtensionCyclicSheet, pow_zero, sheetPositivePower, hm',
    hone, Category.comp_id, Category.assoc]
  rfl

private theorem sheetImmersions (i : Fin m) :
    IsOpenImmersion (constantExtensionCyclicSheet D m hm X₀ i) ∧
      IsClosedImmersion (constantExtensionCyclicSheet D m hm X₀ i) := by
  let := (D.extensionEmbedding m hm).toAlgebra
  have := (constantExtensionField_properties D m hm).1
  let π := Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))
  have : Etale π := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr Algebra.Etale.of_finite_of_isSeparable
  have hp : Etale (constantExtensionProjection D m hm X₀).left :=
    show Etale (pullback.fst X₀.hom π) from inferInstance
  let p := zlFiberMap D (constantExtensionProjection D m hm X₀)
  have : Etale p := MorphismProperty.overPullbackMap (P := @Etale)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
    (constantExtensionProjection D m hm X₀) hp
  have hpsep : IsSeparated (constantExtensionProjection D m hm X₀).left :=
    show IsSeparated (pullback.fst X₀.hom π) from inferInstance
  have : IsSeparated p := MorphismProperty.overPullbackMap (P := @IsSeparated)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
    (constantExtensionProjection D m hm X₀) hpsep
  let j := constantExtensionSheet D m hm X₀
  have : IsIso (j ≫ p) := constantExtensionFiberMap_isIso D m hm X₀
  have : MorphismProperty.HasOfPostcompProperty
      (@IsOpenImmersion : MorphismProperty Scheme.{u}) @Etale := by
    rw [MorphismProperty.hasOfPostcompProperty_iff_le_diagonal]
    intro A B f hf
    let : Etale f := hf
    exact inferInstanceAs (IsOpenImmersion (pullback.diagonal f))
  have : IsOpenImmersion j := MorphismProperty.of_postcomp
    @IsOpenImmersion (W' := @Etale) j p ‹_› inferInstance
  have : IsClosedImmersion j := IsClosedImmersion.of_comp j p
  change IsOpenImmersion
      ((constantExtensionFiberIso D m hm X₀).inv ≫ j ≫
        ((D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)) ^ i.val).hom) ∧
    IsClosedImmersion
      ((constantExtensionFiberIso D m hm X₀).inv ≫ j ≫
        ((D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)) ^ i.val).hom)
  exact ⟨inferInstance, inferInstance⟩

/-- The cyclic sheets cover the actual constant-extension fibre by clopen components.
Source: Deligne, Weil II, (1.1.7) and paragraph after (1.1.10), pp. 150--152
(blueprint: lem-zl-constant-extension-sheet-geometry).

Proof: constantExtensionSheetTensorSplitting gives the prescribed evaluation formula
and embedding count. The distinguished sheet followed by the geometric projection is
the canonical fibre isomorphism. That projection is etale and separated; the diagonal
criteria therefore make the distinguished sheet an open and closed immersion. Every
cyclic sheet is its composite with two isomorphisms, so is also an open and closed
immersion. Take the actual open ranges. constantExtensionCyclicSheetPartition supplies
their disjointness and cover. The canonical isomorphism of open immersions with equal
ranges constructs each coordinate and its factorization. The successor equality is
the power-successor identity. At the last index, the already proved distinguished-sheet
return and fibre-Frobenius return give the required cyclic return after cancelling the
fibre isomorphism. The new-model Frobenius identity is constantExtensionFiber_return.
No data is chosen from the unfinished point-partition theorem. -/
theorem constantExtensionSheetGeometry :
    Nonempty (ZlSheetGeometry D m hm X₀) := by
  have hopen (i : Fin m) := (sheetImmersions D m hm X₀ i).1
  have hclosed (i : Fin m) := (sheetImmersions D m hm X₀ i).2
  obtain ⟨hdisjoint, hcover⟩ := constantExtensionCyclicSheetPartition D m hm X₀
  let h := constantExtensionCyclicSheet D m hm X₀
  let U := fun i : Fin m ↦ (h i).opensRange
  have hrange (i : Fin m) : Set.range (h i) = Set.range (U i).ι := by
    rw [Scheme.Opens.range_ι]
    rfl
  refine ⟨{
    tensor := constantExtensionSheetTensorSplitting D m hm
    opens := U
    closed := fun i ↦ (h i).isClosedEmbedding.isClosed_range
    disjoint := ?_
    cover := ?_
    coordinate := fun i ↦ IsOpenImmersion.isoOfRangeEq (h i) (U i).ι (hrange i)
    factor := fun i ↦ IsOpenImmersion.isoOfRangeEq_hom_fac (h i) (U i).ι (hrange i)
    successor := sheetSuccessor D m hm X₀
    return_map := sheetReturn D m hm X₀
    new_frobenius := constantExtensionFiber_return D m hm X₀ }⟩
  · intro i j hij
    exact TopologicalSpace.Opens.coe_disjoint.mp (hdisjoint hij)
  · apply TopologicalSpace.Opens.ext
    rw [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top]
    exact hcover

end WeilConjectures
