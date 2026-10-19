/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison
public import Sheaf.Paper.PurityAffineLineDatum
import Sheaf.Paper.PurityRelativeKummer
import Sheaf.Paper.AffineLineSupportGeometry
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-! # The shifted exceptional object of the zero section
Source: blueprint main-20261015, lem-pur-gysin-structure, proof steps 1--5 and 7.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport
open CategoryTheory.Pretriangulated DerivedCategory

private theorem restriction_unit_isIso
    {C : Type*} {D : Type*} {E : Type*} {A : Type*}
    [Category C] [Category D] [Category E] [Category A]
    {Lp : C ⥤ D} {Rp : D ⥤ C} {Lj : D ⥤ E} {Rj : E ⥤ D}
    {L : C ⥤ E} {R : E ⥤ C}
    (adjp : Lp ⊣ Rp) (adjj : Lj ⊣ Rj) (adj : L ⊣ R)
    (e : Rj ⋙ Rp ≅ R) (H : C ⥤ A) (S : C)
    [IsIso (adjp.unit.app S)] [IsIso (H.map (adj.unit.app S))] :
    IsIso (H.map (Rp.map (adjj.unit.app (Lp.obj S)) ≫
      e.hom.app (Lj.obj (Lp.obj S)))) := by
  let a := (adjp.comp adjj).ofNatIsoRight e
  have hi : IsIso (H.map (a.unit.app S)) := by
    rw [← Adjunction.unit_leftAdjointUniq_hom_app adj a S, H.map_comp]
    infer_instance
  have he : a.unit.app S = adjp.unit.app S ≫
      Rp.map (adjj.unit.app (Lp.obj S)) ≫ e.hom.app (Lj.obj (Lp.obj S)) := by
    simp [a, Adjunction.ofNatIsoRight_unit, Adjunction.comp_unit_app, Category.assoc]
  rw [he, H.map_comp] at hi
  exact IsIso.of_isIso_comp_left (H.map (adjp.unit.app S)) _

private theorem unit_isIso {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (adj' : L' ⊣ R)
    (S : C) {K : D} (f : L.obj S ⟶ K) [IsIso f]
    (hf : IsIso (adj.unit.app S ≫ R.map f)) : IsIso (adj'.unit.app S) := by
  have : IsIso (adj.unit.app S) := IsIso.of_isIso_comp_right _ (R.map f)
  rw [← Adjunction.unit_leftAdjointUniq_hom_app adj adj' S]
  infer_instance

private theorem unit_map_isIso {C D A : Type*}
    [Category C] [Category D] [Category A]
    {L L' : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (adj' : L' ⊣ R)
    (H : C ⥤ A) (S : C) {K : D} (f : L.obj S ⟶ K) [IsIso f]
    (hf : IsIso (H.map (adj.unit.app S ≫ R.map f))) :
    IsIso (H.map (adj'.unit.app S)) := by
  have : IsIso (H.map (adj.unit.app S) ≫ H.map (R.map f)) := by
    simpa only [H.map_comp] using hf
  have : IsIso (H.map (adj.unit.app S)) :=
    IsIso.of_isIso_comp_right _ (H.map (R.map f))
  rw [← Adjunction.unit_leftAdjointUniq_hom_app adj adj' S, H.map_comp]
  infer_instance

private theorem triangle_concentration {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) (A : C)
    (hP : ∀ q : ℤ, q ≠ 0 → IsZero ((homologyFunctor C q).obj T.obj₂))
    (hQ : ∀ q : ℤ, q ≠ 0 → q ≠ 1 → IsZero ((homologyFunctor C q).obj T.obj₃))
    [IsIso ((homologyFunctor C 0).map T.mor₂)]
    (e : (homologyFunctor C 1).obj T.obj₃ ≅ A) :
    Nonempty (T.obj₁⟦(2 : ℤ)⟧ ≅ (singleFunctor C 0).obj A) := by
  have hB (q : ℤ) (hq : q ≠ 2) :
      IsZero ((homologyFunctor C q).obj T.obj₁) := by
    by_cases h0 : q = 0
    · subst q
      apply (HomologySequence.exact₁ T hT (-1) 0 (by omega)).isZero_of_both_zeros
      · exact (hQ (-1) (by omega) (by omega)).eq_of_src _ _
      · apply (cancel_mono ((homologyFunctor C 0).map T.mor₂)).mp
        simpa only [Functor.map_comp, Functor.map_zero, zero_comp] using
          congrArg (homologyFunctor C 0).map (comp_distTriang_mor_zero₁₂ T hT)
    by_cases h1 : q = 1
    · subst q
      apply (HomologySequence.exact₁ T hT 0 1 rfl).isZero_of_both_zeros
      · exact (HomologySequence.epi_homologyMap_mor₂_iff T hT 0 1 rfl).mp inferInstance
      · exact (hP 1 (by omega)).eq_of_tgt _ _
    exact (HomologySequence.exact₁ T hT (q - 1) q (by omega)).isZero_of_both_isZero
      (hQ (q - 1) (by omega) (by omega)) (hP q h0)
  have : Mono (HomologySequence.δ T 1 2 rfl) :=
    (HomologySequence.exact₃ T hT 1 2 rfl).mono_g
      ((hP 1 (by omega)).eq_of_src _ _)
  have : Epi (HomologySequence.δ T 1 2 rfl) :=
    (HomologySequence.exact₁ T hT 1 2 rfl).epi_f
      ((hP 2 (by omega)).eq_of_tgt _ _)
  have : IsIso (HomologySequence.δ T 1 2 rfl) := isIso_of_mono_of_epi _
  let B := T.obj₁⟦(2 : ℤ)⟧
  have hz (q : ℤ) (hq : q ≠ 0) : IsZero ((homologyFunctor C q).obj B) :=
    IsZero.of_iso (hB (2 + q) (by omega))
      (((homologyFunctor C 0).shiftIso (2 : ℤ) q (2 + q) rfl).app T.obj₁)
  have : B.IsGE 0 := (isGE_iff B 0).mpr fun q hq ↦ hz q (by omega)
  have : B.IsLE 0 := (isLE_iff B 0).mpr fun q hq ↦ hz q (by omega)
  obtain ⟨M, ⟨i⟩⟩ := B.exists_iso_singleFunctor_obj_of_isGE_of_isLE 0
  let h : M ≅ A :=
    ((singleFunctorCompHomologyFunctorIso C 0).app M).symm ≪≫
      (homologyFunctor C 0).mapIso i.symm ≪≫
      ((homologyFunctor C 0).shiftIso (2 : ℤ) 0 2 (add_zero 2)).app T.obj₁ ≪≫
      (asIso (HomologySequence.δ T 1 2 rfl)).symm ≪≫ e
  exact ⟨i ≪≫ (singleFunctor C 0).mapIso h⟩

namespace WeilConjectures.PurityFiniteSetting

private theorem twist_pullback_isIso (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso (P.twistEtalePullback h f)] : IsIso (P.twistPullback h f) := by
  dsimp [twistPullback]
  infer_instance

private theorem derived_pullback_isIso (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso (P.twistEtalePullback h f)] : IsIso (P.derivedCoefficientPullback h f true) := by
  have := twist_pullback_isIso P h f
  unfold derivedCoefficientPullback
  infer_instance

private theorem relative_unit_isIso (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso (P.twistEtalePullback h f)]
    (hf : IsIso (P.relativeUnit h f true)) :
    IsIso (((upperStarLowerStarAdjunction (Modules P)
      f).mapDerivedCategoryRightDerivedAdjunction).unit.app (P.derivedSheaf h Y true)) := by
  have := derived_pullback_isIso P h f
  exact unit_isIso (derivedUpperStarLowerStarAdjunction (Modules P) f)
    (upperStarLowerStarAdjunction (Modules P) f).mapDerivedCategoryRightDerivedAdjunction
    (P.derivedSheaf h Y true) (P.derivedCoefficientPullback h f true) hf

private theorem relative_unit_homology_isIso (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso (P.twistEtalePullback h f)]
    (hf : IsIso ((homologyFunctor (ProSheaves P Y) 0).map (P.relativeUnit h f true))) :
    IsIso ((homologyFunctor (ProSheaves P Y) 0).map
      (((upperStarLowerStarAdjunction (Modules P)
        f).mapDerivedCategoryRightDerivedAdjunction).unit.app (P.derivedSheaf h Y true))) := by
  have := derived_pullback_isIso P h f
  exact unit_map_isIso (derivedUpperStarLowerStarAdjunction (Modules P) f)
    (upperStarLowerStarAdjunction (Modules P) f).mapDerivedCategoryRightDerivedAdjunction
    (homologyFunctor (ProSheaves P Y) 0) (P.derivedSheaf h Y true)
    (P.derivedCoefficientPullback h f true) hf


/-- The localization triangle identifies the shifted exceptional object with the coefficient
unit. Source: blueprint main-20261015, lem-pur-gysin-structure, first paragraph.
(blueprint: lem-pur-gysin-shifted-constant).

Proof: affine-line support geometry makes the coordinate complement quasi-compact. Apply
exists_comparison to the zero section and projection. Its distinguished triangle has middle
term the direct image on the line and third term the direct image on the punctured line.
The canonical single-complex comparison identifies the input with the root sheaf in degree
zero. Relative Kummer makes the middle term the root line in degree zero and the third term
have cohomology only in degrees zero and one. The restriction in degree zero is invertible:
the composition law for adjunction units identifies its composite with the affine-line unit
with the punctured-line unit. Negative cohomology vanishes because right derived direct
image preserves bounded-below complexes starting in degree zero. In the long exact sequence,
the degree-zero restriction kills H0 and H1 of the first term, the connecting map identifies
its H2 with the constant coefficient sheaf using the Kummer generator, and all other degrees
vanish between zero outer terms. Shift by two. Good truncation identifies this object with
its degree-zero cohomology placed in degree zero, yielding the asserted isomorphism. This
argument is valid on empty and disconnected schemes as well. -/
theorem gysin_shifted_constant (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [IsClosedImmersion (zeroSection Y)] :
    Nonempty (((closedTerm P (zeroSection Y)).obj
      ((DerivedCategory.Plus.singleFunctor (EtSheaves P (Line Y)) 0).obj
        (P.twistEtale h (Line Y))))⟦(2 : ℤ)⟧ ≅ P.derivedSheaf h Y false) := by
  let : Y.Over (Spec (.of P.field.k)) := ⟨a⟩
  have : LocallyOfFiniteType (Y ↘ Spec (.of P.field.k)) := by
    change LocallyOfFiniteType a
    infer_instance
  have : QuasiCompact (Y ↘ Spec (.of P.field.k)) := by
    change QuasiCompact a
    infer_instance
  have : IsSeparated (Y ↘ Spec (.of P.field.k)) := by
    change IsSeparated a
    infer_instance
  have hgeom := affineLine_support_geometry P.field.k Y
  have : QuasiCompact (openImmersion Y) := hgeom.2.2.2.2.2
  have : IsOpenImmersion (openImmersion Y) := by
    dsimp [openImmersion]
    infer_instance
  let : (Line Y).Over (Spec (.of P.field.k)) := ⟨lineProjection Y ≫ a⟩
  have : (lineProjection Y).IsOver (Spec (.of P.field.k)) :=
    ⟨rfl⟩
  have : LocallyOfFiniteType (lineProjection Y ≫ a) := hgeom.1.1
  have : QuasiCompact (lineProjection Y ≫ a) := hgeom.1.2
  have : LocallyOfFiniteType (lineProjection Y) := by
    dsimp [lineProjection]
    infer_instance
  have : QuasiCompact (lineProjection Y) := by
    dsimp [lineProjection]
    infer_instance
  have : IsSeparated (lineProjection Y) := by
    dsimp [lineProjection]
    infer_instance
  have hcompl : IsCompl (Set.range (zeroSection Y).base)
      (Set.range (openImmersion Y).base) := by
    have hs : Set.range (zeroSection Y).base =
        ((Line Y).basicOpen (coordinate Y) : Set (Line Y))ᶜ := by
      change Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y) = _
      rw [AffineSpace.range_zeroSection]
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
      exact ⟨fun hx ↦ hx (ULift.up 0), fun hx i ↦ by
        have : i = ULift.up 0 := Subsingleton.elim _ _
        subst i
        exact hx⟩
    rw [hs]
    change IsCompl _ (Set.range ((Line Y).basicOpen (coordinate Y)).ι.base)
    rw [Scheme.Opens.range_ι]
    exact isCompl_compl.symm
  have : IsSeparated (Line Y ↘ Spec (.of P.field.k)) := by
    change IsSeparated (lineProjection Y ≫ a)
    infer_instance
  have : LocallyOfFiniteType (Line Y ↘ Spec (.of P.field.k)) := by
    change LocallyOfFiniteType (lineProjection Y ≫ a)
    infer_instance
  have : QuasiCompact (Line Y ↘ Spec (.of P.field.k)) := by
    change QuasiCompact (lineProjection Y ≫ a)
    infer_instance
  have hcomparison : Nonempty (Comparison P (lineProjection Y) (zeroSection Y)
      (openImmersion Y) (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) Y)) :=
    exists_comparison P (lineProjection Y) (zeroSection Y)
      (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) Y)
      (openImmersion Y) hcompl
  obtain ⟨c⟩ := hcomparison
  have hk : RelativeKummerConclusions P h Y a := (P.relative_kummer h Y).1
  let p := lineProjection Y
  let j := openImmersion Y
  let π := puncturedProjection Y
  let S := P.derivedSheaf h Y true
  have : S.IsGE 0 := by
    dsimp [S, derivedSheaf]
    infer_instance
  have : S.IsLE 0 := by
    dsimp [S, derivedSheaf]
    infer_instance
  let K := P.derivedSheaf h (Line Y) true
  let V := P.derivedSheaf h (Punctured Y) true
  let B := (DerivedCategory.Plus.singleFunctor (EtSheaves P (Line Y)) 0).obj
    (P.twistEtale h (Line Y))
  let Lp := (upperStar (Modules P) p).mapDerivedCategory
  let Rp := (lowerStar (Modules P) p).rightDerivedFunctor
  let Lj := (upperStar (Modules P) j).mapDerivedCategory
  let Rπ := (lowerStar (Modules P) π).rightDerivedFunctor
  let H := homologyFunctor (ProSheaves P Y) 0
  let adp := (upperStarLowerStarAdjunction (Modules P) p).mapDerivedCategoryRightDerivedAdjunction
  let adj := (upperStarLowerStarAdjunction (Modules P) j).mapDerivedCategoryRightDerivedAdjunction
  let adπ := (upperStarLowerStarAdjunction (Modules P) π).mapDerivedCategoryRightDerivedAdjunction
  let adp' := derivedUpperStarLowerStarAdjunction (Modules P) p
  let adπ' := derivedUpperStarLowerStarAdjunction (Modules P) π
  have := (upperStarLowerStarAdjunction (Modules P) j).preservesKInjectiveComplexes
  let ec := Functor.rightDerivedFunctorCompIso'
    (lowerStar (Modules P) j) (lowerStar (Modules P) p) (lowerStarComp (Modules P) j p)
  have := P.isIso_twistEtalePullback h p (P.exponent_isUnit Y a)
  have := P.isIso_twistEtalePullback h π (P.exponent_isUnit Y a)
  have := P.isIso_twistEtalePullback h j (P.exponent_isUnit (Line Y) (p ≫ a))
  have := twist_pullback_isIso P h p
  have := twist_pullback_isIso P h j
  have : IsIso (adp.unit.app S) := relative_unit_isIso P h p hk.2.1
  have : IsIso (H.map (adπ.unit.app S)) :=
    relative_unit_homology_isIso P h π hk.2.2.2.1
  let eK : (input P (Line Y)).obj B ≅ K :=
    ((comparisonUpperStar (Modules P) (Line Y)).mapDerivedCategorySingleFunctor 0).app
      (P.twistEtale h (Line Y))
  let ep : Lp.obj S ≅ K :=
    ((upperStar (Modules P) p).mapDerivedCategorySingleFunctor 0).app (P.twist h Y) ≪≫
      (singleFunctor (ProSheaves P (Line Y)) 0).mapIso (asIso (P.twistPullback h p))
  let ej : Lj.obj K ≅ V :=
    ((upperStar (Modules P) j).mapDerivedCategorySingleFunctor 0).app
      (P.twist h (Line Y)) ≪≫
      (singleFunctor (ProSheaves P (Punctured Y)) 0).mapIso (asIso (P.twistPullback h j))
  let eM : (middleTerm P p).obj B ≅ Rp.obj K := Rp.mapIso eK
  let eQ : (openTerm P p j).obj B ≅ Rπ.obj V :=
    Rπ.mapIso (Lj.mapIso eK ≪≫ ej)
  let r : Rp ⟶ Lj ⋙ Rπ :=
    Functor.whiskerRight adj.unit Rp ≫ Functor.whiskerLeft Lj ec.hom
  have hr : IsIso (H.map ((restriction P p j).app B)) := by
    have hh := restriction_unit_isIso adp adj adπ ec H S
    change IsIso ((Functor.whiskerRight r H).app ((input P (Line Y)).obj B))
    apply (NatTrans.isIso_app_iff_of_iso (Functor.whiskerRight r H)
      (eK ≪≫ ep.symm)).mpr
    exact hh
  let T := Triangle.mk (c.first.app B) ((restriction P p j).app B) (c.boundary.app B)
  have : IsIso (P.relativeUnit h p true) := hk.2.1
  have : IsIso ((homologyFunctor (ProSheaves P Y) 0).map T.mor₂) := hr
  have hP (q : ℤ) (hq : q ≠ 0) :
      IsZero ((homologyFunctor (ProSheaves P Y) q).obj T.obj₂) := by
    let e := eM ≪≫ (asIso (P.relativeUnit h p true)).symm
    apply IsZero.of_iso _ ((homologyFunctor (ProSheaves P Y) q).mapIso e)
    rcases lt_or_gt_of_ne hq with hq | hq
    · exact (isGE_iff S 0).mp inferInstance q hq
    · exact (isLE_iff S 0).mp inferInstance q hq
  have hQ (q : ℤ) (h0 : q ≠ 0) (h1 : q ≠ 1) :
      IsZero ((homologyFunctor (ProSheaves P Y) q).obj T.obj₃) := by
    apply IsZero.of_iso _ ((homologyFunctor (ProSheaves P Y) q).mapIso eQ)
    by_cases hq : q < 0
    · have := (lowerStar (Modules P) π).isGE_rightDerivedFunctor_obj_singleFunctor
        (P.twist h (Punctured Y))
      exact (isGE_iff (Rπ.obj V) 0).mp this q hq
    · have heq : (q.toNat : ℤ) = q := Int.toNat_of_nonneg (by omega)
      simpa only [heq] using hk.2.2.2.2.2 q.toNat (by omega)
  have : IsIso (P.kummerGenerator h Y a) := hk.2.2.2.2.1
  let eg : (homologyFunctor (ProSheaves P Y) 1).obj T.obj₃ ≅ P.constant Y :=
    (homologyFunctor (ProSheaves P Y) 1).mapIso eQ ≪≫
      (asIso (P.kummerGenerator h Y a)).symm
  exact triangle_concentration T (c.distinguished B) (P.constant Y) hP hQ eg

end WeilConjectures.PurityFiniteSetting
