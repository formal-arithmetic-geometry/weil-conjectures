/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.Algebra.Homology.FilteredDerivedHomCalculus
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.FilteredTruncationTriangle

/-!
# Exact change of coefficients on finite filtered derived categories

Source: Varshavsky, §§5.1.1–5.1.2; Stacks Project, Tags 05S2 and 05S4.
(blueprint: lem-trf-exact-filtered-coefficient-change).
-/

@[expose] public section

set_option autoImplicit false

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.FiniteFiltered

variable {A : Type u₁} {B : Type u₂}
variable [Category.{v₁} A] [Category.{v₂} B] [Abelian A] [Abelian B]
variable [HasDerivedCategory.{max u₁ v₁} A] [HasDerivedCategory.{max u₂ v₂} B]
variable (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable [TriangulatedLocalization A false] [TriangulatedLocalization B false]
variable (S : TruncationCalculus A false) (T : TruncationCalculus B false)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

omit [HasDerivedCategory A] [HasDerivedCategory B]
  [TriangulatedLocalization A false] [TriangulatedLocalization B false] in
omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private lemma coefficient_antitone (K : FilteredObject (CochainComplex A ℤ)) :
    Antitone (fun p : ℤ ↦ imageSubobject
      ((F.mapHomologicalComplex (.up ℤ)).map (K.filtration.step p).arrow)) := by
  intro i j hij
  dsimp only
  rw [← Subobject.ofLE_arrow (K.filtration.antitone_step hij), Functor.map_comp]
  exact imageSubobject_comp_le _ _

private noncomputable def coefficientObject (K : FilteredObject (CochainComplex A ℤ)) :
    FilteredObject (CochainComplex B ℤ) where
  obj := (F.mapHomologicalComplex (.up ℤ)).obj K.obj
  filtration :=
    { F := fun p ↦ imageSubobject
        ((F.mapHomologicalComplex (.up ℤ)).map (K.filtration.step p).arrow)
      F_succ_le := fun p ↦ coefficient_antitone F K (by omega) }

omit [HasDerivedCategory A] [HasDerivedCategory B]
  [TriangulatedLocalization A false] [TriangulatedLocalization B false] in
private lemma coefficient_bounds (K : Complex A false) :
    (coefficientObject F K.obj).filtration.IsFinite ∧
      DegreeBound B false (coefficientObject F K.obj).obj := by
  obtain ⟨n, m, hn, hm⟩ := K.property.1
  obtain ⟨⟨a, ha⟩, _⟩ := K.property.2
  refine ⟨⟨n, m, ?_, ?_⟩, ⟨⟨a, fun i hi ↦ F.map_isZero (ha i hi)⟩, Or.inl rfl⟩⟩
  · change imageSubobject ((F.mapHomologicalComplex (.up ℤ)).map
      (K.obj.filtration.step n).arrow) = ⊤
    change imageSubobject ((F.mapHomologicalComplex (.up ℤ)).map
      (K.obj.filtration.F n).arrow) = ⊤
    rw [hn, imageSubobject_mono]
    exact Subobject.mk_eq_top_of_isIso _
  · change imageSubobject ((F.mapHomologicalComplex (.up ℤ)).map
      (K.obj.filtration.step m).arrow) = ⊥
    change imageSubobject ((F.mapHomologicalComplex (.up ℤ)).map
      (K.obj.filtration.F m).arrow) = ⊥
    rw [hm, Subobject.bot_arrow, Functor.map_zero, imageSubobject_zero]

omit [HasDerivedCategory A] [HasDerivedCategory B]
  [TriangulatedLocalization A false] [TriangulatedLocalization B false] in
omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private lemma coefficient_preserves {K M : Complex A false} (f : K ⟶ M) :
    ∀ p : ℤ, ∃ l : ((coefficientObject F K.obj).filtration.step p : CochainComplex B ℤ) ⟶
      ((coefficientObject F M.obj).filtration.step p : CochainComplex B ℤ),
      l ≫ ((coefficientObject F M.obj).filtration.step p).arrow =
        ((coefficientObject F K.obj).filtration.step p).arrow ≫
          (F.mapHomologicalComplex (.up ℤ)).map f.hom.hom := by
  intro p
  let H := F.mapHomologicalComplex (.up ℤ)
  have hs := congrArg H.map (restriction_square f.hom p)
  simp only [Functor.map_comp] at hs
  exact ⟨imageSubobjectMap (Arrow.homMk (H.map (FilteredObject.restrictionSteps f.hom p))
    (H.map f.hom.hom) hs), by
      change imageSubobjectMap _ ≫ (imageSubobject _).arrow = _
      exact imageSubobjectMap_arrow _⟩

private noncomputable def coefficientComplex : Complex A false ⥤ Complex B false where
  obj K := ⟨coefficientObject F K.obj, coefficient_bounds F K⟩
  map f := ⟨⟨(F.mapHomologicalComplex (.up ℤ)).map f.hom.hom, coefficient_preserves F f⟩⟩
  map_id K := by
    apply ObjectProperty.hom_ext
    change FilteredObject.Hom.mk _ _ =
      FilteredObject.Hom.mk _ _
    congr 1
    exact (F.mapHomologicalComplex (.up ℤ)).map_id K.obj.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    change FilteredObject.Hom.mk _ _ =
      FilteredObject.Hom.mk _ _
    congr 1
    exact (F.mapHomologicalComplex (.up ℤ)).map_comp f.hom.hom g.hom.hom

private noncomputable def coefficientStepIso
    (K : FilteredObject (CochainComplex A ℤ)) (p : ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).obj (K.filtration.step p) ≅
      ((coefficientObject F K).filtration.step p : CochainComplex B ℤ) := by
  let m := (F.mapHomologicalComplex (.up ℤ)).map (K.filtration.step p).arrow
  have : Mono (factorThruImageSubobject m) :=
    mono_of_mono_fac (imageSubobject_arrow_comp m)
  have : IsIso (factorThruImageSubobject m) := isIso_of_mono_of_epi _
  exact asIso (factorThruImageSubobject m)

omit [HasDerivedCategory A] [HasDerivedCategory B]
  [TriangulatedLocalization A false] [TriangulatedLocalization B false] in
private lemma coefficientStepIso_arrow (K : FilteredObject (CochainComplex A ℤ)) (p : ℤ) :
    (coefficientStepIso F K p).hom ≫ ((coefficientObject F K).filtration.step p).arrow =
      (F.mapHomologicalComplex (.up ℤ)).map (K.filtration.step p).arrow := by
  exact imageSubobject_arrow_comp _

omit [HasDerivedCategory A] [HasDerivedCategory B]
  [TriangulatedLocalization A false] [TriangulatedLocalization B false] in
private lemma coefficientStepIso_inclusion
    (K : FilteredObject (CochainComplex A ℤ)) (p : ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map
        (Subobject.ofLE _ _ (K.filtration.F_succ_le p)) ≫
        (coefficientStepIso F K p).hom =
      (coefficientStepIso F K (p + 1)).hom ≫
        Subobject.ofLE _ _ ((coefficientObject F K).filtration.F_succ_le p) := by
  apply (cancel_mono ((coefficientObject F K).filtration.step p).arrow).1
  simp only [Category.assoc, coefficientStepIso_arrow, Subobject.ofLE_arrow,
    ← Functor.map_comp]

private noncomputable def coefficientGradeIso
    (K : FilteredObject (CochainComplex A ℤ)) (p : ℤ) :
    (coefficientObject F K).filtration.gradedPiece p ≅
      (F.mapHomologicalComplex (.up ℤ)).obj (K.filtration.gradedPiece p) :=
  ((PreservesCokernel.iso (F.mapHomologicalComplex (.up ℤ))
    (Subobject.ofLE _ _ (K.filtration.F_succ_le p))) ≪≫
      cokernel.mapIso _ _ (coefficientStepIso F K (p + 1)) (coefficientStepIso F K p)
        (coefficientStepIso_inclusion F K p)).symm

omit [HasDerivedCategory A] [HasDerivedCategory B]
  [TriangulatedLocalization A false] [TriangulatedLocalization B false] in
private lemma coefficientGradeIso_projection
    (K : FilteredObject (CochainComplex A ℤ)) (p : ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map
        (K.filtration.complexQuotientπ p (p + 1) (by omega)) ≫
        (coefficientGradeIso F K p).inv =
      (coefficientStepIso F K p).hom ≫
        (coefficientObject F K).filtration.complexQuotientπ p (p + 1) (by omega) := by
  dsimp [coefficientGradeIso, DecreasingFiltration.complexQuotientπ]
  rw [← Category.assoc, PreservesCokernel.π_iso_hom]
  simp

omit [HasDerivedCategory A] [HasDerivedCategory B]
  [TriangulatedLocalization A false] [TriangulatedLocalization B false] in
private lemma coefficientStepIso_naturality {K M : Complex A false} (f : K ⟶ M) (p : ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map (FilteredObject.restrictionSteps f.hom p) ≫
        (coefficientStepIso F M.obj p).hom =
      (coefficientStepIso F K.obj p).hom ≫
        FilteredObject.restrictionSteps ((coefficientComplex F).map f).hom p := by
  have h := restriction_square ((coefficientComplex F).map f).hom p
  change FilteredObject.restrictionSteps ((coefficientComplex F).map f).hom p ≫
    ((coefficientObject F M.obj).filtration.step p).arrow =
    ((coefficientObject F K.obj).filtration.step p).arrow ≫
      (F.mapHomologicalComplex (.up ℤ)).map f.hom.hom at h
  apply (cancel_mono ((coefficientObject F M.obj).filtration.step p).arrow).1
  simp only [Category.assoc, coefficientStepIso_arrow, h]
  rw [← Functor.map_comp, restriction_square, Functor.map_comp,
    ← Category.assoc, coefficientStepIso_arrow]

omit [HasDerivedCategory A] [HasDerivedCategory B]
  [TriangulatedLocalization A false] [TriangulatedLocalization B false] in
private lemma graded_projection_square {K M : FilteredObject (CochainComplex A ℤ)}
    (f : K ⟶ M) (p : ℤ) :
    K.filtration.complexQuotientπ p (p + 1) (by omega) ≫
        FilteredObject.gradedMapSteps f p =
      FilteredObject.restrictionSteps f p ≫
        M.filtration.complexQuotientπ p (p + 1) (by omega) :=
  Classical.choose_spec (FilteredObject.exists_gradedMap_steps K M f p)

omit [HasDerivedCategory A] [HasDerivedCategory B]
  [TriangulatedLocalization A false] [TriangulatedLocalization B false] in
private lemma coefficientGradeIso_inv_naturality {K M : Complex A false} (f : K ⟶ M)
    (p : ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map (FilteredObject.gradedMapSteps f.hom p) ≫
        (coefficientGradeIso F M.obj p).inv =
      (coefficientGradeIso F K.obj p).inv ≫
        FilteredObject.gradedMapSteps ((coefficientComplex F).map f).hom p := by
  have : Epi (K.obj.filtration.complexQuotientπ p (p + 1) (by omega)) := by
    dsimp [DecreasingFiltration.complexQuotientπ]
    infer_instance
  apply (cancel_epi ((F.mapHomologicalComplex (.up ℤ)).map
    (K.obj.filtration.complexQuotientπ p (p + 1) (by omega)))).1
  rw [← Functor.map_comp_assoc, graded_projection_square, Functor.map_comp]
  have h := graded_projection_square ((coefficientComplex F).map f).hom p
  change (coefficientObject F K.obj).filtration.complexQuotientπ p (p + 1) (by omega) ≫
    FilteredObject.gradedMapSteps ((coefficientComplex F).map f).hom p =
    FilteredObject.restrictionSteps ((coefficientComplex F).map f).hom p ≫
      (coefficientObject F M.obj).filtration.complexQuotientπ p (p + 1) (by omega) at h
  rw [Category.assoc, coefficientGradeIso_projection, ← Category.assoc,
    coefficientStepIso_naturality, Category.assoc, ← h,
    ← Category.assoc, ← coefficientGradeIso_projection, Category.assoc]

private noncomputable def coefficientGradedComparison (p : ℤ) :
    coefficientComplex F ⋙ graded false p ≅ graded false p ⋙ F.mapHomologicalComplex (.up ℤ) :=
  (NatIso.ofComponents (fun K ↦ (coefficientGradeIso F K.obj p).symm)
    (fun f ↦ coefficientGradeIso_inv_naturality F f p)).symm

omit [HasDerivedCategory A] [HasDerivedCategory B]
  [TriangulatedLocalization A false] [TriangulatedLocalization B false] in
private lemma coefficient_quasiIso {K M : Complex A false} (f : K ⟶ M)
    (hf : quasiIso false f) : quasiIso false ((coefficientComplex F).map f) := by
  intro p
  have := hf p
  have : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map ((graded false p).map f)) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology _ _
  let e := coefficientGradedComparison F p
  have h := e.hom.naturality f
  dsimp only [Functor.comp_map] at h
  have : QuasiIso ((graded false p).map ((coefficientComplex F).map f) ≫ e.hom.app M) := by
    rw [h]
    infer_instance
  exact quasiIso_of_comp_right _ (e.hom.app M)

omit [HasDerivedCategory A] [HasDerivedCategory B]
  [TriangulatedLocalization A false] [TriangulatedLocalization B false] in
private lemma coefficient_inverts : (quasiIso (A := A) false).IsInvertedBy
    (coefficientComplex F ⋙ Q false) := by
  intro K M f hf
  exact Localization.inverts (Q false) (quasiIso false) _ (coefficient_quasiIso F f hf)

private noncomputable def coefficientDerived : Derived (A := A) false ⥤ Derived (A := B) false :=
  Localization.lift (coefficientComplex F ⋙ Q false) (coefficient_inverts F) (Q false)

private noncomputable def coefficientDerivedQ :
    Q false ⋙ coefficientDerived F ≅ coefficientComplex F ⋙ Q false :=
  Localization.fac (coefficientComplex F ⋙ Q false) (coefficient_inverts F) (Q false)

private noncomputable def coefficientOmegaQ :
    Q false ⋙ coefficientDerived F ⋙ T.omega ≅ Q false ⋙ S.omega ⋙ F.mapDerivedCategory :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (coefficientDerivedQ F) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ T.omegaComparison ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft (forget false) F.mapDerivedCategoryFactors.symm ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerRight S.omegaComparison.symm _ ≪≫
    Functor.associator _ _ _

private noncomputable def coefficientOmega :
    coefficientDerived F ⋙ T.omega ≅ S.omega ⋙ F.mapDerivedCategory :=
  (Localization.fullyFaithfulWhiskeringLeft (Q false) (quasiIso false)
    (DerivedCategory B)).preimageIso (coefficientOmegaQ F S T)

private noncomputable def coefficientGrQ (p : ℤ) :
    Q false ⋙ coefficientDerived F ⋙ T.gr p ≅ Q false ⋙ S.gr p ⋙ F.mapDerivedCategory :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (coefficientDerivedQ F) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (T.grComparison p) ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (coefficientGradedComparison F p) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (graded false p) F.mapDerivedCategoryFactors.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (S.grComparison p).symm _ ≪≫ Functor.associator _ _ _

private noncomputable def coefficientGr (p : ℤ) :
    coefficientDerived F ⋙ T.gr p ≅ S.gr p ⋙ F.mapDerivedCategory :=
  (Localization.fullyFaithfulWhiskeringLeft (Q false) (quasiIso false)
    (DerivedCategory B)).preimageIso (coefficientGrQ F S T p)

private noncomputable def highMap {K M : Complex A false} (r : ℤ) (f : K ⟶ M) :
    high false K r ⟶ high false M r := by
  refine ⟨⟨FilteredObject.restrictionSteps f.hom r, fun p ↦ ?_⟩⟩
  let h₁ := ((highObject K.obj r).filtration.step p).arrow ≫
    FilteredObject.restrictionSteps f.hom r
  let h₂ := Subobject.pullbackπ (K.obj.filtration.step r).arrow (K.obj.filtration.step p) ≫
    FilteredObject.restrictionSteps f.hom p
  have hs : h₂ ≫ (M.obj.filtration.step p).arrow =
      h₁ ≫ (M.obj.filtration.step r).arrow := by
    dsimp [h₁, h₂]
    rw [Category.assoc, restriction_square, ← Category.assoc,
      (Subobject.isPullback (K.obj.filtration.step r).arrow (K.obj.filtration.step p)).w,
      Category.assoc, Category.assoc, restriction_square]
    rfl
  exact ⟨(Subobject.isPullback (M.obj.filtration.step r).arrow
      (M.obj.filtration.step p)).lift h₂ h₁ hs,
    (Subobject.isPullback (M.obj.filtration.step r).arrow
      (M.obj.filtration.step p)).lift_snd h₂ h₁ hs⟩

omit [HasDerivedCategory A] [TriangulatedLocalization A false] in
private lemma highMap_inclusion {K M : Complex A false} (r : ℤ) (f : K ⟶ M) :
    highMap r f ≫ highι false M r = highι false K r ≫ f := by
  apply ObjectProperty.hom_ext
  change FilteredObject.Hom.mk _ _ = FilteredObject.Hom.mk _ _
  congr 1
  exact restriction_square f.hom r

private noncomputable def highComplex (r : ℤ) : Complex A false ⥤ Complex A false where
  obj K := high false K r
  map f := highMap r f
  map_id K := by
    apply ObjectProperty.hom_ext
    change FilteredObject.Hom.mk _ _ = FilteredObject.Hom.mk _ _
    congr 1
    change FilteredObject.restrictionSteps (𝟙 K : K ⟶ K).hom r = 𝟙 _
    apply (cancel_mono (K.obj.filtration.step r).arrow).1
    have h := restriction_square (𝟙 K : K ⟶ K).hom r
    change FilteredObject.restrictionSteps (𝟙 K : K ⟶ K).hom r ≫ _ = _ ≫ 𝟙 _ at h
    simpa using h
  map_comp f g := by
    apply ObjectProperty.hom_ext
    change FilteredObject.Hom.mk _ _ = FilteredObject.Hom.mk _ _
    congr 1
    rename_i K M N
    change FilteredObject.restrictionSteps (f ≫ g).hom r =
      FilteredObject.restrictionSteps f.hom r ≫ FilteredObject.restrictionSteps g.hom r
    apply (cancel_mono (N.obj.filtration.step r).arrow).1
    rw [restriction_square, Category.assoc, restriction_square,
      ← Category.assoc, restriction_square]
    change _ ≫ (f.hom.hom ≫ g.hom.hom) = (_ ≫ f.hom.hom) ≫ g.hom.hom
    exact (Category.assoc _ _ _).symm

omit [TriangulatedLocalization A false] in
private lemma highInclusion_cancel (K M : Complex A false) (r : ℤ)
    (x y : (Q false).obj (high false K r) ⟶ (Q false).obj (high false M r))
    (h : x ≫ (Q false).map (highι false M r) = y ≫ (Q false).map (highι false M r)) :
    x = y := by
  obtain ⟨D⟩ := filteredTruncationTriangle A
  have hs (p : ℤ) (hp : p < r) :
      IsZero ((D.gr p).obj ((Q false).obj (high false K r))) :=
    IsZero.of_iso (D.high_support r p ((Q false).obj K) hp)
      ((D.gr p).mapIso (D.high_comparison r K).symm)
  have he := (D.high_hom_bijective r ((Q false).obj (high false K r))
    ((Q false).obj M) hs).injective
  have heq : x ≫ (D.high_comparison r M).inv = y ≫ (D.high_comparison r M).inv := by
    apply he
    dsimp only
    simpa only [Category.assoc, ← D.high_normalization, Iso.inv_hom_id_assoc] using h
  exact (cancel_mono (D.high_comparison r M).inv).1 heq

private lemma highComparison_naturality (S : TruncationCalculus A false)
    {K M : Complex A false} (r : ℤ) (f : K ⟶ M) :
    (S.high r).map ((Q false).map f) ≫ (S.highComparison r M).hom =
      (S.highComparison r K).hom ≫ (Q false).map (highMap r f) := by
  apply (cancel_epi (S.highComparison r K).inv).1
  apply highInclusion_cancel
  rw [Category.assoc, Category.assoc, S.inclusion_normalization]
  simp only [Iso.inv_hom_id_assoc]
  have h := (S.inclusion r).naturality ((Q false).map f)
  dsimp only [Functor.id_map] at h
  rw [h, ← Category.assoc, ← S.inclusion_normalization, Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, highMap_inclusion]

private noncomputable def highComparisonNat (S : TruncationCalculus A false) (r : ℤ) :
    Q false ⋙ S.high r ≅ highComplex r ⋙ Q false :=
  NatIso.ofComponents (S.highComparison r) (fun f ↦ highComparison_naturality S r f)

private noncomputable def highUnderlyingComparison (S : TruncationCalculus A false) (r : ℤ) :
    Q false ⋙ S.high r ⋙ S.omega ≅ (highComplex r ⋙ forget false) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (highComparisonNat S r) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ S.omegaComparison ≪≫ (Functor.associator _ _ _).symm

private noncomputable def coefficientStepComparison (r : ℤ) :
    (highComplex r ⋙ forget false) ⋙ F.mapHomologicalComplex (.up ℤ) ≅
      coefficientComplex F ⋙ highComplex r ⋙ forget false :=
  NatIso.ofComponents (fun K ↦ coefficientStepIso F K.obj r)
    (fun f ↦ coefficientStepIso_naturality F f r)

private noncomputable def coefficientHighOmegaQ :
    Q false ⋙ S.high 0 ⋙ S.omega ⋙ F.mapDerivedCategory ≅
      Q false ⋙ coefficientDerived F ⋙ T.high 0 ⋙ T.omega :=
  Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (highUnderlyingComparison S 0) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (highComplex 0 ⋙ forget false) F.mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (coefficientStepComparison F 0) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (highUnderlyingComparison T 0).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (coefficientDerivedQ F).symm _ ≪≫ Functor.associator _ _ _

private noncomputable def coefficientHighOmega :
    S.high 0 ⋙ S.omega ⋙ F.mapDerivedCategory ≅
      coefficientDerived F ⋙ T.high 0 ⋙ T.omega :=
  (Localization.fullyFaithfulWhiskeringLeft (Q false) (quasiIso false)
    (DerivedCategory B)).preimageIso (coefficientHighOmegaQ F S T)

private lemma coefficientOmega_app (K : Complex A false) :
    (coefficientOmega F S T).hom.app ((Q false).obj K) =
      T.omega.map ((coefficientDerivedQ F).hom.app K) ≫
        T.omegaComparison.hom.app ((coefficientComplex F).obj K) ≫
        F.mapDerivedCategoryFactors.inv.app K.obj.obj ≫
        F.mapDerivedCategory.map (S.omegaComparison.inv.app K) := by
  have h := congr_app
    ((Localization.fullyFaithfulWhiskeringLeft (Q false) (quasiIso false)
      (DerivedCategory B)).map_preimage (coefficientOmegaQ F S T).hom) K
  change (coefficientOmega F S T).hom.app ((Q false).obj K) =
    (coefficientOmegaQ F S T).hom.app K at h
  exact h.trans (by simp [coefficientOmegaQ, forget])

private lemma coefficientGr_app (p : ℤ) (K : Complex A false) :
    (coefficientGr F S T p).hom.app ((Q false).obj K) =
      (T.gr p).map ((coefficientDerivedQ F).hom.app K) ≫
        (T.grComparison p).hom.app ((coefficientComplex F).obj K) ≫
        DerivedCategory.Q.map (coefficientGradeIso F K.obj p).hom ≫
        F.mapDerivedCategoryFactors.inv.app (K.obj.filtration.gradedPiece p) ≫
        F.mapDerivedCategory.map ((S.grComparison p).inv.app K) := by
  have h := congr_app
    ((Localization.fullyFaithfulWhiskeringLeft (Q false) (quasiIso false)
      (DerivedCategory B)).map_preimage (coefficientGrQ F S T p).hom) K
  change (coefficientGr F S T p).hom.app ((Q false).obj K) =
    (coefficientGrQ F S T p).hom.app K at h
  exact h.trans (by simp [coefficientGrQ, coefficientGradedComparison, graded])

private lemma coefficientHighOmega_app (K : Complex A false) :
    (coefficientHighOmega F S T).hom.app ((Q false).obj K) =
      F.mapDerivedCategory.map (S.omega.map (S.highComparison 0 K).hom) ≫
        F.mapDerivedCategory.map (S.omegaComparison.hom.app (high false K 0)) ≫
        F.mapDerivedCategoryFactors.hom.app (K.obj.filtration.step 0) ≫
        DerivedCategory.Q.map (coefficientStepIso F K.obj 0).hom ≫
        T.omegaComparison.inv.app (high false ((coefficientComplex F).obj K) 0) ≫
        T.omega.map (T.highComparison 0 ((coefficientComplex F).obj K)).inv ≫
        T.omega.map ((T.high 0).map ((coefficientDerivedQ F).inv.app K)) := by
  have h := congr_app
    ((Localization.fullyFaithfulWhiskeringLeft (Q false) (quasiIso false)
      (DerivedCategory B)).map_preimage (coefficientHighOmegaQ F S T).hom) K
  change (coefficientHighOmega F S T).hom.app ((Q false).obj K) =
    (coefficientHighOmegaQ F S T).hom.app K at h
  exact h.trans (by simp [coefficientHighOmegaQ, highUnderlyingComparison,
    highComparisonNat, coefficientStepComparison, Category.assoc,
    highComplex, forget, high, highObject])

private lemma coefficient_inclusion_representative (K : Complex A false) :
    (coefficientHighOmega F S T).hom.app ((Q false).obj K) ≫
      T.omega.map ((T.inclusion 0).app ((coefficientDerived F).obj ((Q false).obj K))) ≫
      (coefficientOmega F S T).hom.app ((Q false).obj K) =
      F.mapDerivedCategory.map (S.omega.map ((S.inclusion 0).app ((Q false).obj K))) := by
  let M := (coefficientComplex F).obj K
  have hi := congrArg T.omega.map
    ((T.inclusion 0).naturality ((coefficientDerivedQ F).inv.app K))
  dsimp only [Functor.id_map] at hi
  simp only [Functor.map_comp] at hi
  have hc : T.omega.map ((coefficientDerivedQ F).inv.app K) ≫
      T.omega.map ((coefficientDerivedQ F).hom.app K) = 𝟙 _ := by
    erw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  have ht : T.omega.map (T.highComparison 0 M).inv ≫
      T.omega.map ((T.inclusion 0).app ((Q false).obj M)) =
      T.omega.map ((Q false).map (highι false M 0)) := by
    erw [← Functor.map_comp, ← T.inclusion_normalization, Iso.inv_hom_id_assoc]
  have hn := T.omegaComparison.hom.naturality (highι false M 0)
  dsimp only [Functor.comp_map, forget] at hn
  have ho : T.omegaComparison.inv.app (high false M 0) ≫
      T.omega.map ((Q false).map (highι false M 0)) ≫ T.omegaComparison.hom.app M =
      DerivedCategory.Q.map (M.obj.filtration.step 0).arrow := by
    erw [hn, Iso.inv_hom_id_app_assoc]
    rfl
  have hF := F.mapDerivedCategoryFactors.hom.naturality (K.obj.filtration.step 0).arrow
  dsimp only [Functor.comp_map] at hF
  have hFF : F.mapDerivedCategoryFactors.hom.app (K.obj.filtration.step 0) ≫
      DerivedCategory.Q.map
        ((F.mapHomologicalComplex (.up ℤ)).map (K.obj.filtration.step 0).arrow) ≫
      F.mapDerivedCategoryFactors.inv.app K.obj.obj =
      F.mapDerivedCategory.map (DerivedCategory.Q.map (K.obj.filtration.step 0).arrow) := by
    erw [← Category.assoc, ← hF, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  have hS := S.omegaComparison.hom.naturality (highι false K 0)
  change S.omega.map ((Q false).map (highι false K 0)) ≫ S.omegaComparison.hom.app K =
    S.omegaComparison.hom.app (high false K 0) ≫
      DerivedCategory.Q.map (K.obj.filtration.step 0).arrow at hS
  have hSS : S.omegaComparison.hom.app (high false K 0) ≫
      DerivedCategory.Q.map (K.obj.filtration.step 0).arrow ≫
      S.omegaComparison.inv.app K = S.omega.map ((Q false).map (highι false K 0)) := by
    erw [← Category.assoc, ← hS, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  erw [coefficientHighOmega_app, coefficientOmega_app]
  repeat' erw [Category.assoc]
  erw [reassoc_of% hi, reassoc_of% hc]
  erw [reassoc_of% ht, reassoc_of% ho,
    ← DerivedCategory.Q.map_comp_assoc, coefficientStepIso_arrow, reassoc_of% hFF]
  repeat' erw [← F.mapDerivedCategory.map_comp]
  erw [hSS, ← S.omega.map_comp, S.inclusion_normalization]

private lemma coefficient_projection_representative (K : Complex A false) :
    (coefficientHighOmega F S T).hom.app ((Q false).obj K) ≫
      T.gradeProjection.app ((coefficientDerived F).obj ((Q false).obj K)) ≫
      (coefficientGr F S T 0).hom.app ((Q false).obj K) =
      F.mapDerivedCategory.map (S.gradeProjection.app ((Q false).obj K)) := by
  let M := (coefficientComplex F).obj K
  have hi := T.gradeProjection.naturality ((coefficientDerivedQ F).inv.app K)
  dsimp only [Functor.comp_map] at hi
  have hc : (T.gr 0).map ((coefficientDerivedQ F).inv.app K) ≫
      (T.gr 0).map ((coefficientDerivedQ F).hom.app K) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  have ht : T.omegaComparison.inv.app (high false M 0) ≫
      T.omega.map (T.highComparison 0 M).inv ≫ T.gradeProjection.app ((Q false).obj M) ≫
      (T.grComparison 0).hom.app M =
      DerivedCategory.Q.map (M.obj.filtration.complexQuotientπ 0 1 (by omega)) := by
    erw [T.gradeProjection_normalization, ← T.omega.map_comp_assoc,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp,
      Iso.inv_hom_id_app_assoc]
  have hg : (coefficientStepIso F K.obj 0).hom ≫
      M.obj.filtration.complexQuotientπ 0 1 (by omega) ≫
      (coefficientGradeIso F K.obj 0).hom =
      (F.mapHomologicalComplex (.up ℤ)).map
        (K.obj.filtration.complexQuotientπ 0 1 (by omega)) := by
    erw [← Category.assoc, ← coefficientGradeIso_projection, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
    rfl
  erw [← Category.assoc] at hg
  have hF := F.mapDerivedCategoryFactors.hom.naturality
    (K.obj.filtration.complexQuotientπ 0 1 (by omega))
  dsimp only [Functor.comp_map] at hF
  have hFF : F.mapDerivedCategoryFactors.hom.app (K.obj.filtration.step 0) ≫
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map
        (K.obj.filtration.complexQuotientπ 0 1 (by omega))) ≫
      F.mapDerivedCategoryFactors.inv.app (K.obj.filtration.gradedPiece 0) =
      F.mapDerivedCategory.map
        (DerivedCategory.Q.map (K.obj.filtration.complexQuotientπ 0 1 (by omega))) := by
    erw [← Category.assoc, ← hF, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  have hS := S.gradeProjection_normalization K
  have hSS : S.omega.map (S.highComparison 0 K).hom ≫
      S.omegaComparison.hom.app (high false K 0) ≫
      DerivedCategory.Q.map (K.obj.filtration.complexQuotientπ 0 1 (by omega)) ≫
      (S.grComparison 0).inv.app K = S.gradeProjection.app ((Q false).obj K) := by
    erw [← reassoc_of% hS, Iso.hom_inv_id_app, Category.comp_id]
  erw [coefficientHighOmega_app, coefficientGr_app]
  repeat' erw [Category.assoc]
  erw [reassoc_of% hi, reassoc_of% hc]
  erw [reassoc_of% ht]
  repeat' erw [← DerivedCategory.Q.map_comp_assoc]
  erw [hg, reassoc_of% hFF]
  repeat' erw [← F.mapDerivedCategory.map_comp]
  erw [hSS]

private lemma coefficient_inclusion :
    (coefficientHighOmega F S T).hom ≫
      Functor.whiskerLeft (coefficientDerived F)
        (Functor.whiskerRight (T.inclusion 0) T.omega ≫
          (Functor.leftUnitor T.omega).hom) ≫
      (coefficientOmega F S T).hom =
    (Functor.associator (S.high 0) S.omega F.mapDerivedCategory).inv ≫
      Functor.whiskerRight
        (Functor.whiskerRight (S.inclusion 0) S.omega ≫
          (Functor.leftUnitor S.omega).hom) F.mapDerivedCategory := by
  apply Localization.natTrans_ext (Q false) (quasiIso false)
  intro K
  simpa using coefficient_inclusion_representative F S T K

private lemma coefficient_projection :
    (coefficientHighOmega F S T).hom ≫
      Functor.whiskerLeft (coefficientDerived F) T.gradeProjection ≫
      (coefficientGr F S T 0).hom =
    (Functor.associator (S.high 0) S.omega F.mapDerivedCategory).inv ≫
      Functor.whiskerRight S.gradeProjection F.mapDerivedCategory := by
  apply Localization.natTrans_ext (Q false) (quasiIso false)
  intro K
  simpa using coefficient_projection_representative F S T K

/-- The coefficient functor with its canonical forgetful, graded, and filtration-zero
comparisons. The last two equations retain the inclusion and quotient maps themselves.
Source: Varshavsky, §§5.1.1–5.1.2; Stacks 05S2, 05S4.
(blueprint: lem-trf-exact-filtered-coefficient-change). -/
structure ExactFilteredCoefficientChangeData where
  lift : Derived (A := A) false ⥤ Derived (A := B) false
  omega : lift ⋙ T.omega ≅ S.omega ⋙ F.mapDerivedCategory
  gr : ∀ r : ℤ, lift ⋙ T.gr r ≅ S.gr r ⋙ F.mapDerivedCategory
  highOmega : S.high 0 ⋙ S.omega ⋙ F.mapDerivedCategory ≅ lift ⋙ T.high 0 ⋙ T.omega
  inclusion : ∀ X : Derived (A := A) false,
    highOmega.hom.app X ≫ T.omega.map ((T.inclusion 0).app (lift.obj X)) ≫
        omega.hom.app X =
      F.mapDerivedCategory.map (S.omega.map ((S.inclusion 0).app X))
  projection : ∀ X : Derived (A := A) false,
    highOmega.hom.app X ≫ T.gradeProjection.app (lift.obj X) ≫ (gr 0).hom.app X =
      F.mapDerivedCategory.map (S.gradeProjection.app X)

/-- An exact additive coefficient functor descends to uniformly finite, bounded-below
filtered derived categories, preserving the normalized forgetful and graded comparisons
and the filtration-zero inclusion and quotient squares.
Source: Varshavsky, §§5.1.1–5.1.2; Stacks Project, Tags 05S2 and 05S4.
(blueprint: lem-trf-exact-filtered-coefficient-change).

Proof: Apply F termwise to the underlying complex and to each filtration inclusion,
taking the latter's image as its new filtration step. Exactness preserves monomorphisms,
so these image steps are canonically F of the original steps. They retain both finite
filtration bounds and the strict lower cochain bound. Preservation of cokernels identifies
the new associated graded complex with F of the old one, naturally in filtered maps.
Thus graded quasi-isomorphisms remain graded quasi-isomorphisms and the functor descends
by the localization universal property. The same universal property descends the natural
forgetful and graded comparisons. On complexes, F of each filtration subobject is canonically
the corresponding new filtration subobject. The normalized high comparisons are natural:
this follows by composing with the inclusion and using the high-truncation Hom bijection
from the filtered truncation triangle. These isomorphisms give highOmega after forgetting.
Before localization the inclusion square commutes by
its defining factorization and the grade-zero quotient square commutes by the cokernel
universal property. The normalizations in S and T identify these with exactly the two
displayed squares. Equality after precomposition with the localization functor implies
equality of natural transformations, hence the equations hold on every localized object.
Zero objects, the empty filtration interval, and indices outside the filtration support
are covered by the same image and cokernel calculations. -/
theorem exactFilteredCoefficientChange : Nonempty (ExactFilteredCoefficientChangeData F S T) := by
  refine ⟨{ lift := coefficientDerived F
            omega := coefficientOmega F S T
            gr := coefficientGr F S T
            highOmega := coefficientHighOmega F S T
            inclusion := ?_
            projection := ?_ }⟩
  · intro X
    simpa using congr_app (coefficient_inclusion F S T) X
  · intro X
    simpa using congr_app (coefficient_projection F S T) X

end CochainComplex.FiniteFiltered
