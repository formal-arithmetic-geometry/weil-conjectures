/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Abelian.Filtration
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import Sheaf.Algebra.Homology.FlatConvolutionGradedIso
import Sheaf.Algebra.Homology.FlatKFlatExtension
import Sheaf.CategoryTheory.DerivedCountableSumsExact
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits

/-!
# Convolution tensor and its canonical graded comparison

Source: Stacks Project, More on Algebra, `section-kunneth-spectral-sequence`,
paragraphs preceding Tag 0H7W,
and Tag 0H7Y (blueprint: lem-kun-filtered-tensor-graded-comparison).

The coproduct indexed by `i : ℤ` uses the pair `(i, a - i)` on the diagonal `i + j = a`.
All complexes are unbounded integer cochain complexes. The upstream monoidal tensor on
complexes is `CochainComplex.mapBifunctor` for the module tensor, with the Koszul sign.
The derived tensor is the upstream K-flat derived monoidal tensor; its comparison is the
lax monoidal map of the localization. This is the ordinary tensor of Tag 06Y6, as in
`lem-pc-derived-tensor-second-factor-functor` with identical coefficient rings.
-/

@[expose] public section

set_option autoImplicit false


universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CochainComplex

variable {R : Type u} [CommRing R]

/-- The hypotheses on one filtered complex: finite filtration, flat terms in the underlying,
step and graded complexes, and K-flatness of those same complexes.
Source: Stacks, Section `section-kunneth-spectral-sequence` before Tag 0H7W, finite specialization
(blueprint: lem-kun-filtered-tensor-graded-comparison). -/
def HasKunnethFiltration (P : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)) : Prop :=
  P.filtration.IsFinite ∧
  (∀ n : ℤ, ObjectProperty.flat (P.obj.X n)) ∧
  (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat P.obj ∧
  (∀ i n : ℤ, ObjectProperty.flat
    ((P.filtration.step i : CochainComplex (ModuleCat.{u} R) ℤ).X n)) ∧
  (∀ i n : ℤ, ObjectProperty.flat ((P.filtration.gradedPiece i).X n)) ∧
  (∀ i : ℤ, (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat
    (P.filtration.step i : CochainComplex (ModuleCat.{u} R) ℤ)) ∧
  (∀ i : ℤ, (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat
    (P.filtration.gradedPiece i))

/-- The full category of filtered complexes satisfying the hypotheses of the comparison.
Source: Stacks, Section `section-kunneth-spectral-sequence` before Tag 0H7W
(blueprint: lem-kun-filtered-tensor-graded-comparison). -/
abbrev KunnethFilteredComplex (R : Type u) [CommRing R] :=
  ObjectProperty.FullSubcategory (HasKunnethFiltration (R := R))

/-- The diagonal family of tensors of filtration steps.
Source: Stacks, `section-kunneth-spectral-sequence`, convolution formula before Tag 0H7W
(blueprint: lem-kun-filtered-tensor-graded-comparison). -/
noncomputable def kunnethTensorSteps
    (P Q : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)) (a i : ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  (P.filtration.step i : CochainComplex (ModuleCat.{u} R) ℤ) ⊗
    (Q.filtration.step (a - i) : CochainComplex (ModuleCat.{u} R) ℤ)

/-- The diagonal family of tensors of graded complexes.
Source: Stacks, `section-kunneth-spectral-sequence`, graded comparison before Tag 0H7W
(blueprint: lem-kun-filtered-tensor-graded-comparison). -/
noncomputable def kunnethTensorGraded
    (P Q : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)) (a i : ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  P.filtration.gradedPiece i ⊗ Q.filtration.gradedPiece (a - i)

/-- The sum of the tensor inclusions, whose image is the convolution step.
Source: Stacks, `section-kunneth-spectral-sequence`, convolution formula before Tag 0H7W
(blueprint: lem-kun-filtered-tensor-graded-comparison). -/
noncomputable def kunnethConvolutionArrow
    (P Q : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)) (a : ℤ) :
    (∐ kunnethTensorSteps P Q a) ⟶ P.obj ⊗ Q.obj :=
  Sigma.desc (fun i ↦ (P.filtration.step i).arrow ⊗ₘ (Q.filtration.step (a - i)).arrow)

set_option linter.flexible false in
/-- Successive convolution steps are nested.
Source: Stacks, Section `section-kunneth-spectral-sequence` before Tag 0H7W
(blueprint: lem-kun-filtered-tensor-graded-comparison).

Proof: the summand indexed by `(i,j)` on diagonal `a+1` factors through the summand
`(i-1,j)` on diagonal `a`, using the decreasing inclusion of the first filtration.
The coproduct universal property then gives containment of images. This is Step 2
of the node, and does not use flatness, K-flatness or finiteness. -/
theorem kunnethConvolution_decreasing
    (P Q : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)) (a : ℤ) :
    imageSubobject (kunnethConvolutionArrow P Q (a + 1)) ≤
      imageSubobject (kunnethConvolutionArrow P Q a) := by
  let h : ∀ i : ℤ, kunnethTensorSteps P Q (a + 1) i ⟶
      (∐ kunnethTensorSteps P Q a) := fun i ↦
    (𝟙 (P.filtration.step i : CochainComplex (ModuleCat.{u} R) ℤ) ⊗ₘ
        (Subobject.ofLE (Q.filtration.step (a + 1 - i)) (Q.filtration.step (a - i))
          (Q.filtration.antitone_step (by omega)))) ≫
      Sigma.ι (kunnethTensorSteps P Q a) i
  have hh : kunnethConvolutionArrow P Q (a + 1) =
      Sigma.desc h ≫ kunnethConvolutionArrow P Q a := by
    apply Sigma.hom_ext
    intro i
    simp [kunnethConvolutionArrow, kunnethTensorSteps, h, Category.assoc]
    rw [← id_tensorHom]
    rw [tensorHom_comp_tensorHom]
    simp [Subobject.ofLE_arrow]
  rw [hh]
  exact imageSubobject_comp_le _ _


/-- The actual convolution filtration: the image of the sum of tensor inclusions.
Source: Stacks, `section-kunneth-spectral-sequence`, convolution formula before Tag 0H7W
(blueprint: lem-kun-filtered-tensor-graded-comparison). -/
noncomputable def kunnethConvolution
    (P Q : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)) :
    DecreasingFiltration (P.obj ⊗ Q.obj) where
  F a := imageSubobject (kunnethConvolutionArrow P Q a)
  F_succ_le a := kunnethConvolution_decreasing P Q a

/-- The tensor complex equipped with its convolution filtration.
Source: Stacks, Section `section-kunneth-spectral-sequence` before Tag 0H7W
(blueprint: lem-kun-filtered-tensor-graded-comparison). -/
noncomputable def kunnethConvolutionObject
    (P Q : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)) :
    FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) :=
  ⟨P.obj ⊗ Q.obj, kunnethConvolution P Q⟩

/-- The ordinary graded projection, the cokernel of the next-step inclusion.
Source: Stacks, Homology, Tag 012K
(blueprint: lem-kun-filtered-tensor-graded-comparison). -/
noncomputable abbrev kunnethGradedProjection
    (P : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)) (i : ℤ) :
    (P.filtration.step i : CochainComplex (ModuleCat.{u} R) ℤ) ⟶
      P.filtration.gradedPiece i :=
  P.filtration.complexQuotientπ i (i + 1) (Int.le_add_one le_rfl)

private noncomputable def convolutionLift
    (P Q : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)) (a i : ℤ) :
    (P.filtration.step i : CochainComplex (ModuleCat.{u} R) ℤ) ⊗
        (Q.filtration.step (a - i) : CochainComplex (ModuleCat.{u} R) ℤ) ⟶
      ((kunnethConvolutionObject P Q).filtration.step a : CochainComplex (ModuleCat.{u} R) ℤ) :=
  Sigma.ι (kunnethTensorSteps P Q a) i ≫
    factorThruImageSubobject (kunnethConvolutionArrow P Q a)

private theorem convolutionLift_arrow
    (P Q : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)) (a i : ℤ) :
    convolutionLift P Q a i ≫ ((kunnethConvolutionObject P Q).filtration.step a).arrow =
      (P.filtration.step i).arrow ⊗ₘ (Q.filtration.step (a - i)).arrow := by
  simp [convolutionLift, kunnethConvolutionObject, kunnethConvolution, kunnethConvolutionArrow]

private theorem restrictionSteps_arrow
    {P P' : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)}
    (f : P ⟶ P') (i : ℤ) :
    FilteredObject.restrictionSteps f i ≫ (P'.filtration.step i).arrow =
      (P.filtration.step i).arrow ≫ f.hom :=
  Classical.choose_spec (f.preserves i)

private theorem convolutionMap_preserves
    {P P' Q Q' : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)}
    (f : P ⟶ P') (g : Q ⟶ Q') (a : ℤ) :
    ∃ t : ((kunnethConvolutionObject P Q).filtration.step a : CochainComplex (ModuleCat.{u} R) ℤ) ⟶
        ((kunnethConvolutionObject P' Q').filtration.step a : CochainComplex (ModuleCat.{u} R) ℤ),
      t ≫ ((kunnethConvolutionObject P' Q').filtration.step a).arrow =
        ((kunnethConvolutionObject P Q).filtration.step a).arrow ≫ (f.hom ⊗ₘ g.hom) := by
  let b : ∀ i : ℤ, kunnethTensorSteps P Q a i ⟶ kunnethTensorSteps P' Q' a i :=
    fun i ↦ FilteredObject.restrictionSteps f i ⊗ₘ
      FilteredObject.restrictionSteps g (a - i)
  have hb : kunnethConvolutionArrow P Q a ≫ (f.hom ⊗ₘ g.hom) =
      Limits.Sigma.map b ≫ kunnethConvolutionArrow P' Q' a := by
    apply Sigma.hom_ext
    intro i
    simp [kunnethConvolutionArrow, kunnethTensorSteps, b,
      tensorHom_comp_tensorHom, restrictionSteps_arrow]
  exact ⟨imageSubobjectMap (Arrow.homMk _ _ hb.symm), imageSubobjectMap_arrow _⟩

private noncomputable def convolutionMap
    {P P' Q Q' : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    kunnethConvolutionObject P Q ⟶ kunnethConvolutionObject P' Q' where
  hom := f.hom ⊗ₘ g.hom
  preserves := convolutionMap_preserves f g

private theorem iso_inv_naturality
    {C : Type*} [Category C] {X X' Y Y' : C}
    (e : X ≅ Y) (e' : X' ≅ Y') (f : X ⟶ X') (g : Y ⟶ Y')
    (h : f ≫ e'.hom = e.hom ≫ g) : g ≫ e'.inv = e.inv ≫ f := by
  apply (cancel_mono e'.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, Iso.inv_hom_id_assoc]

private theorem filteredHom_ext
    {P Q : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)}
    (f g : P ⟶ Q) (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

private theorem gradedMapSteps_projection
    {P P' : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)}
    (f : P ⟶ P') (i : ℤ) :
    kunnethGradedProjection P i ≫ FilteredObject.gradedMapSteps f i =
      FilteredObject.restrictionSteps f i ≫ kunnethGradedProjection P' i :=
  Classical.choose_spec (FilteredObject.exists_gradedMap_steps P P' f i)

private theorem restriction_lift_naturality
    {C : Type*} [Category C] [Abelian C] {P P' : FilteredObject C}
    (f : P ⟶ P') (a : ℤ) {X X' : C} (t : X ⟶ X')
    (l : X ⟶ (P.filtration.step a : C))
    (l' : X' ⟶ (P'.filtration.step a : C))
    (s : X ⟶ P.obj) (s' : X' ⟶ P'.obj)
    (hl : l ≫ (P.filtration.step a).arrow = s)
    (hl' : l' ≫ (P'.filtration.step a).arrow = s')
    (hs : t ≫ s' = s ≫ f.hom) :
    t ≫ l' = l ≫ FilteredObject.restrictionSteps f a := by
  apply (cancel_mono (P'.filtration.step a).arrow).1
  have hres : FilteredObject.restrictionSteps f a ≫ (P'.filtration.step a).arrow =
      (P.filtration.step a).arrow ≫ f.hom := Classical.choose_spec (f.preserves a)
  simp only [Category.assoc, hl', hres]
  rw [← Category.assoc, hl]
  exact hs

private theorem convolutionLift_naturality
    {P P' Q Q' : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)}
    (f : P ⟶ P') (g : Q ⟶ Q') (a i : ℤ) :
    (FilteredObject.restrictionSteps f i ⊗ₘ FilteredObject.restrictionSteps g (a - i)) ≫
        convolutionLift P' Q' a i =
      convolutionLift P Q a i ≫ FilteredObject.restrictionSteps (convolutionMap f g) a := by
  apply restriction_lift_naturality (convolutionMap f g) a _ _ _ _ _
    (convolutionLift_arrow P Q a i) (convolutionLift_arrow P' Q' a i)
  change _ = _ ≫ (f.hom ⊗ₘ g.hom)
  simp only [tensorHom_comp_tensorHom, restrictionSteps_arrow]

private theorem convolution_graded_naturality
    {P P' Q Q' : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)}
    (f : P ⟶ P') (g : Q ⟶ Q') (a : ℤ)
    (e : (∐ kunnethTensorGraded P Q a) ≅ (kunnethConvolution P Q).gradedPiece a)
    (e' : (∐ kunnethTensorGraded P' Q' a) ≅ (kunnethConvolution P' Q').gradedPiece a)
    (he : ∀ i, (kunnethGradedProjection P i ⊗ₘ kunnethGradedProjection Q (a - i)) ≫
      Sigma.ι (kunnethTensorGraded P Q a) i ≫ e.hom =
        convolutionLift P Q a i ≫
          kunnethGradedProjection (kunnethConvolutionObject P Q) a)
    (he' : ∀ i, (kunnethGradedProjection P' i ⊗ₘ kunnethGradedProjection Q' (a - i)) ≫
      Sigma.ι (kunnethTensorGraded P' Q' a) i ≫ e'.hom =
        convolutionLift P' Q' a i ≫
          kunnethGradedProjection (kunnethConvolutionObject P' Q') a) :
    Limits.Sigma.map
        (f := kunnethTensorGraded P Q a) (g := kunnethTensorGraded P' Q' a)
        (fun i ↦ FilteredObject.gradedMapSteps f i ⊗ₘ
          FilteredObject.gradedMapSteps g (a - i)) ≫ e'.hom =
      e.hom ≫ FilteredObject.gradedMapSteps (convolutionMap f g) a := by
  apply Sigma.hom_ext
  intro i
  have hL (K : CochainComplex (ModuleCat.{u} R) ℤ) :
      PreservesColimitsOfShape WalkingParallelPair (tensorLeft K) :=
    inferInstanceAs (PreservesColimitsOfShape WalkingParallelPair
      ((Functor.map₂CochainComplex (curriedTensor (ModuleCat.{u} R))).obj K))
  have hR (K : CochainComplex (ModuleCat.{u} R) ℤ) :
      PreservesColimitsOfShape WalkingParallelPair (tensorRight K) :=
    inferInstanceAs (PreservesColimitsOfShape WalkingParallelPair
      ((Functor.map₂CochainComplex (curriedTensor (ModuleCat.{u} R))).flip.obj K))
  have : Epi (kunnethGradedProjection P i) := by
    unfold kunnethGradedProjection DecreasingFiltration.complexQuotientπ
    infer_instance
  have : Epi (kunnethGradedProjection Q (a - i)) := by
    unfold kunnethGradedProjection DecreasingFiltration.complexQuotientπ
    infer_instance
  have : Epi (kunnethGradedProjection P i ⊗ₘ kunnethGradedProjection Q (a - i)) := by
    have : (tensorRight (Q.filtration.step (a - i) :
        CochainComplex (ModuleCat.{u} R) ℤ)).PreservesEpimorphisms :=
      NormalMonoCategory.preservesEpimorphisms_of_preservesCokernels _
    have : (tensorLeft (P.filtration.gradedPiece i)).PreservesEpimorphisms :=
      NormalMonoCategory.preservesEpimorphisms_of_preservesCokernels _
    have h₁ : Epi ((tensorRight (Q.filtration.step (a - i) :
        CochainComplex (ModuleCat.{u} R) ℤ)).map (kunnethGradedProjection P i)) :=
      (tensorRight (Q.filtration.step (a - i) :
        CochainComplex (ModuleCat.{u} R) ℤ)).map_epi _
    have h₂ : Epi ((tensorLeft (P.filtration.gradedPiece i)).map
        (kunnethGradedProjection Q (a - i))) :=
      (tensorLeft (P.filtration.gradedPiece i)).map_epi _
    have : Epi (kunnethGradedProjection P i ▷
        (Q.filtration.step (a - i) : CochainComplex (ModuleCat.{u} R) ℤ)) := h₁
    have : Epi (P.filtration.gradedPiece i ◁ kunnethGradedProjection Q (a - i)) := h₂
    rw [tensorHom_def]
    exact epi_comp _ _
  apply (cancel_epi
    (kunnethGradedProjection P i ⊗ₘ kunnethGradedProjection Q (a - i))).1
  simp only [Sigma.ι_map_assoc]
  have hp :
      (kunnethGradedProjection P i ⊗ₘ kunnethGradedProjection Q (a - i)) ≫
          (FilteredObject.gradedMapSteps f i ⊗ₘ FilteredObject.gradedMapSteps g (a - i)) =
        (FilteredObject.restrictionSteps f i ⊗ₘ
          FilteredObject.restrictionSteps g (a - i)) ≫
          (kunnethGradedProjection P' i ⊗ₘ kunnethGradedProjection Q' (a - i)) := by
    simp only [tensorHom_comp_tensorHom, gradedMapSteps_projection]
  rw [← Category.assoc, hp, Category.assoc, he', ← Category.assoc,
    convolutionLift_naturality, Category.assoc, ← gradedMapSteps_projection]
  simpa only [Category.assoc] using
    congrArg (fun t ↦ t ≫ FilteredObject.gradedMapSteps (convolutionMap f g) a) (he i).symm

set_option linter.flexible false in
private theorem convolution_finite
    (P Q : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ))
    (hP : P.filtration.IsFinite) (hQ : Q.filtration.IsFinite) :
    (kunnethConvolution P Q).IsFinite := by
  obtain ⟨A, C, hA, hC⟩ := hP
  obtain ⟨B, D, hB, hD⟩ := hQ
  refine ⟨A + B, C + D - 1, ?_, ?_⟩
  · have hQA : Q.filtration.step (A + B - A) = ⊤ := by simpa using hB
    have : IsIso (P.filtration.step A).arrow :=
      (Subobject.isIso_arrow_iff_eq_top _).2 hA
    have : IsIso (Q.filtration.step (A + B - A)).arrow :=
      (Subobject.isIso_arrow_iff_eq_top _).2 hQA
    have : Epi ((P.filtration.step A).arrow ⊗ₘ
        (Q.filtration.step (A + B - A)).arrow) := inferInstance
    have : Epi (kunnethConvolutionArrow P Q (A + B)) := by
      have hh : Sigma.ι (kunnethTensorSteps P Q (A + B)) A ≫
          kunnethConvolutionArrow P Q (A + B) =
          (P.filtration.step A).arrow ⊗ₘ (Q.filtration.step (A + B - A)).arrow := by
        simp [kunnethConvolutionArrow, kunnethTensorSteps]
      exact epi_of_epi_fac hh
    have : Epi (imageSubobject (kunnethConvolutionArrow P Q (A + B))).arrow :=
      epi_of_epi_fac (imageSubobject_arrow_comp _)
    have := isIso_of_mono_of_epi
      (imageSubobject (kunnethConvolutionArrow P Q (A + B))).arrow
    exact Subobject.eq_top_of_isIso_arrow
      (imageSubobject (kunnethConvolutionArrow P Q (A + B)))
  · have hz : kunnethConvolutionArrow P Q (C + D - 1) = 0 := by
      apply Sigma.hom_ext
      intro i
      simp only [kunnethConvolutionArrow, kunnethTensorSteps, Sigma.ι_desc, comp_zero]
      by_cases hi : C ≤ i
      · have hPi : P.filtration.step i = ⊥ := by
          apply le_antisymm _ bot_le
          simpa [hC] using P.filtration.antitone_step hi
        have harrow : (P.filtration.step i).arrow = 0 := by
          rw [hPi]
          exact ((isZero_zero _).of_iso Subobject.botCoeIsoZero).eq_of_src _ _
        simp [harrow, tensorHom_def]
      · have hQi : Q.filtration.step (C + D - 1 - i) = ⊥ := by
          apply le_antisymm _ bot_le
          simpa [hD] using Q.filtration.antitone_step (show D ≤ C + D - 1 - i by omega)
        have harrow : (Q.filtration.step (C + D - 1 - i)).arrow = 0 := by
          rw [hQi]
          exact ((isZero_zero _).of_iso Subobject.botCoeIsoZero).eq_of_src _ _
        simp [harrow, tensorHom_def]
    change imageSubobject (kunnethConvolutionArrow P Q (C + D - 1)) = ⊥
    rw [hz, imageSubobject_zero]

private theorem filtration_steps_good
    (P : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ))
    (hfin : P.filtration.IsFinite)
    (hflat : ∀ i n, ObjectProperty.flat ((P.filtration.gradedPiece i).X n))
    (hk : ∀ i, (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat
      (P.filtration.gradedPiece i)) :
    ∀ i : ℤ,
      (∀ n, ObjectProperty.flat
        ((P.filtration.step i : CochainComplex (ModuleCat.{u} R) ℤ).X n)) ∧
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat
        (P.filtration.step i : CochainComplex (ModuleCat.{u} R) ℤ) := by
  obtain ⟨_, b, _, hb⟩ := hfin
  have hz (p : ℤ) (hp : b ≤ p) :
      IsZero (P.filtration.step p : CochainComplex (ModuleCat.{u} R) ℤ) := by
    have hbot : P.filtration.step p = ⊥ := by
      apply le_antisymm _ bot_le
      simpa [hb] using P.filtration.antitone_step hp
    rw [hbot]
    exact (isZero_zero _).of_iso Subobject.botCoeIsoZero
  have hi : ∀ k : ℕ, ∀ p : ℤ, b ≤ p + k →
      (∀ n, ObjectProperty.flat
        ((P.filtration.step p : CochainComplex (ModuleCat.{u} R) ℤ).X n)) ∧
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat
        (P.filtration.step p : CochainComplex (ModuleCat.{u} R) ℤ) := by
    intro k
    induction k with
    | zero =>
      intro p hp
      have hzero := hz p (by simpa using hp)
      exact ⟨fun n ↦ ObjectProperty.prop_of_isZero _
        ((HomologicalComplex.eval _ _ n).map_isZero hzero),
        ObjectProperty.prop_of_isZero _ hzero⟩
    | succ k ih =>
      intro p hp
      obtain ⟨hs, hks⟩ := ih (p + 1) (by omega)
      let i := Subobject.ofLE (P.filtration.step (p + 1)) (P.filtration.step p)
        (P.filtration.antitone_step (by omega))
      let S := ShortComplex.cokernelSequence i
      have hS : S.ShortExact :=
        { exact := ShortComplex.cokernelSequence_exact i
          mono_f := by dsimp [S, ShortComplex.cokernelSequence, i]; infer_instance }
      exact shortExact_flat_kFlat_middle S hS hs (hflat p) hks (hk p)
  intro p
  exact hi (b - p).toNat p (by omega)

private theorem tensor_terms_flat
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : ∀ n, ObjectProperty.flat (P.X n))
    (hQ : ∀ n, ObjectProperty.flat (Q.X n)) (n : ℤ) :
    ObjectProperty.flat ((P ⊗ Q).X n) := by
  change ObjectProperty.flat
    (∐ fun p : {p : ℤ × ℤ // p.1 + p.2 = n} ↦ P.X p.1.1 ⊗ Q.X p.1.2)
  have := closedUnderColimitsOfShape_flat (ModuleCat.{u} R)
    (Discrete {p : ℤ × ℤ // p.1 + p.2 = n})
  exact ObjectProperty.prop_of_isColimit _ (colimit.isColimit _)
    (fun p ↦ ObjectProperty.prop_tensor (hP p.as.1.1) (hQ p.as.1.2))

private theorem sum_terms_flat (P : ℤ → CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : ∀ i n, ObjectProperty.flat ((P i).X n)) (n : ℤ) :
    ObjectProperty.flat ((∐ P).X n) := by
  have := closedUnderColimitsOfShape_flat (ModuleCat.{u} R) (Discrete ℤ)
  exact ObjectProperty.prop_of_isColimit _
    (isColimitOfPreserves (HomologicalComplex.eval _ _ n) (coproductIsCoproduct P))
    (fun i ↦ hP i.as n)

private theorem sum_kFlat (P : ℤ → CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : ∀ i, (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat (P i)) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat (∐ P) := by
  exact ObjectProperty.prop_of_isColimit _ (coproductIsCoproduct P) (fun i ↦ hP i.as)

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

private theorem tensorComparison_isIso
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat P) :
    IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) := by
  have hP' := (HomotopyCategory.kFlat_quotient_obj_iff P).2 hP
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
      ((HomotopyCategory.quotient _ _).obj P)
      ((HomotopyCategory.quotient _ _).obj Q)) :=
    DerivedMonoidal.isIso_counit_app_app_of_kFlat_left DerivedCategory.Qh _ _ _ hP'
  have : IsIso (Functor.LaxMonoidal.μ
      (HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙ DerivedCategory.Qh) P Q) := by
    rw [Functor.LaxMonoidal.comp_μ]
    infer_instance
  change IsIso
    (((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).inv.app P ⊗ₘ
        (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).inv.app Q) ≫
      Functor.LaxMonoidal.μ
        (HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙ DerivedCategory.Qh) P Q ≫
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.app (P ⊗ Q))
  infer_instance

/-- The diagonal family of ordinary K-flat derived tensors in `D(R)`.
Source: Stacks, Section `section-kunneth-spectral-sequence` and Tag 06Y6
(blueprint: lem-kun-filtered-tensor-graded-comparison). -/
noncomputable def kunnethDerivedGraded
    (P Q : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)) (a i : ℤ) :
    DerivedCategory (ModuleCat.{u} R) :=
  DerivedCategory.Q.obj (P.filtration.gradedPiece i) ⊗
    DerivedCategory.Q.obj (Q.filtration.gradedPiece (a - i))

set_option linter.unusedVariables false in
/-- The canonical convolution/graded comparison, natural in both filtered complexes.
Source: Stacks, More on Algebra, `section-kunneth-spectral-sequence`
before Tag 0H7W and Tag 0H7Y
(blueprint: lem-kun-filtered-tensor-graded-comparison).

The maps `l` are fixed by the tensor inclusion equation; the equation for `e` says exactly
that tensors of residue classes map to the residue class of tensors of representatives.
The equations for `c` and `cgr` fix the derived tensor comparisons. The localized
complex sum, with the displayed coprojections, is a coproduct of derived tensors. Thus
`(DerivedCategory.Q.mapIso (e P Q a)).symm` is the displayed derived graded comparison.
Naturality and identity/composition
laws are simultaneous in both variables. The last clause is preservation of quasi-isomorphisms
on every graded complex.

Proof: use `flatConvolution_graded_iso` for the ordinary quotient calculation. The
convolution bounds are the sums of lower bounds and the sum of upper bounds minus one.
Tensor products and direct sums preserve flatness and K-flatness; descending induction
through step/graded short exact sequences uses `shortExact_flat_kFlat_middle` for steps.
Image functoriality constructs the filtered tensor map. Cancel the tensor products of
graded projections to prove simultaneous naturality of the representative equation.
K-flatness makes the localization's lax monoidal comparison invertible, using its
homotopy-category counit. The localization preserves the countable coproduct by
`DerivedCategory.isColimit_mapCocone_countableSum`; precompose its diagram by the tensor
comparison isomorphisms. Finally factor each tensor of graded maps into its two whiskered
maps. K-flatness makes each a quasi-isomorphism, and exact coproducts preserve this property.
The naturality square transfers it to the convolution graded map. -/
theorem filteredTensor_graded_comparison :
    ∃ (m : ∀ (P P' Q Q' : KunnethFilteredComplex R) (f : P ⟶ P') (g : Q ⟶ Q'),
          kunnethConvolutionObject P.obj Q.obj ⟶ kunnethConvolutionObject P'.obj Q'.obj)
      (l : ∀ (P Q : KunnethFilteredComplex R) (a i : ℤ),
          kunnethTensorSteps P.obj Q.obj a i ⟶
            ((kunnethConvolution P.obj Q.obj).step a :
              CochainComplex (ModuleCat.{u} R) ℤ))
      (e : ∀ (P Q : KunnethFilteredComplex R) (a : ℤ),
          (∐ kunnethTensorGraded P.obj Q.obj a) ≅
            (kunnethConvolution P.obj Q.obj).gradedPiece a)
      (c : ∀ P Q : KunnethFilteredComplex R,
          DerivedCategory.Q.obj P.obj.obj ⊗ DerivedCategory.Q.obj Q.obj.obj ≅
            DerivedCategory.Q.obj (P.obj.obj ⊗ Q.obj.obj))
      (cgr : ∀ (P Q : KunnethFilteredComplex R) (a i : ℤ),
          kunnethDerivedGraded P.obj Q.obj a i ≅
            DerivedCategory.Q.obj (kunnethTensorGraded P.obj Q.obj a i)),
      (∀ P Q : KunnethFilteredComplex R,
        HasKunnethFiltration (kunnethConvolutionObject P.obj Q.obj)) ∧
      (∀ (P Q : KunnethFilteredComplex R) (a i : ℤ),
        l P Q a i ≫ ((kunnethConvolution P.obj Q.obj).step a).arrow =
          (P.obj.filtration.step i).arrow ⊗ₘ (Q.obj.filtration.step (a - i)).arrow) ∧
      (∀ (P Q : KunnethFilteredComplex R) (a i : ℤ),
        (kunnethGradedProjection P.obj i ⊗ₘ kunnethGradedProjection Q.obj (a - i)) ≫
            Sigma.ι (kunnethTensorGraded P.obj Q.obj a) i ≫ (e P Q a).hom =
          l P Q a i ≫ kunnethGradedProjection (kunnethConvolutionObject P.obj Q.obj) a) ∧
      (∀ (P P' Q Q' : KunnethFilteredComplex R) (f : P ⟶ P') (g : Q ⟶ Q'),
        (m P P' Q Q' f g).hom = f.hom.hom ⊗ₘ g.hom.hom) ∧
      (∀ (P P' Q Q' : KunnethFilteredComplex R) (f : P ⟶ P') (g : Q ⟶ Q') (a : ℤ),
        CategoryTheory.Limits.Sigma.map
            (f := kunnethTensorGraded P.obj Q.obj a)
            (g := kunnethTensorGraded P'.obj Q'.obj a)
            (fun i ↦ FilteredObject.gradedMapSteps f.hom i ⊗ₘ
            FilteredObject.gradedMapSteps g.hom (a - i)) ≫ (e P' Q' a).hom =
          (e P Q a).hom ≫ FilteredObject.gradedMapSteps (m P P' Q Q' f g) a) ∧
      (∀ P Q : KunnethFilteredComplex R,
        m P P Q Q (𝟙 P) (𝟙 Q) = 𝟙 _) ∧
      (∀ (P P' P'' Q Q' Q'' : KunnethFilteredComplex R)
          (f : P ⟶ P') (f' : P' ⟶ P'') (g : Q ⟶ Q') (g' : Q' ⟶ Q''),
        m P P'' Q Q'' (f ≫ f') (g ≫ g') =
          m P P' Q Q' f g ≫ m P' P'' Q' Q'' f' g') ∧
      (∀ P Q : KunnethFilteredComplex R,
        (c P Q).hom = Functor.LaxMonoidal.μ DerivedCategory.Q P.obj.obj Q.obj.obj) ∧
      (∀ (P Q : KunnethFilteredComplex R) (a i : ℤ),
        (cgr P Q a i).hom = Functor.LaxMonoidal.μ DerivedCategory.Q
          (P.obj.filtration.gradedPiece i) (Q.obj.filtration.gradedPiece (a - i))) ∧
      (∀ (P Q : KunnethFilteredComplex R) (a : ℤ),
        Nonempty (IsColimit (Cofan.mk
          (DerivedCategory.Q.obj (∐ kunnethTensorGraded P.obj Q.obj a))
          (fun i ↦ (cgr P Q a i).hom ≫ DerivedCategory.Q.map
            (Sigma.ι (kunnethTensorGraded P.obj Q.obj a) i))))) ∧
      (∀ (P P' Q Q' : KunnethFilteredComplex R) (f : P ⟶ P') (g : Q ⟶ Q') (a : ℤ),
        DerivedCategory.Q.map (FilteredObject.gradedMapSteps (m P P' Q Q' f g) a) ≫
            (DerivedCategory.Q.mapIso (e P' Q' a)).inv =
          (DerivedCategory.Q.mapIso (e P Q a)).inv ≫ DerivedCategory.Q.map
            (CategoryTheory.Limits.Sigma.map
            (f := kunnethTensorGraded P.obj Q.obj a)
            (g := kunnethTensorGraded P'.obj Q'.obj a)
            (fun i ↦ FilteredObject.gradedMapSteps f.hom i ⊗ₘ
              FilteredObject.gradedMapSteps g.hom (a - i)))) ∧
      (∀ (P P' Q Q' : KunnethFilteredComplex R) (f : P ⟶ P') (g : Q ⟶ Q'),
        (∀ i : ℤ, QuasiIso (FilteredObject.gradedMapSteps f.hom i)) →
        (∀ j : ℤ, QuasiIso (FilteredObject.gradedMapSteps g.hom j)) →
          ∀ a : ℤ, QuasiIso (FilteredObject.gradedMapSteps (m P P' Q Q' f g) a)) := by
  classical
  have hex (P Q : KunnethFilteredComplex R) (a : ℤ) :
      ∃ e : (∐ kunnethTensorGraded P.obj Q.obj a) ≅
          (kunnethConvolution P.obj Q.obj).gradedPiece a,
        ∀ i, (kunnethGradedProjection P.obj i ⊗ₘ
            kunnethGradedProjection Q.obj (a - i)) ≫
            Sigma.ι (kunnethTensorGraded P.obj Q.obj a) i ≫ e.hom =
          convolutionLift P.obj Q.obj a i ≫
            kunnethGradedProjection (kunnethConvolutionObject P.obj Q.obj) a := by
    rcases P.property with ⟨hPf, hP, -, hPs, hPg, -, -⟩
    rcases Q.property with ⟨hQf, hQ, -, hQs, hQg, -, -⟩
    exact flatConvolution_graded_iso P.obj Q.obj hPf hQf hP hQ hPs hQs hPg hQg
      (kunnethConvolution P.obj Q.obj) (fun _ ↦ rfl)
      (convolutionLift P.obj Q.obj) (convolutionLift_arrow P.obj Q.obj) a
  choose e he using hex
  let m := fun (P P' Q Q' : KunnethFilteredComplex R) (f : P ⟶ P') (g : Q ⟶ Q') ↦
    convolutionMap f.hom g.hom
  let l := fun (P Q : KunnethFilteredComplex R) ↦ convolutionLift P.obj Q.obj
  let c : ∀ P Q : KunnethFilteredComplex R,
      DerivedCategory.Q.obj P.obj.obj ⊗ DerivedCategory.Q.obj Q.obj.obj ≅
        DerivedCategory.Q.obj (P.obj.obj ⊗ Q.obj.obj) := fun P Q ↦
    have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P.obj.obj Q.obj.obj) :=
      tensorComparison_isIso _ _ P.property.2.2.1
    asIso (Functor.LaxMonoidal.μ DerivedCategory.Q P.obj.obj Q.obj.obj)
  let cgr : ∀ (P Q : KunnethFilteredComplex R) (a i : ℤ),
      kunnethDerivedGraded P.obj Q.obj a i ≅
        DerivedCategory.Q.obj (kunnethTensorGraded P.obj Q.obj a i) := fun P Q a i ↦
    have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q
        (P.obj.filtration.gradedPiece i) (Q.obj.filtration.gradedPiece (a - i))) :=
      tensorComparison_isIso _ _ (P.property.2.2.2.2.2.2 i)
    asIso (Functor.LaxMonoidal.μ DerivedCategory.Q
      (P.obj.filtration.gradedPiece i) (Q.obj.filtration.gradedPiece (a - i)))
  have hnat (P P' Q Q' : KunnethFilteredComplex R) (f : P ⟶ P') (g : Q ⟶ Q') (a : ℤ) :=
    convolution_graded_naturality f.hom g.hom a (e P Q a) (e P' Q' a)
      (he P Q a) (he P' Q' a)
  have hgood (P Q : KunnethFilteredComplex R) :
      HasKunnethFiltration (kunnethConvolutionObject P.obj Q.obj) := by
    have hfin := convolution_finite P.obj Q.obj P.property.1 Q.property.1
    have hgf (a n : ℤ) : ObjectProperty.flat
        (((kunnethConvolution P.obj Q.obj).gradedPiece a).X n) := by
      apply ObjectProperty.prop_of_iso _ ((HomologicalComplex.eval _ _ n).mapIso (e P Q a))
      exact sum_terms_flat _ (fun i n ↦ tensor_terms_flat _ _
        (P.property.2.2.2.2.1 i) (Q.property.2.2.2.2.1 (a - i)) n) n
    have hgk (a : ℤ) :
        (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat
          ((kunnethConvolution P.obj Q.obj).gradedPiece a) := by
      apply ObjectProperty.prop_of_iso _ (e P Q a)
      exact sum_kFlat _ (fun i ↦ ObjectProperty.prop_tensor
        (P.property.2.2.2.2.2.2 i) (Q.property.2.2.2.2.2.2 (a - i)))
    have hs := filtration_steps_good (kunnethConvolutionObject P.obj Q.obj) hfin hgf hgk
    exact ⟨hfin, tensor_terms_flat _ _ P.property.2.1 Q.property.2.1,
      ObjectProperty.prop_tensor P.property.2.2.1 Q.property.2.2.1,
      fun i ↦ (hs i).1, hgf, fun i ↦ (hs i).2, hgk⟩
  refine ⟨m, l, e, c, cgr, hgood, ?_, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun P Q ↦ convolutionLift_arrow P.obj Q.obj
  · intros
    rfl
  · exact hnat
  · intro P Q
    apply filteredHom_ext
    change (𝟙 P.obj.obj) ⊗ₘ (𝟙 Q.obj.obj) = 𝟙 _
    simp
  · intro P P' P'' Q Q' Q'' f f' g g'
    apply filteredHom_ext
    change (f.hom.hom ≫ f'.hom.hom) ⊗ₘ (g.hom.hom ≫ g'.hom.hom) =
      (f.hom.hom ⊗ₘ g.hom.hom) ≫ (f'.hom.hom ⊗ₘ g'.hom.hom)
    rw [tensorHom_comp_tensorHom]
  · intros
    rfl
  · intros
    rfl
  · intro P Q a
    obtain ⟨hc⟩ := DerivedCategory.isColimit_mapCocone_countableSum
      (ModuleCat.{u} R) ℤ (kunnethTensorGraded P.obj Q.obj a)
    have : PreservesColimit (Discrete.functor (kunnethTensorGraded P.obj Q.obj a))
        DerivedCategory.Q := preservesColimit_of_preserves_colimit_cocone
      (HomologicalComplex.isColimitCoconeOfHasColimitEval _) hc
    have hs := isColimitOfPreserves DerivedCategory.Q
      (coproductIsCoproduct (kunnethTensorGraded P.obj Q.obj a))
    let ec : Discrete.functor (kunnethDerivedGraded P.obj Q.obj a) ≅
        Discrete.functor (kunnethTensorGraded P.obj Q.obj a) ⋙ DerivedCategory.Q :=
      Discrete.natIso (fun i ↦ cgr P Q a i.as)
    exact ⟨(IsColimit.precomposeHomEquiv ec _).symm hs⟩
  · intro P P' Q Q' f g a
    have hn := congrArg DerivedCategory.Q.map (hnat P P' Q Q' f g a)
    simp only [Functor.map_comp] at hn
    exact iso_inv_naturality (DerivedCategory.Q.mapIso (e P Q a))
      (DerivedCategory.Q.mapIso (e P' Q' a)) _ _ hn
  · intro P P' Q Q' f g hf hg a
    let W := HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)
    have ht (i : ℤ) : W
        (FilteredObject.gradedMapSteps f.hom i ⊗ₘ
          FilteredObject.gradedMapSteps g.hom (a - i)) := by
      rw [tensorHom_def]
      exact W.comp_mem _ _
        ((Q.property.2.2.2.2.2.2 (a - i)).whiskerRight (hf i))
        ((P'.property.2.2.2.2.2.2 i).whiskerLeft (hg (a - i)))
    have hsum : W (Limits.Sigma.map
        (f := kunnethTensorGraded P.obj Q.obj a)
        (g := kunnethTensorGraded P'.obj Q'.obj a)
        (fun i ↦ FilteredObject.gradedMapSteps f.hom i ⊗ₘ
          FilteredObject.gradedMapSteps g.hom (a - i))) :=
      W.colimMap (Discrete.natTrans
        (F := Discrete.functor (kunnethTensorGraded P.obj Q.obj a))
        (G := Discrete.functor (kunnethTensorGraded P'.obj Q'.obj a)) (fun i ↦
        FilteredObject.gradedMapSteps f.hom i.as ⊗ₘ
          FilteredObject.gradedMapSteps g.hom (a - i.as))) (fun i ↦ ht i.as)
    have hcomp := W.comp_mem _ _ hsum (W.of_isIso (e P' Q' a).hom)
    rw [hnat P P' Q Q' f g a] at hcomp
    exact (W.precomp_iff _ _ (W.of_isIso (e P Q a).hom)).1 hcomp


end CochainComplex
