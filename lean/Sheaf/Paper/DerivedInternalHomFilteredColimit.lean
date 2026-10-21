/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.HomComplexComponents

public import Sheaf.Paper.DerivedInternalHomFilteredColimitData

import Sheaf.Algebra.Homology.StrictScalarHomChain
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import Sheaf.Paper.InternalHomRepresentativeAPI
import Sheaf.Paper.InternalHomFiniteFreeStage
import Sheaf.Paper.InternalHomFilteredContinuity
import WeilConjectures.FromJoel.CategoryTheory.Abelian.GrothendieckAxioms.Colim
/-! # Filtered finite-free coefficient passage for internal Hom

Source: Bhatt--Scholze, Lemma 6.8.12, Proposition 6.8.14 and Remark 6.8.15;
the conditional ring-sheaf argument in the DAG
(blueprint: lem-sfb-dc-hom-filtered-colimit).

All comparisons below are specified on actual sheafified pure tensors. Colimits
are colimits of strict complexes, followed by localization, as in the node.

## Main definitions

- `comparison`: the unique evaluation-normalized strict coefficient comparison.
- `scalarComparison`: its S-linear chain representative.
- `derivedComparison`: the actual canonical comparison in D(S).

## Main statements

- `filteredColimit_comparison`: the strict colimit roof and its two cocone squares.
- `scalarComparison_restriction`: evaluation-normalized scalar adjunction for that roof.
- `derivedInternalHom_filteredColimit_comparison`: invertibility in D(S).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v r w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace WeilConjectures.SfbHomFilteredColimit

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]

private theorem functorProductSquare
    {A B D : Type*} [Category A] [Category B] [Category D]
    (F : A × B ⥤ D) {X X' : A} {Y Y' : B} (f : X ⟶ X') (g : Y ⟶ Y') :
    F.map (X := (X, Y)) (Y := (X', Y)) (f, 𝟙 Y) ≫
        F.map (X := (X', Y)) (Y := (X', Y')) (𝟙 X', g) =
      F.map (X := (X, Y)) (Y := (X, Y')) (𝟙 X, g) ≫
        F.map (X := (X, Y')) (Y := (X', Y')) (f, 𝟙 Y') := by
  rw [← F.map_comp, ← F.map_comp]
  congr 1
  ext <;> simp

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem filteredColimit_comparison_naturality
    (R : Sheaf J CommRingCat.{max u v r})
    {I : Type (max u v r)} [SmallCategory I] [IsFiltered I]
    [HasColimitsOfShape I (Modules.{u, v, r} J R)]
    (T : I ⥤ Modules.{u, v, r} J R)
    (P L : CochainComplex (Modules.{u, v, r} J R) ℤ) :
    (colimit.post T
        (tensorFixed.{u, v, r} J R ((homFixed.{u, v, r} J R P).obj L)) ≫
          (comparison.{u, v, r} J R P L).app (colimit T) =
      colimMap (Functor.whiskerLeft T (comparison.{u, v, r} J R P L)) ≫
        colimit.post T
          (tensorFixed.{u, v, r} J R ((coefficientHomResolution.{r, u, v} J R).obj L) ⋙
            homFixed.{u, v, r} J R P)) ∧
    (∀ i : I,
      (homFixed.{u, v, r} J R P).map
          ((tensorFixed.{u, v, r} J R L).map (colimit.ι T i)) ≫
        roofDenominator.{u, v, r} J R P L (colimit T) =
      roofDenominator.{u, v, r} J R P L (T.obj i) ≫
        (homFixed.{u, v, r} J R P).map
          ((tensorFixed.{u, v, r} J R
            ((coefficientHomResolution.{r, u, v} J R).obj L)).map (colimit.ι T i))) := by
  constructor
  · apply colimit.hom_ext
    intro i
    simp only [colimit.ι_post_assoc, ι_colimMap_assoc, colimit.ι_post]
    exact (comparison.{u, v, r} J R P L).naturality (colimit.ι T i)
  · intro i
    let F := tensor.{u, v, r} J R
    let H := homFixed.{u, v, r} J R P
    have hs := functorProductSquare F (colimit.ι T i) ((resolutionUnit.{u, v, r} J R).app L)
    exact (H.map_comp _ _).symm.trans ((congrArg H.map hs).trans (H.map_comp _ _))

/-- The strict colimit formula, including the two commuting roof squares.
Source: the node's argument, steps 1--9; Bhatt--Scholze 6.8.12 and 6.8.14
(blueprint: lem-sfb-dc-hom-filtered-colimit).
Proof: the finite-free-stage theorem gives quasi-isomorphisms for each stage numerator
and denominator. The filtered-continuity theorem supplies the colimit denominator,
continuity map and tensor cocone isomorphism. Exact filtered colimits preserve the
stage numerator quasi-isomorphisms. Naturality and the colimit universal property
identify their composite with the colimit numerator preceded by the tensor cocone
isomorphism. Cancel that isomorphism by two-out-of-three. The second strict cocone
square follows from the tensor bifunctor's interchange identity and functoriality
of resolved Hom. Continuity is used at the bounded-below input, and is transported
to its possibly unbounded K-injective replacement by the continuity theorem. -/
theorem filteredColimit_comparison (R : Sheaf J CommRingCat.{max u v r})
    {I : Type (max u v r)} [SmallCategory I] [IsFiltered I]
    [HasColimitsOfShape I (Modules.{u, v, r} J R)]
    [HasExactColimitsOfShape I (Modules.{u, v, r} J R)]
    (T : I ⥤ Modules.{u, v, r} J R)
    (hfree : ∀ i : I, ∃ d : ℕ, Nonempty
      (T.obj i ≅ limit (Discrete.functor (fun _ : Fin d ↦
        SheafOfModules.unit ((sheafCompose J
          (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R)))))
    (P L : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hcont : Continuous.{u, v, r} J R (I := I) P)
    (b : ℤ) (hL : ∀ n : ℤ, n < b → IsZero (L.X n)) :
    QuasiIso ((comparison.{u, v, r} J R P L).app (colimit T)) ∧
    QuasiIso (roofDenominator.{u, v, r} J R P L (colimit T)) ∧
    (∀ i : I, QuasiIso ((comparison.{u, v, r} J R P L).app (T.obj i))) ∧
    (∀ i : I, QuasiIso (roofDenominator.{u, v, r} J R P L (T.obj i))) ∧
    IsIso (colimit.post T
      (tensorFixed.{u, v, r} J R ((homFixed.{u, v, r} J R P).obj L))) ∧
    (colimit.post T
        (tensorFixed.{u, v, r} J R ((homFixed.{u, v, r} J R P).obj L)) ≫
          (comparison.{u, v, r} J R P L).app (colimit T) =
      colimMap (Functor.whiskerLeft T (comparison.{u, v, r} J R P L)) ≫
        colimit.post T
          (tensorFixed.{u, v, r} J R ((coefficientHomResolution.{r, u, v} J R).obj L) ⋙
            homFixed.{u, v, r} J R P)) ∧
    (∀ i : I,
      (homFixed.{u, v, r} J R P).map
          ((tensorFixed.{u, v, r} J R L).map (colimit.ι T i)) ≫
        roofDenominator.{u, v, r} J R P L (colimit T) =
      roofDenominator.{u, v, r} J R P L (T.obj i) ≫
        (homFixed.{u, v, r} J R P).map
          ((tensorFixed.{u, v, r} J R
            ((coefficientHomResolution.{r, u, v} J R).obj L)).map (colimit.ι T i))) := by
  have hstage (i : I) :=
    internalHom_finiteFree_stage.{u, v, r} J R (T.obj i) (hfree i) P L
  obtain ⟨hd, hc, hs⟩ :=
    internalHom_filtered_continuity.{u, v, r} J R T hfree P L hP hcont b hL
  obtain ⟨hn, hv⟩ := filteredColimit_comparison_naturality.{u, v, r} J R T P L
  have ha : QuasiIso
      (colimMap (Functor.whiskerLeft T (comparison.{u, v, r} J R P L))) :=
    (HomologicalComplex.quasiIso (Modules.{u, v, r} J R) (.up ℤ)).colimMap
      (Functor.whiskerLeft T (comparison.{u, v, r} J R P L))
      (fun i ↦ (hstage i).1)
  have hcomp : QuasiIso
      (colimit.post T
          (tensorFixed.{u, v, r} J R ((homFixed.{u, v, r} J R P).obj L)) ≫
        (comparison.{u, v, r} J R P L).app (colimit T)) := by
    rw [hn]
    infer_instance
  have hcolim : QuasiIso ((comparison.{u, v, r} J R P L).app (colimit T)) :=
    quasiIso_of_comp_left
      (colimit.post T
        (tensorFixed.{u, v, r} J R ((homFixed.{u, v, r} J R P).obj L)))
      ((comparison.{u, v, r} J R P L).app (colimit T))
  exact ⟨hcolim, hd, fun i ↦ (hstage i).1, fun i ↦ (hstage i).2, hs, hn, hv⟩

/-- The coefficient algebra as an R-module, using actual restriction of scalars.
Source: Stacks 03EK (blueprint: lem-sfb-dc-hom-filtered-colimit). -/
noncomputable def underlyingCoefficient {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) : Modules.{u, v, r} J R :=
  (SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).map φ)).obj
      (SheafOfModules.unit ((sheafCompose J
        (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj S))

/-- A presentation of the underlying module colimit of the algebra diagram. The two
section equations require exactly the given algebra transitions and colimit injections.
Source: the node's statement, sheaf-algebra colimit
(blueprint: lem-sfb-dc-hom-filtered-colimit). -/
structure ModuleDiagram {R : Sheaf J CommRingCat.{max u v r}}
    {I : Type (max u v r)} [SmallCategory I] [IsFiltered I]
    (S : I ⥤ Sheaf J CommRingCat.{max u v r})
    (algebra : (Functor.const I).obj R ⟶ S) [HasColimit S]
    (φ : R ⟶ colimit S) where
  modules : I ⥤ Modules.{u, v, r} J R
  [hasColimit : HasColimit modules]
  stage : ∀ i : I, modules.obj i ≅ underlyingCoefficient.{u, v, r} J (algebra.app i)
  transition : ∀ (i j : I) (f : i ⟶ j) (U : Cᵒᵖ) (x : (modules.obj i).val.obj U),
    ((stage j).hom.val.app U) ((modules.map f).val.app U x) =
      (S.map f).hom.app U ((stage i).hom.val.app U x)
  colimitIso : colimit modules ≅ underlyingCoefficient.{u, v, r} J φ
  colimit_normalization : ∀ (i : I) (U : Cᵒᵖ) (x : (modules.obj i).val.obj U),
    (colimitIso.hom.val.app U) ((colimit.ι modules i).val.app U x) =
      (colimit.ι S i).hom.app U ((stage i).hom.val.app U x)

attribute [instance] ModuleDiagram.hasColimit

/-- Sheafified scalar-tensor generators, transported only along the specified ordinary
extension-of-scalars object equality.
Source: Stacks 03EK (blueprint: lem-sfb-dc-hom-filtered-colimit). -/
noncomputable def extensionGenerator {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings φ M)
    (M : Modules.{u, v, r} J R) (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (E.obj M).val.obj U :=
  ((eqToHom (h M).symm).val.app U)
    ((CategoryTheory.toSheafify J
      (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))

attribute [local irreducible] extensionGenerator

attribute [local irreducible] coefficientHomResolution resolutionUnit

private theorem scalarModel_exists {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings φ M)
    (hmap : ∀ {M N : Modules.{u, v, r} J R} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (h N).symm) :
    ∃ D : SheafOfModules.StrictScalarHom.Data.{u, v, r} φ, D.extension.functor = E := by
  obtain ⟨D, _⟩ := SheafOfModules.StrictScalarHom.exists_scalarHomChainIdentification.{u, v, r}
    (J := J)
  refine ⟨D R S φ, ?_⟩
  refine CategoryTheory.Functor.ext (F := (D R S φ).extension.functor) (G := E)
    (fun M : Modules.{u, v, r} J R ↦
      ((D R S φ).extension.obj_eq M).trans (h M).symm) ?_
  intro M N f
  rw [(D R S φ).extension.map_eq, hmap]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  rfl

private theorem model_section {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (D : SheafOfModules.StrictScalarHom.Data.{u, v, r} φ)
    (h : ∀ M : Modules.{u, v, r} J R,
      D.extension.functor.obj M = SheafOfModules.changeOfRings φ M)
    (B : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (n : ℤ) (U : Cᵒᵖ) (s : S.obj.obj U) (x : (B.X n).val.obj U) :
    D.extension.section B n U s x =
      extensionGenerator.{u, v, r} J φ D.extension.functor h (B.X n) U s x := by
  unfold extensionGenerator
  rfl

@[no_expose] private noncomputable def extensionPresheafUnit {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings (J := J) φ M)
    (M : Modules.{u, v, r} J R) :
    SheafOfModules.changeOfRingsPresheaf.{v, u, max u v r} (J := J) φ M ⟶
      (PresheafOfModules.restrictScalars (𝟙
        ((sheafCompose J (forget₂ CommRingCat.{max u v r}
          RingCat.{max u v r})).obj S).obj)).obj (E.obj M).val :=
  PresheafOfModules.toSheafify (𝟙 _)
      (CategoryTheory.toSheafify J
        (SheafOfModules.changeOfRingsPresheaf.{v, u, max u v r} (J := J) φ M).presheaf) ≫
    (PresheafOfModules.restrictScalars (𝟙 _)).map ((eqToHom (h M).symm).val)

attribute [local irreducible] extensionPresheafUnit

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem extensionPresheafUnit_apply {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings (J := J) φ M)
    (M : Modules.{u, v, r} J R) (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (extensionPresheafUnit.{u, v, r} J φ E h M).app U
        (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x) =
      extensionGenerator.{u, v, r} J φ E h M U s x := by
  unfold extensionPresheafUnit extensionGenerator
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem extensionGenerator_smul {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings φ M)
    (M : Modules.{u, v, r} J R) (U : Cᵒᵖ) (s t : S.obj.obj U) (x : M.val.obj U) :
    extensionGenerator.{u, v, r} J φ E h M U (s * t) x =
      s • extensionGenerator.{u, v, r} J φ E h M U t x := by
  rw [← extensionPresheafUnit_apply.{u, v, r} J φ E h,
    ← extensionPresheafUnit_apply.{u, v, r} J φ E h]
  have ht := ModuleCat.ExtendScalars.smul_tmul (φ.hom.app U).hom
    (M := M.val.obj U) s t x
  have hv := ((extensionPresheafUnit.{u, v, r} J φ E h M).app U).hom.map_smul s
    (t ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)
  exact (congrArg ((extensionPresheafUnit.{u, v, r} J φ E h M).app U) ht).symm.trans hv

/-- Pure-tensor normalization of the actual S-linear comparison on representatives.
The output uses I_S(E(I_R(L))); the roof denominator is I_S(E(eta_L)).
Source: the node's argument, steps 6 and 10; Stacks 08J9
(blueprint: lem-sfb-dc-hom-filtered-colimit). -/
def ScalarNormalized {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings φ M)
    [E.Additive] (P L : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (a : (E.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((homFixed.{u, v, r} J R P).obj L) ⟶
      (homFixed.{u, v, r} J S
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)).obj
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((coefficientHomResolution.{r, u, v} J R).obj L))) : Prop :=
  ∀ (n p q : ℤ) (hpq : p + n = q) (U : Cᵒᵖ) (s t : S.obj.obj U)
    (f : (((homFixed.{u, v, r} J R P).obj L).X n).val.obj U)
    (x : (P.X p).val.obj U),
    homValue.{u, v, r} J S
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((coefficientHomResolution.{r, u, v} J S).obj
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((coefficientHomResolution.{r, u, v} J R).obj L))) n p q hpq U
        ((a.f n).val.app U (extensionGenerator.{u, v, r} J φ E h _ U s f))
        (extensionGenerator.{u, v, r} J φ E h _ U t x) =
      ((((resolutionUnit.{u, v, r} J S).app
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((coefficientHomResolution.{r, u, v} J R).obj L))).f q).val.app U)
        (extensionGenerator.{u, v, r} J φ E h _ U (s * t)
          (homValue.{u, v, r} J R P
            ((coefficientHomResolution.{r, u, v} J R).obj L) n p q hpq U f x))


omit [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}] in
private theorem model_evaluate_eq (R : Sheaf J CommRingCat.{max u v r})
    (P N : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (n p q : ℤ) (hpq : p + n = q) (U : Cᵒᵖ)
    (f : ((homComplex (R := R) P N).X n).val.obj U) (x : (P.X p).val.obj U) :
    SheafOfModules.StrictScalarHom.evaluate.{u, v, r} P N n p q hpq U f x =
      homValue.{u, v, r} J R P N n p q hpq U f x := by
  rfl

attribute [local irreducible] homValue

private theorem model_normalized {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (D : SheafOfModules.StrictScalarHom.Data.{u, v, r} φ)
    (h : ∀ M : Modules.{u, v, r} J R,
      D.extension.functor.obj M = SheafOfModules.changeOfRings φ M)
    (P L : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (a : D.extension.complex.obj ((homFixed.{u, v, r} J R P).obj L) ⟶
      (homFixed.{u, v, r} J S (D.extension.complex.obj P)).obj
        (D.extension.complex.obj ((coefficientHomResolution.{r, u, v} J R).obj L))) :
    ScalarNormalized.{u, v, r} J φ D.extension.functor h P L a ↔
      SheafOfModules.StrictScalarHom.SigmaFormula D.extension P
        ((coefficientHomResolution.{r, u, v} J R).obj L)
        ((coefficientHomResolution.{r, u, v} J S).obj
          (D.extension.complex.obj ((coefficientHomResolution.{r, u, v} J R).obj L)))
        ((resolutionUnit.{u, v, r} J S).app
          (D.extension.complex.obj ((coefficientHomResolution.{r, u, v} J R).obj L))) a := by
  unfold ScalarNormalized SheafOfModules.StrictScalarHom.SigmaFormula
  simp only [model_evaluate_eq, model_section.{u, v, r} J φ D h]
  have hs (M : Modules.{u, v, r} J R) (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
      extensionGenerator.{u, v, r} J φ D.extension.functor h M U s x =
        s • extensionGenerator.{u, v, r} J φ D.extension.functor h M U 1 x := by
    simpa only [mul_one] using extensionGenerator_smul.{u, v, r} J φ D.extension.functor
      h M U s 1 x
  constructor
  · intro hn n p q hpq U s t f x
    have he := hn n p q hpq U s t f x
    rw [hs _ U (s * t)] at he
    erw [map_smul] at he
    exact he
  · intro hn n p q hpq U s t f x
    rw [hs _ U (s * t)]
    erw [map_smul]
    exact hn n p q hpq U s t f x

/-- Existence and uniqueness of the canonical chain-level scalar comparison.
Source: the node's argument, step 10; Stacks 03EK and 08J9
(blueprint: lem-sfb-dc-hom-filtered-colimit).
Proof: the balanced evaluation formula `(s tensor f)(t tensor x) = st tensor f(x)`
commutes with restrictions and with the Hom differential. Sheafify it, then compose
with the fixed target augmentation. Pure-tensor generation and the actual Hom-product
projections give uniqueness. This constructs the comparison before proving invertibility. -/
theorem scalarComparison_existsUnique {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings φ M)
    (hmap : ∀ {M N : Modules.{u, v, r} J R} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (h N).symm)
    [E.Additive] (P L : CochainComplex (Modules.{u, v, r} J R) ℤ) :
    ∃! a : (E.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((homFixed.{u, v, r} J R P).obj L) ⟶
      (homFixed.{u, v, r} J S
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)).obj
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((coefficientHomResolution.{r, u, v} J R).obj L)),
      ScalarNormalized.{u, v, r} J φ E h P L a := by
  obtain ⟨D, hD⟩ := scalarModel_exists.{u, v, r} J φ E h hmap
  subst E
  let IR := coefficientHomResolution.{r, u, v} J R
  let EC := D.extension.complex
  let N := (coefficientHomResolution.{r, u, v} J S).obj (EC.obj (IR.obj L))
  let q := (resolutionUnit.{u, v, r} J S).app (EC.obj (IR.obj L))
  refine ⟨D.sigma P (IR.obj L) N q, ?_, ?_⟩
  · exact (model_normalized.{u, v, r} J φ D h P L _).mpr
      (D.sigma_formula P (IR.obj L) N q)
  · intro a ha
    exact D.sigma_unique P (IR.obj L) N q a
      ((model_normalized.{u, v, r} J φ D h P L a).mp ha)

/-- The canonical evaluation-transpose comparison, on its specified chain representatives.
Its selection is from a uniqueness assertion, not from mere existence.
Source: the node's argument, step 10 (blueprint: lem-sfb-dc-hom-filtered-colimit). -/
noncomputable def scalarComparison {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings φ M)
    (hmap : ∀ {M N : Modules.{u, v, r} J R} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (h N).symm)
    [E.Additive] (P L : CochainComplex (Modules.{u, v, r} J R) ℤ) :=
  (scalarComparison_existsUnique.{u, v, r} J φ E h hmap P L).exists.choose



attribute [local irreducible] scalarComparison

set_option backward.isDefEq.respectTransparency true in
private theorem scalarComparison_eq_model {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (D : SheafOfModules.StrictScalarHom.Data.{u, v, r} φ)
    (h : ∀ M : Modules.{u, v, r} J R,
      D.extension.functor.obj M = SheafOfModules.changeOfRings φ M)
    (hmap : ∀ {M N : Modules.{u, v, r} J R} (f : M ⟶ N), D.extension.functor.map f =
      eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (h N).symm)
    (P L : CochainComplex (Modules.{u, v, r} J R) ℤ) :
    scalarComparison.{u, v, r} J φ D.extension.functor h hmap P L =
      D.sigma P ((coefficientHomResolution.{r, u, v} J R).obj L)
        ((coefficientHomResolution.{r, u, v} J S).obj
          (D.extension.complex.obj ((coefficientHomResolution.{r, u, v} J R).obj L)))
        ((resolutionUnit.{u, v, r} J S).app
          (D.extension.complex.obj ((coefficientHomResolution.{r, u, v} J R).obj L))) := by
  apply D.sigma_unique
  apply (model_normalized.{u, v, r} J φ D h P L _).mp
  unfold scalarComparison
  exact (scalarComparison_existsUnique.{u, v, r} J φ D.extension.functor
    h hmap P L).exists.choose_spec

open MonoidalCategory SheafOfModules
@[no_expose]
private noncomputable abbrev moduleTensorGenerator
    (R : Sheaf J CommRingCat.{max u v r})
    (M N : Modules.{u, v, r} J R) (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients R
    letI := SheafOfModules.monoidalCategory R
    (M ⊗ N).val.obj U :=
  RepresentativeAPI.pure.{u, v, r} J R M N U x y


@[no_expose] private def fixedUncurryIso
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    (G : A ⥤ B) (F : B ⥤ D ⥤ E) (X : A) :
    Prod.sectR X D ⋙ (G.prod (𝟭 D) ⋙ Functor.uncurry.obj F) ≅ F.obj (G.obj X) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro Y Z f
    change ((F.map (G.map (𝟙 X))).app Y ≫ (F.obj (G.obj X)).map f) ≫ 𝟙 _ =
      𝟙 _ ≫ (F.obj (G.obj X)).map f
    rw [G.map_id, F.map_id]
    simp only [NatTrans.id_app, Category.id_comp, Category.comp_id])


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorComplexGeneratorIso (R : Sheaf J CommRingCat.{max u v r})
    (T : Modules.{u, v, r} J R) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients R
    letI := SheafOfModules.monoidalCategory R
    letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
    ∃ β : (Prod.sectR T (CochainComplex (Modules.{u, v, r} J R) ℤ) ⋙ tensor.{u, v, r} J R) ≅
        (tensorLeft T).mapHomologicalComplex (.up ℤ),
      ∀ (B : CochainComplex (Modules.{u, v, r} J R) ℤ) (n : ℤ) (U : Cᵒᵖ)
        (t : T.val.obj U) (x : (B.X n).val.obj U),
        ((β.hom.app B).f n).val.app U (tensorGenerator.{u, v, r} J R T B n U t x) =
          moduleTensorGenerator.{u, v, r} J R T (B.X n) U t x := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let β : (Prod.sectR T (CochainComplex (Modules.{u, v, r} J R) ℤ) ⋙ tensor.{u, v, r} J R) ≅
      (tensorLeft T).mapHomologicalComplex (.up ℤ) :=
    fixedUncurryIso (HomologicalComplex.single (Modules.{u, v, r} J R) (.up ℤ) 0)
      ((curriedTensor (Modules.{u, v, r} J R)).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ)) T ≪≫
      CochainComplex.map₂HomologicalComplexObjSingleIso (curriedTensor _) T
  refine ⟨β, ?_⟩
  intro B n U t x
  change ((RepresentativeAPI.singleTensorIso.{u, v, r} J R T B).hom.f n).val.app U
    (tensorGenerator.{u, v, r} J R T B n U t x) = _
  exact RepresentativeAPI.tensorGenerator_hom.{u, v, r} J R T B n U t x


private theorem model_tensorSection_eq {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (B : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (n : ℤ) (U : Cᵒᵖ) (s : S.obj.obj U) (x : (B.X n).val.obj U) :
    SheafOfModules.StrictScalarHom.tensorSection.{u, v, r} φ B n U s x =
      RepresentativeAPI.pure.{u, v, r} J R (underlyingCoefficient.{u, v, r} J φ)
        (B.X n) U s x := by
  rfl

attribute [local irreducible] RepresentativeAPI.pure tensor

set_option backward.isDefEq.respectTransparency true in
private theorem model_tensorIso {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (D : SheafOfModules.StrictScalarHom.Data.{u, v, r} φ)
    (h : ∀ M : Modules.{u, v, r} J R,
      D.extension.functor.obj M = SheafOfModules.changeOfRings φ M) :
    ∃ ν : (Prod.sectR (underlyingCoefficient.{u, v, r} J φ)
        (CochainComplex (Modules.{u, v, r} J R) ℤ) ⋙ tensor.{u, v, r} J R) ≅
        D.extension.functor.mapHomologicalComplex (.up ℤ) ⋙
          (SheafOfModules.restrictScalars.{max u v r}
            ((sheafCompose J
              (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).map φ)).mapHomologicalComplex
                (.up ℤ),
      ∀ (B : CochainComplex (Modules.{u, v, r} J R) ℤ) (n : ℤ) (U : Cᵒᵖ)
        (s : S.obj.obj U) (x : (B.X n).val.obj U),
        ((ν.hom.app B).f n).val.app U
          (tensorGenerator.{u, v, r} J R (underlyingCoefficient.{u, v, r} J φ) B n U s x) =
          extensionGenerator.{u, v, r} J φ D.extension.functor h (B.X n) U s x := by
  obtain ⟨β, hβ⟩ := tensorComplexGeneratorIso.{u, v, r} J R
    (underlyingCoefficient.{u, v, r} J φ)
  refine ⟨β ≪≫ D.nu, ?_⟩
  intro B n U s x
  change ((D.nu.hom.app B).f n).val.app U
    (((β.hom.app B).f n).val.app U
      (tensorGenerator.{u, v, r} J R (underlyingCoefficient.{u, v, r} J φ) B n U s x)) = _
  rw [hβ]
  change ((D.nu.hom.app B).f n).val.app U
    (RepresentativeAPI.pure.{u, v, r} J R (underlyingCoefficient.{u, v, r} J φ)
      (B.X n) U s x) = _
  rw [← model_tensorSection_eq]
  exact (D.nu_pure B n U s x).trans (model_section.{u, v, r} J φ D h B n U s x)

private noncomputable abbrev restrictCoefficient {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) :=
  SheafOfModules.restrictScalars.{max u v r}
    ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).map φ)

omit [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}] in
private theorem homValue_post (R : Sheaf J CommRingCat.{max u v r})
    {P Q Q' : CochainComplex (Modules.{u, v, r} J R) ℤ} (g : Q ⟶ Q')
    (n p q : ℤ) (hpq : p + n = q) (U : Cᵒᵖ)
    (z : ((homComplex.{u, v, max u v r, max u v r} (R := R) P Q).X n).val.obj U) (x : (P.X
      p).val.obj U) :
    homValue.{u, v, r} J R P Q' n p q hpq U
      (((((homComplexFunctor.{u, v, max u v r, max u v r} (R := R)).obj (op P)).map g).f
        n).val.app U z) x =
      (g.f q).val.app U (homValue.{u, v, r} J R P Q n p q hpq U z x) := by
  exact RepresentativeAPI.homValue_map_right.{u, v, r} J R P g n p q hpq U z x

attribute [local irreducible] homComplexFunctor

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 800000 in
-- Comparing the two chain models requires many definitional conversions.
/-- Restriction identifies the scalar comparison with the R-linear colimit roof, with
its evaluation normalization fixed explicitly at both chain-level identifications.
Source: the node's argument, step 10; Stacks 03EK and 08J9
(blueprint: lem-sfb-dc-hom-filtered-colimit).
Proof: the tensor identification sends `s tensor x` to the same scalar-extension
pure tensor. The ordinary chain-Hom adjunction sends f to `x ↦ f(1 tensor x)`.
These formulas give inverse chain maps, with signs matching the Hom differential.
Apply the formulas to scalarComparison and use naturality of the R-resolution unit.
Both sides of the square send `s tensor f`, evaluated on x, to the double-resolution
image of `s tensor f(x)`. Pure tensors and Hom-product projections detect equality.
Thus the equation holds before localization, not just at separate derived stages. -/
theorem scalarComparison_restriction {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings φ M)
    (hmap : ∀ {M N : Modules.{u, v, r} J R} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (h N).symm)
    [E.Additive] :
    ∃ ν : (Prod.sectR (underlyingCoefficient.{u, v, r} J φ)
        (CochainComplex (Modules.{u, v, r} J R) ℤ) ⋙ tensor.{u, v, r} J R) ≅
        E.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          (SheafOfModules.restrictScalars
            ((sheafCompose J
              (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).map φ)).mapHomologicalComplex
                (ComplexShape.up ℤ),
      (∀ (B : CochainComplex (Modules.{u, v, r} J R) ℤ) (n : ℤ) (U : Cᵒᵖ)
        (s : S.obj.obj U) (x : (B.X n).val.obj U),
        ((ν.hom.app B).f n).val.app U
          (tensorGenerator.{u, v, r} J R (underlyingCoefficient.{u, v, r} J φ) B n U s x) =
          extensionGenerator.{u, v, r} J φ E h (B.X n) U s x) ∧
      ∃ θ : ∀ (P : CochainComplex (Modules.{u, v, r} J R) ℤ)
          (N : CochainComplex (Modules.{u, v, r} J S) ℤ),
        ((SheafOfModules.restrictScalars
          ((sheafCompose J
            (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).map φ)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
                (homComplex (R := S) ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) N) ≅
          homComplex (R := R) P
            (((SheafOfModules.restrictScalars
              ((sheafCompose J
                (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).map
                  φ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj N),
        (∀ (P : CochainComplex (Modules.{u, v, r} J R) ℤ)
          (N : CochainComplex (Modules.{u, v, r} J S) ℤ)
          (n p q : ℤ) (hpq : p + n = q) (U : Cᵒᵖ)
          (f : ((homComplex (R := S)
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) N).X n).val.obj U)
          (x : (P.X p).val.obj U),
          homValue.{u, v, r} J R P _ n p q hpq U
            (((θ P N).hom.f n).val.app U f) x =
          homValue.{u, v, r} J S _ N n p q hpq U f
            (extensionGenerator.{u, v, r} J φ E h (P.X p) U 1 x)) ∧
        ∀ P L : CochainComplex (Modules.{u, v, r} J R) ℤ,
          ((SheafOfModules.restrictScalars
            ((sheafCompose J
              (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).map φ)).mapHomologicalComplex
                (ComplexShape.up ℤ)).map (scalarComparison.{u, v, r} J φ E h hmap P L) ≫
            (θ P ((coefficientHomResolution.{r, u, v} J S).obj
              ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                ((coefficientHomResolution.{r, u, v} J R).obj L)))).hom ≫
            ((homComplexFunctor.{u, v, max u v r, max u v r} (R := R)).obj (op P)).map
              ((resolutionUnit.{u, v, r} J R).app _) =
          ν.inv.app ((homFixed.{u, v, r} J R P).obj L) ≫
            (comparison.{u, v, r} J R P L).app (underlyingCoefficient.{u, v, r} J φ) ≫
            (homFixed.{u, v, r} J R P).map
              (ν.hom.app ((coefficientHomResolution.{r, u, v} J R).obj L) ≫
                ((SheafOfModules.restrictScalars
                  ((sheafCompose J
                    (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).map
                      φ)).mapHomologicalComplex (ComplexShape.up ℤ)).map
                        ((resolutionUnit.{u, v, r} J S).app
                          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                            ((coefficientHomResolution.{r, u, v} J R).obj L)))) := by
  obtain ⟨D, hD⟩ := scalarModel_exists.{u, v, r} J φ E h hmap
  subst E
  obtain ⟨ν, hν⟩ := model_tensorIso.{u, v, r} J φ D h
  let EC := D.extension.functor.mapHomologicalComplex (.up ℤ)
  let UC := (restrictCoefficient.{u, v, r} J φ).mapHomologicalComplex (.up ℤ)
  let θ : ∀ (P : CochainComplex (Modules.{u, v, r} J R) ℤ)
      (N : CochainComplex (Modules.{u, v, r} J S) ℤ),
      UC.obj (homComplex (R := S) (EC.obj P) N) ≅
        homComplex (R := R) P (UC.obj N) := fun P N ↦ D.theta P N
  have hθ (P : CochainComplex (Modules.{u, v, r} J R) ℤ)
      (N : CochainComplex (Modules.{u, v, r} J S) ℤ) :
      ∀ (n p q : ℤ) (hpq : p + n = q) (U : Cᵒᵖ)
        (f : ((homComplex (R := S) (EC.obj P) N).X n).val.obj U)
        (x : (P.X p).val.obj U),
        homValue.{u, v, r} J R P _ n p q hpq U (((θ P N).hom.f n).val.app U f) x =
          homValue.{u, v, r} J S _ N n p q hpq U f
            (extensionGenerator.{u, v, r} J φ D.extension.functor h (P.X p) U 1 x) := by
    intro n p q hpq U f x
    have ht := D.theta_evaluate P N n p q hpq U f x
    rw [model_evaluate_eq, model_evaluate_eq,
      model_section.{u, v, r} J φ D h] at ht
    exact ht
  refine ⟨ν, hν, θ, hθ, ?_⟩
  intro P L
  let IR := coefficientHomResolution.{r, u, v} J R
  let IS := coefficientHomResolution.{r, u, v} J S
  let T := underlyingCoefficient.{u, v, r} J φ
  let B := (homFixed.{u, v, r} J R P).obj L
  let Q : CochainComplex (Modules.{u, v, r} J R) ℤ :=
    UC.obj (IS.obj (EC.obj (IR.obj L)))
  let g : (tensor.{u, v, r} J R).obj (T, IR.obj L) ⟶ Q :=
    ν.hom.app (IR.obj L) ≫ UC.map ((resolutionUnit.{u, v, r} J S).app (EC.obj (IR.obj L)))
  have hs : ScalarNormalized.{u, v, r} J φ D.extension.functor h P L
      (scalarComparison.{u, v, r} J φ D.extension.functor h hmap P L) := by
    unfold scalarComparison
    exact (scalarComparison_existsUnique.{u, v, r} J φ D.extension.functor
      h hmap P L).exists.choose_spec
  have hr : Normalized.{u, v, r} J R P L (comparison.{u, v, r} J R P L) :=
    (comparison_existsUnique.{u, v, r} J R P L).exists.choose_spec
  apply (Iso.eq_inv_comp (ν.app B)).2
  apply HomologicalComplex.hom_ext
  intro n
  apply RepresentativeAPI.tensorGenerator_hom_ext.{u, v, r} J R T B P (IR.obj Q) n n
  intro p q hpq U s f x
  change homValue.{u, v, r} J R P (IR.obj Q) n p q hpq U
      (((((homComplexFunctor (R := R)).obj (op P)).map
        ((resolutionUnit.{u, v, r} J R).app Q)).f n).val.app U
          (((θ P (IS.obj (EC.obj (IR.obj L)))).hom.f n).val.app U
            (((scalarComparison.{u, v, r} J φ D.extension.functor h hmap P L).f n).val.app U
              (((ν.hom.app B).f n).val.app U
                (tensorGenerator.{u, v, r} J R T B n U s f))))) x =
    homValue.{u, v, r} J R P (IR.obj Q) n p q hpq U
      (((((homComplexFunctor (R := R)).obj (op P)).map (IR.map g)).f n).val.app U
        ((((comparison.{u, v, r} J R P L).app T).f n).val.app U
          (tensorGenerator.{u, v, r} J R T B n U s f))) x
  erw [hν B n U s f]
  rw [homValue_post.{u, v, r} J R (P := P)
    ((resolutionUnit.{u, v, r} J R).app Q) n p q hpq U _ x]
  rw [homValue_post.{u, v, r} J R (P := P) (IR.map g) n p q hpq U _ x]
  let z := (((scalarComparison.{u, v, r} J φ D.extension.functor h hmap P L).f n).val.app U
    (extensionGenerator.{u, v, r} J φ D.extension.functor h (B.X n) U s f))
  have ht := hθ P (IS.obj (EC.obj (IR.obj L))) n p q hpq U z x
  have ht' := congrArg ((((resolutionUnit.{u, v, r} J R).app Q).f q).val.app U) ht
  refine ht'.trans ?_
  have hs0 := hs n p q hpq U s 1 f x
  simp only [mul_one] at hs0
  have htS := congrArg ((((resolutionUnit.{u, v, r} J R).app Q).f q).val.app U)
    hs0
  refine htS.trans ?_
  have htR := congrArg (((IR.map g).f q).val.app U) (hr T n p q hpq U s f x)
  refine Eq.trans ?_ htR.symm
  let v := homValue.{u, v, r} J R P (IR.obj L) n p q hpq U f x
  have hnat : g ≫ (resolutionUnit.{u, v, r} J R).app Q =
      (resolutionUnit.{u, v, r} J R).app ((tensor.{u, v, r} J R).obj (T, IR.obj L)) ≫
        IR.map g := (resolutionUnit.{u, v, r} J R).naturality g
  have hg := congrArg (fun k : (tensor.{u, v, r} J R).obj (T, IR.obj L) ⟶
      IR.obj Q ↦ (k.f q).val.app U
    (tensorGenerator.{u, v, r} J R T (IR.obj L) q U s v)) hnat
  change (((resolutionUnit.{u, v, r} J R).app Q).f q).val.app U
      ((((resolutionUnit.{u, v, r} J S).app (EC.obj (IR.obj L))).f q).val.app U
        (((ν.hom.app (IR.obj L)).f q).val.app U
          (tensorGenerator.{u, v, r} J R T (IR.obj L) q U s v))) = _ at hg
  have hn := congrArg (fun z ↦
    (((resolutionUnit.{u, v, r} J R).app Q).f q).val.app U
      ((((resolutionUnit.{u, v, r} J S).app (EC.obj (IR.obj L))).f q).val.app U z))
        (hν (IR.obj L) q U s v)
  exact hn.symm.trans hg

private noncomputable def singleEvalIso
    {A B : Type*} [Category A] [Category B]
    [HasZeroMorphisms A] [HasZeroMorphisms B] [HasZeroObject A]
    (F : A ⥤ B) [F.PreservesZeroMorphisms] :
    HomologicalComplex.single A (.up ℤ) 0 ⋙ F.mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.eval B (.up ℤ) 0 ≅ F :=
  Functor.isoWhiskerRight (HomologicalComplex.singleCompEvalIsoSelf A (.up ℤ) 0) F

private noncomputable def functorIsoOfComplexIso
    {A B : Type*} [Category A] [Category B]
    [HasZeroMorphisms A] [HasZeroMorphisms B] [HasZeroObject A]
    (F G : A ⥤ B) [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (α : F.mapHomologicalComplex (.up ℤ) ≅ G.mapHomologicalComplex (.up ℤ)) : F ≅ G :=
  (singleEvalIso F).symm ≪≫
    Functor.isoWhiskerLeft (HomologicalComplex.single A (.up ℤ) 0)
      (Functor.isoWhiskerRight α (HomologicalComplex.eval B (.up ℤ) 0)) ≪≫ singleEvalIso G

private theorem coefficientTensorFunctor_exists {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings φ M)
    (hmap : ∀ {M N : Modules.{u, v, r} J R} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (h N).symm)
    [E.Additive] :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients R
    letI := SheafOfModules.monoidalCategory R
    Nonempty (MonoidalCategory.tensorLeft (underlyingCoefficient.{u, v, r} J φ) ≅
      E ⋙ restrictCoefficient.{u, v, r} J φ) := by
  obtain ⟨D, hD⟩ := scalarModel_exists.{u, v, r} J φ E h hmap
  subst E
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
    (underlyingCoefficient.{u, v, r} J φ)
  exact ⟨functorIsoOfComplexIso _ _ D.nu⟩

section ScalarComparisonQuasiIso
open MonoidalCategory SheafOfModules

private theorem finiteFreeColimit_leftExact (R : Sheaf J CommRingCat.{max u v r})
    {I : Type (max u v r)} [SmallCategory I] [IsFiltered I]
    [HasFilteredColimitsOfSize.{max u v r, max u v r} (Modules.{u, v, r} J R)]
    [AB5OfSize.{max u v r, max u v r} (Modules.{u, v, r} J R)]
    (D : I ⥤ Modules.{u, v, r} J R)
    (hfree : ∀ i : I, ∃ d : ℕ, Nonempty
      (D.obj i ≅ limit (Discrete.functor (fun _ : Fin d ↦
        SheafOfModules.unit ((sheafCompose J
          (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R))))) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients R
    letI := SheafOfModules.monoidalCategory R
    PreservesFiniteLimits (tensorLeft (colimit D)) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := RepresentativeAPI.tensorPreadditive.{u, v, r} J R
  have := (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u, v, r}
    J R).1
  have (M : Modules.{u, v, r} J R) :
      PreservesColimitsOfSize.{max u v r, max u v r} (tensorLeft M) :=
    SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R M
  have (M : Modules.{u, v, r} J R) :
      PreservesColimitsOfSize.{max u v r, max u v r} (tensorRight M) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  apply RepresentativeAPI.tensorLeft_colimit_exact D
  intro i
  obtain ⟨d, ⟨α⟩⟩ := hfree i
  have := RepresentativeAPI.tensorLeft_finiteFree_exact (A := Modules.{u, v, r} J R) d
  exact preservesFiniteLimits_of_natIso ((curriedTensor _).mapIso α).symm

private theorem resolution_isKInjective (R : Sheaf J CommRingCat.{max u v r})
    (L : CochainComplex (Modules.{u, v, r} J R) ℤ) :
    ((coefficientHomResolution.{r, u, v} J R).obj L).IsKInjective := by
  exact (RepresentativeAPI.resolutionProperties.{u, v, r} J R L).2


private theorem resolutionUnit_quasiIso (R : Sheaf J CommRingCat.{max u v r})
    (L : CochainComplex (Modules.{u, v, r} J R) ℤ) :
    QuasiIso ((resolutionUnit.{u, v, r} J R).app L) := by
  exact (RepresentativeAPI.resolutionProperties.{u, v, r} J R L).1


private theorem rawHom_map_quasiIso (R : Sheaf J CommRingCat.{max u v r})
    (P : CochainComplex (Modules.{u, v, r} J R) ℤ)
    {Q Q' : CochainComplex (Modules.{u, v, r} J R) ℤ} (g : Q ⟶ Q')
    [Q.IsKInjective] [Q'.IsKInjective] [QuasiIso g] :
    QuasiIso (((homComplexFunctor (R := R)).obj (op P)).map g) := by
  have hh := quasiIso_homComplex_mapOfUniverses.{u, v, r} g (𝟙 P)
  have hi : ((homComplexFunctor (R := R)).map (𝟙 (op P))).app Q = 𝟙 _ :=
    congrArg (fun k ↦ k.app Q) ((homComplexFunctor (R := R)).map_id (op P))
  change QuasiIso (((homComplexFunctor (R := R)).map (𝟙 (op P))).app Q ≫
    ((homComplexFunctor (R := R)).obj (op P)).map g) at hh
  rw [hi, Category.id_comp] at hh
  exact hh

private theorem homFixed_map_quasiIso (R : Sheaf J CommRingCat.{max u v r})
    (P : CochainComplex (Modules.{u, v, r} J R) ℤ)
    {Q Q' : CochainComplex (Modules.{u, v, r} J R) ℤ} (g : Q ⟶ Q') [QuasiIso g] :
    QuasiIso ((homFixed.{u, v, r} J R P).map g) := by
  exact RepresentativeAPI.homFixedQuasiIso.{u, v, r} J R P g

omit [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}] in
private theorem restriction_reflectsIso {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) : (restrictCoefficient.{u, v, r} J φ).ReflectsIsomorphisms := by
  constructor
  intro M N f hf
  let FR := SheafOfModules.toSheaf.{max u v r}
    ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R)
  let FS := SheafOfModules.toSheaf.{max u v r}
    ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj S)
  have h : IsIso (FR.map ((restrictCoefficient.{u, v, r} J φ).map f)) := inferInstance
  have : IsIso (FS.map f) := h
  exact isIso_of_reflects_iso f FS

private theorem extension_preservesHomology {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings φ M)
    (hmap : ∀ {M N : Modules.{u, v, r} J R} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (h N).symm)
    [E.Additive]
    [PreservesFiniteLimits (E ⋙ restrictCoefficient.{u, v, r} J φ)] :
    E.PreservesHomology := by
  let U := SheafOfModules.restrictScalars.{max u v r}
    ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).map φ)
  obtain ⟨hlim, hcolim, ha⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction φ
  have : PreservesFiniteLimits U := hlim
  have : PreservesFiniteColimits U := hcolim
  have : U.ReflectsIsomorphisms := restriction_reflectsIso.{u, v, r} J φ
  have : PreservesFiniteLimits E := preservesFiniteLimits_of_reflects_of_preserves E U
  obtain ⟨adj, _⟩ := ha E h hmap
  have := adj.isLeftAdjoint
  exact Functor.preservesHomologyOfExact E

/-- Filtered finite-free scalar extension preserves derived internal Hom for every
bounded-below second input. The two assertions are precisely the numerator and
invertible denominator of the canonical comparison roof over S.
Source: Bhatt--Scholze 6.8.12, 6.8.14 and 6.8.15, conditional argument in the node
(blueprint: lem-sfb-dc-hom-filtered-colimit).
Proof: apply filteredColimit_comparison to the underlying finite-free module diagram.
Tensor-colimit preservation and exact filtered colimits show that extension of scalars
is exact. Its right adjoint, coefficient restriction, therefore preserves K-injective
complexes. The evaluation-normalized restriction square identifies the scalar numerator
with the R-linear comparison, up to isomorphisms and resolution augmentations. Hom
invariance between K-injective targets and two-out-of-three cancel these factors.
Exact conservative restriction reflects the resulting quasi-isomorphism. Exactness of
extension and invariance of resolved Hom prove the denominator is a quasi-isomorphism.
The generator formulas give strict naturality, which localization carries to the derived
category. No bound on the resolved complex or finite Tor amplitude of P is used. -/
theorem scalarComparison_quasiIso
    (R : Sheaf J CommRingCat.{max u v r})
    {I : Type (max u v r)} [SmallCategory I] [IsFiltered I]
    [HasFilteredColimitsOfSize.{max u v r, max u v r} (Modules.{u, v, r} J R)]
    [AB5OfSize.{max u v r, max u v r} (Modules.{u, v, r} J R)]
    (S : I ⥤ Sheaf J CommRingCat.{max u v r})
    (algebra : (Functor.const I).obj R ⟶ S) [HasColimit S]
    (φ : R ⟶ colimit S)
    (hφ : ∀ i : I, algebra.app i ≫ colimit.ι S i = φ)
    (T : ModuleDiagram.{u, v, r} J S algebra φ)
    (hfree : ∀ i : I, ∃ d : ℕ, Nonempty
      (T.modules.obj i ≅ limit (Discrete.functor (fun _ : Fin d ↦
        SheafOfModules.unit ((sheafCompose J
          (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R)))))
    (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J (colimit S))
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings φ M)
    (hmap : ∀ {M N : Modules.{u, v, r} J R} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (h N).symm)
    [E.Additive] (P L : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hcont : Continuous.{u, v, r} J R (I := I) P)
    (b : ℤ) (hL : ∀ n : ℤ, n < b → IsZero (L.X n)) :
    QuasiIso (scalarComparison.{u, v, r} J φ E h hmap P L) ∧
    QuasiIso ((homFixed.{u, v, r} J (colimit S)
      ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)).map
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((resolutionUnit.{u, v, r} J R).app L)))  := by
  classical
  have := hφ
  let U := restrictCoefficient.{u, v, r} J φ
  let EC := E.mapHomologicalComplex (.up ℤ)
  let UC := U.mapHomologicalComplex (.up ℤ)
  let IR := coefficientHomResolution.{r, u, v} J R
  let IS := coefficientHomResolution.{r, u, v} J (colimit S)
  let A := underlyingCoefficient.{u, v, r} J φ
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  have : PreservesFiniteLimits (tensorLeft (colimit T.modules)) :=
    finiteFreeColimit_leftExact.{u, v, r} J R T.modules hfree
  have : PreservesFiniteLimits (tensorLeft A) :=
    preservesFiniteLimits_of_natIso ((curriedTensor _).mapIso T.colimitIso)
  obtain ⟨α⟩ := coefficientTensorFunctor_exists.{u, v, r} J φ E h hmap
  have : PreservesFiniteLimits (E ⋙ U) := preservesFiniteLimits_of_natIso α
  have : E.PreservesHomology := extension_preservesHomology.{u, v, r} J φ E h hmap
  obtain ⟨hlim, hcolim, ha⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction φ
  have : PreservesFiniteLimits U := hlim
  have : PreservesFiniteColimits U := hcolim
  have : U.PreservesHomology := Functor.preservesHomologyOfExact U
  have : U.ReflectsIsomorphisms := restriction_reflectsIso.{u, v, r} J φ
  obtain ⟨adj, _⟩ := ha E h hmap
  have : U.PreservesKInjectiveComplexes := adj.preservesKInjectiveComplexes
  have := resolutionUnit_quasiIso.{u, v, r} J R L
  have hd : QuasiIso ((homFixed.{u, v, r} J (colimit S) (EC.obj P)).map
      (EC.map ((resolutionUnit.{u, v, r} J R).app L))) :=
    homFixed_map_quasiIso.{u, v, r} J (colimit S) (EC.obj P) _
  refine ⟨?_, hd⟩
  have := (filteredColimit_comparison.{u, v, r} J R T.modules hfree P L hP hcont b hL).1
  have hc : QuasiIso ((comparison.{u, v, r} J R P L).app A) := by
    have hn := (comparison.{u, v, r} J R P L).naturality T.colimitIso.hom
    have : QuasiIso
        ((tensorFixed.{u, v, r} J R ((homFixed.{u, v, r} J R P).obj L)).map
          T.colimitIso.hom ≫ (comparison.{u, v, r} J R P L).app A) := by
      rw [hn]
      infer_instance
    exact quasiIso_of_comp_left
      ((tensorFixed.{u, v, r} J R ((homFixed.{u, v, r} J R P).obj L)).map T.colimitIso.hom)
      ((comparison.{u, v, r} J R P L).app A)
  obtain ⟨ν, _, θ, _, hcomm⟩ := scalarComparison_restriction.{u, v, r} J φ E h hmap
  let Q : CochainComplex (Modules.{u, v, r} J R) ℤ :=
    UC.obj (IS.obj (EC.obj (IR.obj L)))
  have := resolution_isKInjective.{u, v, r} J (colimit S) (EC.obj (IR.obj L))
  have : Q.IsKInjective :=
    Functor.PreservesKInjectiveComplexes.isKInjective_map (F := U)
      (IS.obj (EC.obj (IR.obj L)))
  have := resolution_isKInjective.{u, v, r} J R Q
  have := resolutionUnit_quasiIso.{u, v, r} J R Q
  have hh : QuasiIso (((homComplexFunctor (R := R)).obj (op P)).map
      ((resolutionUnit.{u, v, r} J R).app Q)) :=
    rawHom_map_quasiIso.{u, v, r} J R P (Q := Q) (Q' := IR.obj Q) _
  have := resolutionUnit_quasiIso.{u, v, r} J (colimit S) (EC.obj (IR.obj L))
  let g := ν.hom.app (IR.obj L) ≫
    UC.map ((resolutionUnit.{u, v, r} J (colimit S)).app (EC.obj (IR.obj L)))
  have : QuasiIso g := inferInstance
  have := homFixed_map_quasiIso.{u, v, r} J R P g
  have htotal : QuasiIso (UC.map (scalarComparison.{u, v, r} J φ E h hmap P L) ≫
      (θ P (IS.obj (EC.obj (IR.obj L)))).hom ≫
        ((homComplexFunctor (R := R)).obj (op P)).map
          ((resolutionUnit.{u, v, r} J R).app Q)) := by
    erw [hcomm P L]
    infer_instance
  have : QuasiIso (UC.map (scalarComparison.{u, v, r} J φ E h hmap P L)) :=
    quasiIso_of_comp_right
      (UC.map (scalarComparison.{u, v, r} J φ E h hmap P L))
      ((θ P (IS.obj (EC.obj (IR.obj L)))).hom ≫
        ((homComplexFunctor (R := R)).obj (op P)).map
          ((resolutionUnit.{u, v, r} J R).app Q))
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ U).mp this



end ScalarComparisonQuasiIso

set_option backward.isDefEq.respectTransparency true in
/-- Naturality in both input complexes of the evaluation-normalized scalar map.
Source: the node's argument, step 11; Stacks 08J9
(blueprint: lem-sfb-dc-hom-filtered-colimit).
Proof: evaluate both composites on `s tensor f` and then `t tensor x`. Naturality
of both fixed resolution units makes both values the same postcomposition of
`st tensor f(x)`. Pure tensors and Hom projections give the chain-map equality.
The same identities apply to inverses of quasi-isomorphisms after localization,
so they assert naturality for arbitrary derived morphisms as well. -/
theorem scalarComparison_naturality {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings φ M)
    (hmap : ∀ {M N : Modules.{u, v, r} J R} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (h N).symm)
    [E.Additive] (P P' L L' : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (f : P' ⟶ P) (g : L ⟶ L') :
    (E.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((Functor.uncurry.obj
          (homComplexFunctor.{u, v, max u v r, max u v r} (R := R))).map
            (X := (op P, (coefficientHomResolution.{r, u, v} J R).obj L))
            (Y := (op P', (coefficientHomResolution.{r, u, v} J R).obj L'))
            (f.op, (coefficientHomResolution.{r, u, v} J R).map g)) ≫
        scalarComparison.{u, v, r} J φ E h hmap P' L' =
      scalarComparison.{u, v, r} J φ E h hmap P L ≫
        (Functor.uncurry.obj
          (homComplexFunctor.{u, v, max u v r, max u v r} (R := S))).map
            (X := (op ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P),
              (coefficientHomResolution.{r, u, v} J S).obj
                ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                  ((coefficientHomResolution.{r, u, v} J R).obj L))))
            (Y := (op ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P'),
              (coefficientHomResolution.{r, u, v} J S).obj
                ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                  ((coefficientHomResolution.{r, u, v} J R).obj L'))))
            (((E.mapHomologicalComplex (ComplexShape.up ℤ)).map f).op,
              (coefficientHomResolution.{r, u, v} J S).map
                ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map
                  ((coefficientHomResolution.{r, u, v} J R).map g))) := by
  obtain ⟨D, hD⟩ := scalarModel_exists.{u, v, r} J φ E h hmap
  subst E
  rw [scalarComparison_eq_model.{u, v, r} J φ D h hmap P' L',
    scalarComparison_eq_model.{u, v, r} J φ D h hmap P L]
  let IR := coefficientHomResolution.{r, u, v} J R
  let IS := coefficientHomResolution.{r, u, v} J S
  let EC := D.extension.complex
  let η := resolutionUnit.{u, v, r} J S
  exact D.sigma_natural P P' (IR.obj L) (IR.obj L')
    (IS.obj (EC.obj (IR.obj L))) (IS.obj (EC.obj (IR.obj L')))
    (η.app (EC.obj (IR.obj L))) (η.app (EC.obj (IR.obj L')))
    f (IR.map g) (IS.map (EC.map (IR.map g))) (η.naturality (EC.map (IR.map g)))

attribute [local semireducible] scalarComparison

/-- Compatibility with every map of coefficient-module diagrams, including those induced
by compatible algebra-diagram morphisms. No finite bases occur in the identity.
Source: the node's argument, step 11 (blueprint: lem-sfb-dc-hom-filtered-colimit).
Proof: apply naturality of the strict comparison to the actual colimit map.
Its compatibility with the stage maps is the colimit universal property. -/
theorem comparison_diagram_naturality (R : Sheaf J CommRingCat.{max u v r})
    {I : Type (max u v r)} [SmallCategory I] [IsFiltered I]
    [HasColimitsOfShape I (Modules.{u, v, r} J R)]
    (T T' : I ⥤ Modules.{u, v, r} J R) (τ : T ⟶ T')
    (P L : CochainComplex (Modules.{u, v, r} J R) ℤ) :
    (tensorFixed.{u, v, r} J R ((homFixed.{u, v, r} J R P).obj L)).map (colimMap τ) ≫
        (comparison.{u, v, r} J R P L).app (colimit T') =
      (comparison.{u, v, r} J R P L).app (colimit T) ≫
        (tensorFixed.{u, v, r} J R ((coefficientHomResolution.{r, u, v} J R).obj L) ⋙
          homFixed.{u, v, r} J R P).map (colimMap τ) := by
  exact (comparison.{u, v, r} J R P L).naturality (colimMap τ)


/-- The actual derived comparison roof. The target is the recorded derived internal Hom;
the source is exact scalar extension of its fixed Hom-complex representative. The supplied
quasi-isomorphism is only the proof needed to invert the specified denominator.
Source: the node's argument, steps 3 and 10
(blueprint: lem-sfb-dc-hom-filtered-colimit). -/
noncomputable def derivedComparison {R S : Sheaf J CommRingCat.{max u v r}}
    [HasDerivedCategory.{w} (Modules.{u, v, r} J S)]
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings φ M)
    (hmap : ∀ {M N : Modules.{u, v, r} J R} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (h N).symm)
    [E.Additive] (P L : CochainComplex (Modules.{u, v, r} J R) ℤ)
    [hd : QuasiIso ((homFixed.{u, v, r} J S
      ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)).map
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((resolutionUnit.{u, v, r} J R).app L)))] :
    DerivedCategory.Q.obj ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((homFixed.{u, v, r} J R P).obj L)) ⟶
      (derivedInternalHomOfUniverses.{u, v, r, w} J S).obj
        (op (DerivedCategory.Q.obj ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)),
          DerivedCategory.Q.obj ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) :=
  DerivedCategory.Q.map (scalarComparison.{u, v, r} J φ E h hmap P L) ≫
    inv (DerivedCategory.Q.map ((homFixed.{u, v, r} J S
      ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)).map
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((resolutionUnit.{u, v, r} J R).app L)))) ≫
    (coefficientHomResolutionIso.{r, u, v, w} J S
      ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)).inv

/-- The canonical evaluation-transpose comparison is an isomorphism in D(S).
All presentations are universally quantified: P is any K-flat representative and L any
bounded-below representative, and E has precisely the objects and maps of ordinary scalar
extension from lem-pur-derived-change-of-rings. Thus the statement covers arbitrary
K in D(R) and every L with bounded-below cohomology.
Source: Bhatt--Scholze 6.8.12, 6.8.14 and 6.8.15 and the conditional argument of the node
(blueprint: lem-sfb-dc-hom-filtered-colimit).
Proof: scalarComparison_quasiIso gives the numerator and denominator quasi-isomorphisms.
Localization inverts them; coefficientHomResolutionIso is the fixed factorization for the
recorded internal Hom. Exact finite-free-colimit scalar extension computes derived scalar
extension on every representative, so the source is S tensor^L RHom_R(K,L). The strict
scalarComparison_restriction square identifies its restricted roof with
filteredColimit_comparison, giving the three displayed isomorphisms of the node in order.
The normalization and naturality theorems give independence of bases and all input and
coefficient-diagram naturalities. These are the strict representative steps recorded in the node. -/
theorem derivedInternalHom_filteredColimit_comparison
    (R : Sheaf J CommRingCat.{max u v r})
    {I : Type (max u v r)} [SmallCategory I] [IsFiltered I]
    [HasFilteredColimitsOfSize.{max u v r, max u v r} (Modules.{u, v, r} J R)]
    [AB5OfSize.{max u v r, max u v r} (Modules.{u, v, r} J R)]
    (S : I ⥤ Sheaf J CommRingCat.{max u v r})
    (algebra : (Functor.const I).obj R ⟶ S) [HasColimit S]
    (φ : R ⟶ colimit S)
    (hφ : ∀ i : I, algebra.app i ≫ colimit.ι S i = φ)
    (T : ModuleDiagram.{u, v, r} J S algebra φ)
    (hfree : ∀ i : I, ∃ d : ℕ, Nonempty
      (T.modules.obj i ≅ limit (Discrete.functor (fun _ : Fin d ↦
        SheafOfModules.unit ((sheafCompose J
          (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R)))))
    [HasDerivedCategory.{w} (Modules.{u, v, r} J (colimit S))]
    (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J (colimit S))
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings φ M)
    (hmap : ∀ {M N : Modules.{u, v, r} J R} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (h N).symm)
    [E.Additive] (P L : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hcont : Continuous.{u, v, r} J R (I := I) P)
    (b : ℤ) (hL : ∀ n : ℤ, n < b → IsZero (L.X n)) :
    ∃ hd : QuasiIso ((homFixed.{u, v, r} J (colimit S)
      ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)).map
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((resolutionUnit.{u, v, r} J R).app L))),
      @IsIso _ _ _ _ (@derivedComparison.{u, v, r, w} C _ J _ _ R (colimit S) _
        φ E h hmap _ P L hd) := by
  obtain ⟨hn, hd⟩ := scalarComparison_quasiIso.{u, v, r}
    J R S algebra φ hφ T hfree E h hmap P L hP hcont b hL
  have := hn
  have := hd
  refine ⟨hd, ?_⟩
  dsimp only [derivedComparison]
  infer_instance

end WeilConjectures.SfbHomFilteredColimit
