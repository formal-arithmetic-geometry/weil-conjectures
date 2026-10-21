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

import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import Sheaf.Paper.DerivedInternalHomFilteredColimitData
import all Sheaf.Paper.DerivedInternalHomFilteredColimitData
import Sheaf.Algebra.Homology.StrictScalarHomChain
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Sheaf.Paper.InternalHomFiniteFreeStage
import all Sheaf.Paper.InternalHomFilteredContinuity
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
    change H.map (F.map (X := (T.obj i, L)) (Y := (colimit T, L))
        (colimit.ι T i, 𝟙 L)) ≫
      H.map (F.map (X := (colimit T, L))
        (Y := (colimit T, (coefficientHomResolution.{r, u, v} J R).obj L))
        (𝟙 (colimit T), (resolutionUnit.{u, v, r} J R).app L)) =
      H.map (F.map (X := (T.obj i, L))
        (Y := (T.obj i, (coefficientHomResolution.{r, u, v} J R).obj L))
        (𝟙 (T.obj i), (resolutionUnit.{u, v, r} J R).app L)) ≫
      H.map (F.map (X := (T.obj i, (coefficientHomResolution.{r, u, v} J R).obj L))
        (Y := (colimit T, (coefficientHomResolution.{r, u, v} J R).obj L))
        (colimit.ι T i, 𝟙 _))
    rw [← H.map_comp, ← H.map_comp, ← F.map_comp, ← F.map_comp]
    congr 2

section FilteredAssembly
attribute [local irreducible] comparison roofDenominator tensor homFixed

/-- The strict colimit formula, including the two commuting roof squares.
Source: the node's argument, steps 1--9; Bhatt--Scholze 6.8.12 and 6.8.14
(blueprint: lem-sfb-dc-hom-filtered-colimit).
Proof:
1. Choose a good lower truncation representing the bounded-below input L.
2. Tensor preserves sheaf colimits (lem-weil-pbc-independent-sheaf-tensor-colimits).
A finite-free stage is a finite direct sum of the identity, hence exact, including
rank zero. Exact filtered colimits make tensor by the colimit module exact too.
3. These exact functors preserve quasi-isomorphisms and compute derived tensor
without a Tor bound on P or on Hom(P,I(L)) (lem-pur-derived-change-of-rings).
4. Choose K-flat P (lem-pc-kflat-resolution) and the fixed functorial K-injectives
(prop-pur-kinjective-resolutions-exist). Finite sums of I(L) are K-injective, and
Hom(P,I(L)^d) is Hom(P,I(L))^d, without bounding I(L) or Hom(P,I(L)).
5. The tensor-Hom adjunction on complexes (lem-sc-derived-hom-tensor-total), its
H0/global-homotopy interpretation (lem-pur-hom-complex-global-homotopy), the
K-flat-to-K-injective property (lem-pur-hom-kflat-into-kinjective), and localization
(lem-weil-pbc-kinjective-hom-derived) identify the transpose with chain evaluation.
The cone criterion (lem-pur-quasi-iso-cone-acyclic) and K-flat tensor descent
(lem-weil-pbc-site-derived-tensor-descent) justify tensoring with one K-flat factor.
6. comparison_existsUnique gives the strictly natural maps a_T, and
roofDenominator is F(T tensor eta_L). Both naturality identities are strict.
7. At a finite-free stage a_T and the denominator are quasi-isomorphisms: identify
with finite direct sums and use lem-pur-rhom-well-defined.
8. Take actual termwise filtered colimits of these strict diagrams. Exactness
preserves their quasi-isomorphisms. The two displayed squares are cocone identities.
9. Continuity for the common lower bound on T_i tensor L makes the colimit map
for L a quasi-isomorphism. The denominator at the colimit is one too. The two
squares identify the resulting roof with a_colim, and prove a_colim invertible.
No inference from equality on separate derived-stage coprojections is used. -/
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

end FilteredAssembly

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

private noncomputable def extensionPresheafUnit {R S : Sheaf J CommRingCat.{max u v r}}
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

section ScalarExtensionBridge
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PresheafOfModules.sheafification
  PresheafOfModules.sheafificationAdjunction

private theorem extensionPresheaf_eq {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (M : Modules.{u, v, r} J R) :
    SheafOfModules.changeOfRingsPresheafOfUniverses φ M =
      SheafOfModules.changeOfRingsPresheaf φ M := by
  rfl

private theorem extensionObject_eq {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (M : Modules.{u, v, r} J R) :
    SheafOfModules.changeOfRingsOfUniverses φ M = SheafOfModules.changeOfRings φ M := by
  unfold SheafOfModules.changeOfRingsOfUniverses SheafOfModules.changeOfRings
  rw [extensionPresheaf_eq.{u, v, r} J φ M]
  rfl

private theorem extensionMap_eq {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) {M N : Modules.{u, v, r} J R} (f : M ⟶ N) :
    SheafOfModules.changeOfRingsHomOfUniverses φ M f =
      eqToHom (extensionObject_eq.{u, v, r} J φ M) ≫
        SheafOfModules.changeOfRingsHom φ M f ≫
          eqToHom (extensionObject_eq.{u, v, r} J φ N).symm := by
  apply (conj_eqToHom_iff_heq _ _
    (extensionObject_eq.{u, v, r} J φ M)
    (extensionObject_eq.{u, v, r} J φ N)).mpr
  unfold SheafOfModules.changeOfRingsHomOfUniverses SheafOfModules.changeOfRingsHom
  have hM := extensionPresheaf_eq.{u, v, r} J φ M
  have hN := extensionPresheaf_eq.{u, v, r} J φ N
  cases hM
  cases hN
  rfl

private theorem section_bridge {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (d : SheafOfModules.StrictScalarHom.Data.{u, v, r} φ)
    (h : ∀ M, d.extension.functor.obj M = SheafOfModules.changeOfRings φ M)
    (A : CochainComplex (Modules.{u, v, r} J R) ℤ) (n : ℤ) (U : Cᵒᵖ)
    (s : S.obj.obj U) (x : (A.X n).val.obj U) :
    d.extension.section A n U s x =
      extensionGenerator.{u, v, r} J φ d.extension.functor h (A.X n) U s x := by
  unfold SheafOfModules.StrictScalarHom.Extension.section
    SheafOfModules.scalarExtensionSection extensionGenerator
  have hp := extensionPresheaf_eq.{u, v, r} J φ (A.X n)
  cases hp
  unfold PresheafOfModules.sheafificationAdjunction
  rfl

private theorem extensionFunctor_eq {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (d : SheafOfModules.StrictScalarHom.Data.{u, v, r} φ)
    (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings φ M)
    (hmap : ∀ {M N : Modules.{u, v, r} J R} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (h N).symm) :
    d.extension.functor = E := by
  refine CategoryTheory.Functor.ext
    (fun M ↦ (d.extension.obj_eq M).trans
      ((extensionObject_eq.{u, v, r} J φ M).trans (h M).symm)) ?_
  intro M N f
  rw [d.extension.map_eq, hmap, extensionMap_eq.{u, v, r} J φ f]
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp,
    Category.comp_id]
  simp only [Category.assoc, eqToHom_trans]

end ScalarExtensionBridge

attribute [local irreducible] homValue homComplexFunctor

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

private theorem scalarNormalized_iff {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (d : SheafOfModules.StrictScalarHom.Data.{u, v, r} φ)
    (h : ∀ M, d.extension.functor.obj M = SheafOfModules.changeOfRings φ M)
    (P L : CochainComplex (Modules.{u, v, r} J R) ℤ)
    {a : (d.extension.complex.obj ((homFixed.{u, v, r} J R P).obj L)) ⟶
      (homFixed.{u, v, r} J S (d.extension.complex.obj P)).obj
        (d.extension.complex.obj ((coefficientHomResolution.{r, u, v} J R).obj L))} :
    ScalarNormalized.{u, v, r} J φ d.extension.functor h P L a ↔
      SheafOfModules.StrictScalarHom.SigmaFormula d.extension P
        ((coefficientHomResolution.{r, u, v} J R).obj L)
        ((coefficientHomResolution.{r, u, v} J S).obj
          (d.extension.complex.obj ((coefficientHomResolution.{r, u, v} J R).obj L)))
        ((resolutionUnit.{u, v, r} J S).app
          (d.extension.complex.obj ((coefficientHomResolution.{r, u, v} J R).obj L))) a := by
  let A := (coefficientHomResolution.{r, u, v} J R).obj L
  let τ := (resolutionUnit.{u, v, r} J S).app (d.extension.complex.obj A)
  have he (n p q : ℤ) (hpq : p + n = q) (U : Cᵒᵖ) (s t : S.obj.obj U)
      (f : ((homComplex (R := R) P A).X n).val.obj U) (x : (P.X p).val.obj U) :
      (τ.f q).val.app U (extensionGenerator.{u, v, r} J φ d.extension.functor h
        (A.X q) U (s * t) (homValue.{u, v, r} J R P A n p q hpq U f x)) =
        (s * t) • (τ.f q).val.app U (extensionGenerator.{u, v, r} J φ
          d.extension.functor h (A.X q) U 1
            (homValue.{u, v, r} J R P A n p q hpq U f x)) := by
    have hh := extensionGenerator_smul.{u, v, r} J φ d.extension.functor h
      (A.X q) U (s * t) 1 (homValue.{u, v, r} J R P A n p q hpq U f x)
    simp only [mul_one] at hh
    rw [hh]
    exact ((τ.f q).val.app U).hom.map_smul _ _
  constructor
  · intro hn n p q hpq U s t f x
    have hh := (hn n p q hpq U s t f x).trans (he n p q hpq U s t f x)
    simpa only [homValue, SheafOfModules.StrictScalarHom.evaluate,
      section_bridge.{u, v, r} J φ d h, SheafOfModules.StrictScalarHom.Extension.complex,
      homFixed] using! hh
  · intro hn n p q hpq U s t f x
    have hh := hn n p q hpq U s t f x
    have hh' := he n p q hpq U s t f x
    simp only [SheafOfModules.StrictScalarHom.evaluate,
      section_bridge.{u, v, r} J φ d h] at hh
    have hk : homValue.{u, v, r} J S (d.extension.complex.obj P) _ n p q hpq U
        ((a.f n).val.app U (extensionGenerator.{u, v, r} J φ d.extension.functor h
          ((homComplex (R := R) P A).X n) U s f))
        (extensionGenerator.{u, v, r} J φ d.extension.functor h (P.X p) U t x) =
        (s * t) • (τ.f q).val.app U (extensionGenerator.{u, v, r} J φ
          d.extension.functor h (A.X q) U 1
            (homValue.{u, v, r} J R P A n p q hpq U f x)) := by
      simpa only [homValue] using! hh
    exact hk.trans hh'.symm

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
  obtain ⟨D, _⟩ := @SheafOfModules.StrictScalarHom.exists_scalarHomChainIdentification.{u, v, r}
    C _ J inferInstance inferInstance inferInstance
  let d := D R S φ
  have he := extensionFunctor_eq.{u, v, r} J φ d E h hmap
  subst E
  let A := (coefficientHomResolution.{r, u, v} J R).obj L
  let V := (coefficientHomResolution.{r, u, v} J S).obj (d.extension.complex.obj A)
  let τ := (resolutionUnit.{u, v, r} J S).app (d.extension.complex.obj A)
  refine ⟨d.sigma P A V τ,
    (scalarNormalized_iff.{u, v, r} J φ d h P L).mpr (d.sigma_formula P A V τ), ?_⟩
  intro a ha
  exact d.sigma_unique P A V τ a ((scalarNormalized_iff.{u, v, r} J φ d h P L).mp ha)

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

section RestrictionProof

set_option backward.isDefEq.respectTransparency false

open HomologicalComplex CategoryTheory.MonoidalCategory
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

attribute [local irreducible] SheafOfModules.monoidalCategory
  PresheafOfModules.sheafification PresheafOfModules.sheafificationAdjunction

private noncomputable def tensorTermwiseIso (R : Sheaf J CommRingCat.{max u v r})
    (T : Modules.{u, v, r} J R) :
    let := SheafOfModules.monoidalCategory R
    let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
    (Prod.sectR T (CochainComplex (Modules.{u, v, r} J R) ℤ) ⋙
      tensor.{u, v, r} J R) ≅ (tensorLeft T).mapHomologicalComplex (.up ℤ) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let Q := (curriedTensor (Modules.{u, v, r} J R)).map₂CochainComplex
  let σ := single (Modules.{u, v, r} J R) (.up ℤ) 0
  refine NatIso.ofComponents (singleTensorIso.{u, v, r} J R T) ?_
  intro X Y f
  change ((Q.map (σ.map (𝟙 T))).app X ≫ (Q.obj (σ.obj T)).map f) ≫
      (singleTensorIso.{u, v, r} J R T Y).hom = _
  rw [σ.map_id, Q.map_id, NatTrans.id_app, Category.id_comp]
  exact CochainComplex.mapBifunctorSingle₁Iso_hom_naturality
    (curriedTensor (Modules.{u, v, r} J R)) T f

attribute [local irreducible] singleTensorIso tensorGenerator tensor comparison scalarComparison

set_option backward.isDefEq.respectTransparency false

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
  obtain ⟨D, _⟩ := @SheafOfModules.StrictScalarHom.exists_scalarHomChainIdentification.{u, v, r}
    C _ J inferInstance inferInstance inferInstance
  let d := D R S φ
  have he := extensionFunctor_eq.{u, v, r} J φ d E h hmap
  subst E
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let e := tensorTermwiseIso.{u, v, r} J R (underlyingCoefficient.{u, v, r} J φ)
  let νt : (tensorLeft (underlyingCoefficient.{u, v, r} J φ)).mapHomologicalComplex
      (.up ℤ) ≅ d.extension.complex ⋙
        SheafOfModules.StrictScalarHom.restriction.{u, v, r} φ := by
    simpa only [SheafOfModules.StrictScalarHom.tensor,
      SheafOfModules.StrictScalarHom.scalarModule, underlyingCoefficient] using d.nu
  let ν := e ≪≫ νt
  have hν (B : CochainComplex (Modules.{u, v, r} J R) ℤ) (n : ℤ) (U : Cᵒᵖ)
      (s : S.obj.obj U) (x : (B.X n).val.obj U) :
      ((ν.hom.app B).f n).val.app U
          (tensorGenerator.{u, v, r} J R (underlyingCoefficient.{u, v, r} J φ) B n U s x) =
        extensionGenerator.{u, v, r} J φ d.extension.functor h (B.X n) U s x := by
    change ((d.nu.hom.app B).f n).val.app U
      (((singleTensorIso.{u, v, r} J R (underlyingCoefficient.{u, v, r} J φ) B).hom.f n).val.app U
        (tensorGenerator.{u, v, r} J R (underlyingCoefficient.{u, v, r} J φ) B n U s x)) = _
    rw [tensorGenerator_hom.{u, v, r} J R]
    exact (d.nu_pure B n U s x).trans
      (section_bridge.{u, v, r} J φ d h B n U s x)
  clear_value ν
  have hθ (P : CochainComplex (Modules.{u, v, r} J R) ℤ)
      (N : CochainComplex (Modules.{u, v, r} J S) ℤ)
      (n p q : ℤ) (hpq : p + n = q) (U : Cᵒᵖ)
      (f : ((homComplex (R := S) (d.extension.complex.obj P) N).X n).val.obj U)
      (x : (P.X p).val.obj U) :
      homValue.{u, v, r} J R P _ n p q hpq U
          (((d.theta P N).hom.f n).val.app U f) x =
        homValue.{u, v, r} J S _ N n p q hpq U f
          (extensionGenerator.{u, v, r} J φ d.extension.functor h (P.X p) U 1 x) := by
    have hh := d.theta_evaluate P N n p q hpq U f x
    rw [section_bridge.{u, v, r} J φ d h P p U 1 x] at hh
    simpa only [homValue, SheafOfModules.StrictScalarHom.evaluate] using hh
  refine ⟨ν, hν, d.theta, hθ, ?_⟩
  intro P L
  let EC := d.extension.complex
  let Uφ := SheafOfModules.StrictScalarHom.restriction.{u, v, r} φ
  let IR := coefficientHomResolution.{r, u, v} J R
  let IS := coefficientHomResolution.{r, u, v} J S
  let B := (homFixed.{u, v, r} J R P).obj L
  let A := IR.obj L
  let V := IS.obj (EC.obj A)
  let γ := ν.hom.app A ≫ Uφ.map ((resolutionUnit.{u, v, r} J S).app (EC.obj A))
  have hn : ScalarNormalized.{u, v, r} J φ d.extension.functor h P L
      (scalarComparison.{u, v, r} J φ d.extension.functor h hmap P L) := by
    unfold scalarComparison
    have hh := scalarComparison_existsUnique.{u, v, r} J φ d.extension.functor h hmap P L
    exact hh.exists.choose_spec
  have ha : Normalized.{u, v, r} J R P L (comparison.{u, v, r} J R P L) := by
    unfold comparison
    exact (comparison_existsUnique.{u, v, r} J R P L).exists.choose_spec
  change _ = ν.inv.app B ≫ _
  apply (cancel_epi (ν.hom.app B)).mp
  have hc : ν.hom.app B ≫ ν.inv.app B = 𝟙 _ := ν.hom_inv_id_app B
  simp only [← Category.assoc, hc, Category.id_comp]
  apply HomologicalComplex.hom_ext
  intro n
  apply tensorGenerator_hom_ext.{u, v, r} J R (underlyingCoefficient.{u, v, r} J φ)
    B P (IR.obj (Uφ.obj V)) n n
  intro p q hpq U s f x
  simp only [HomologicalComplex.comp_f, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply]
  let α := scalarComparison.{u, v, r} J φ d.extension.functor h hmap P L
  let c := (comparison.{u, v, r} J R P L).app (underlyingCoefficient.{u, v, r} J φ)
  let η := (resolutionUnit.{u, v, r} J R).app (Uφ.obj V)
  let τ := (resolutionUnit.{u, v, r} J S).app (EC.obj A)
  let z := tensorGenerator.{u, v, r} J R (underlyingCoefficient.{u, v, r} J φ) B n U s f
  let w := homValue.{u, v, r} J R P A n p q hpq U f x
  let y := tensorGenerator.{u, v, r} J R (underlyingCoefficient.{u, v, r} J φ) A q U s w
  have hscalar := hn n p q hpq U s 1 f x
  simp only [mul_one] at hscalar
  have hv := (congrArg
    (fun a : (d.extension.functor.obj (B.X n)).val.obj U ↦
      homValue.{u, v, r} J S (EC.obj P) V n p q hpq U
        ((α.f n).val.app U a)
        (extensionGenerator.{u, v, r} J φ d.extension.functor h (P.X p) U 1 x))
    (hν B n U s f)).trans hscalar
  have ht := (hθ P V n p q hpq U
    ((α.f n).val.app U (((ν.hom.app B).f n).val.app U z)) x).trans hv
  have hleft := (homValue_map_right.{u, v, r} J R P η n p q hpq U
    (((d.theta P V).hom.f n).val.app U
      ((α.f n).val.app U (((ν.hom.app B).f n).val.app U z))) x).trans
    (congrArg (fun a ↦ (η.f q).val.app U a) ht)
  have hcval := ha (underlyingCoefficient.{u, v, r} J φ) n p q hpq U s f x
  have hright := (homValue_map_right.{u, v, r} J R P (IR.map γ) n p q hpq U
    ((c.f n).val.app U z) x).trans
    (congrArg (fun a ↦ ((IR.map γ).f q).val.app U a) hcval)
  have hnat := congrArg
    (fun k : (tensor.{u, v, r} J R).obj (underlyingCoefficient.{u, v, r} J φ, A) ⟶
      IR.obj (Uφ.obj V) ↦ (k.f q).val.app U y)
    ((resolutionUnit.{u, v, r} J R).naturality γ)
  have hgen := congrArg (fun a ↦ (η.f q).val.app U ((τ.f q).val.app U a))
    (hν A q U s w)
  exact hleft.trans ((hright.trans (hnat.symm.trans hgen)).symm)

end RestrictionProof

open HomologicalComplex MonoidalCategory

section QuasiIsoProof
attribute [local irreducible] comparison scalarComparison roofDenominator

/-- Filtered finite-free scalar extension preserves derived internal Hom for every
bounded-below second input. The two assertions are precisely the numerator and
invertible denominator of the canonical comparison roof over S.
Source: Bhatt--Scholze 6.8.12, 6.8.14 and 6.8.15, conditional argument in the node
(blueprint: lem-sfb-dc-hom-filtered-colimit).
Proof:
1--9. Apply filteredColimit_comparison to the underlying module diagram. Its strict
cocone squares identify the colimit roof with evaluation, independently of finite bases.
10. The ordinary scalar adjunction sends an S-linear cochain f to `x ↦ f(1 tensor x)`.
After restriction, scalarComparison_restriction identifies the normalized comparison
with the R-linear comparison followed by Hom of a quasi-isomorphism. Finite-free
tensor and exact filtered colimits make scalar extension exact. Its right adjoint
restriction preserves K-injectives, so the extra Hom augmentation in that square
is a quasi-isomorphism between K-injective targets. Two-out-of-three and conservative
restriction give the numerator. Exact scalar extension preserves eta_L, and homFixed
preserves quasi-isomorphisms, giving the denominator. Their quotient is the specified
canonical comparison.
11. All representative maps are evaluation-defined and strictly natural. Naturality
in both inputs and compatible coefficient-diagram morphisms follows from these formulas
and uniqueness; localization extends it to derived morphisms. No constructibility of L,
finite Tor amplitude of P, lower bound on I_R(L), or basis compatibility is used. -/
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
          ((resolutionUnit.{u, v, r} J R).app L))) := by
  classical
  have _ := hφ
  let U := SheafOfModules.restrictScalars
    ((sheafCompose J
      (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).map φ)
  let EC := E.mapHomologicalComplex (.up ℤ)
  let UC := U.mapHomologicalComplex (.up ℤ)
  let IR := coefficientHomResolution.{r, u, v} J R
  let IS := coefficientHomResolution.{r, u, v} J (colimit S)
  let :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u, v, r}
      J R).1
  let :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u, v, r}
      J (colimit S)).1
  obtain ⟨hUl, hUc, hadj⟩ :=
    SheafOfModules.sheafRingCoefficientOrdinaryAdjunction.{max u v r, u, v} φ
  let : PreservesFiniteLimits U := hUl
  let : PreservesFiniteColimits U := hUc
  obtain ⟨adj, _⟩ := hadj E h hmap
  let : U.ReflectsIsomorphisms := ⟨fun {M N} f hf ↦ by
    have : IsIso ((SheafOfModules.toSheaf _).map f) :=
      inferInstanceAs (IsIso ((SheafOfModules.toSheaf _).map (U.map f)))
    exact isIso_of_reflects_iso f (SheafOfModules.toSheaf _)⟩
  obtain ⟨ν, hν, θ, hθ, hsquare⟩ :=
    scalarComparison_restriction.{u, v, r} J φ E h hmap
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let M := Modules.{u, v, r} J R
  have (X : M) : PreservesColimitsOfSize.{max u v r, max u v r} (tensorLeft X) :=
    SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R X
  let := SheafOfModules.symmetricCategory R
  have (X : M) : PreservesColimitsOfSize.{max u v r, max u v r} (tensorRight X) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)
  let : MonoidalPreadditive M := tensorPreadditive.{u, v, r} J R
  have hstage (i : I) : PreservesFiniteLimits (tensorLeft (T.modules.obj i)) := by
    obtain ⟨d, ⟨α⟩⟩ := hfree i
    exact (tensorFinitePowerExact.{u, v, r} J R (T.modules.obj i) d α).1
  have ht : PreservesFiniteLimits (tensorLeft (colimit T.modules)) :=
    tensorLeft_colimit_exact T.modules hstage
  have hcoef : PreservesFiniteLimits
      (tensorLeft (underlyingCoefficient.{u, v, r} J φ)) :=
    preservesFiniteLimits_of_natIso ((curriedTensor _).mapIso T.colimitIso)
  let t := tensorLeft (underlyingCoefficient.{u, v, r} J φ)
  let σ := single (Modules.{u, v, r} J R) (.up ℤ) 0
  let ev := eval (Modules.{u, v, r} J R) (.up ℤ) 0
  let ε := singleCompEvalIsoSelf (Modules.{u, v, r} J R) (.up ℤ) 0
  let e := tensorTermwiseIso.{u, v, r} J R (underlyingCoefficient.{u, v, r} J φ)
  let νt : t.mapHomologicalComplex (.up ℤ) ≅ EC ⋙ UC := e.symm ≪≫ ν
  let εS := singleCompEvalIsoSelf (Modules.{u, v, r} J (colimit S)) (.up ℤ) 0
  let ν₀ : t ≅ E ⋙ U :=
    (Functor.isoWhiskerRight ε t).symm ≪≫
      Functor.isoWhiskerLeft σ (Functor.isoWhiskerRight νt ev) ≪≫
        Functor.isoWhiskerRight (singleMapHomologicalComplex E (.up ℤ) 0) (UC ⋙ ev) ≪≫
          Functor.isoWhiskerLeft E (Functor.isoWhiskerRight εS U)
  let : PreservesFiniteLimits (E ⋙ U) := preservesFiniteLimits_of_natIso ν₀
  let : PreservesFiniteLimits E := preservesFiniteLimits_of_reflects_of_preserves E U
  let : PreservesColimitsOfSize.{0, 0} E := adj.leftAdjoint_preservesColimits
  let : PreservesFiniteColimits E := inferInstance
  let : U.PreservesKInjectiveComplexes := adj.preservesKInjectiveComplexes
  have hηR (X : CochainComplex (Modules.{u, v, r} J R) ℤ) :
      QuasiIso ((resolutionUnit.{u, v, r} J R).app X) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max u v r} _ X).2
  have hηS (X : CochainComplex (Modules.{u, v, r} J (colimit S)) ℤ) :
      QuasiIso ((resolutionUnit.{u, v, r} J (colimit S)).app X) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max u v r} _ X).2
  have hcolim := (filteredColimit_comparison.{u, v, r} J R T.modules hfree
    P L hP hcont b hL).1
  have hcompare : QuasiIso ((comparison.{u, v, r} J R P L).app
      (underlyingCoefficient.{u, v, r} J φ)) := by
    have hnat := (comparison.{u, v, r} J R P L).naturality T.colimitIso.hom
    have hcomp : QuasiIso
        ((tensorFixed.{u, v, r} J R ((homFixed.{u, v, r} J R P).obj L)).map
          T.colimitIso.hom ≫
          (comparison.{u, v, r} J R P L).app
            (underlyingCoefficient.{u, v, r} J φ)) := by
      rw [hnat]
      infer_instance
    exact quasiIso_of_comp_left
      ((tensorFixed.{u, v, r} J R ((homFixed.{u, v, r} J R P).obj L)).map
        T.colimitIso.hom) _
  let V := IS.obj (EC.obj (IR.obj L))
  let γ := ν.hom.app (IR.obj L) ≫
    UC.map ((resolutionUnit.{u, v, r} J (colimit S)).app (EC.obj (IR.obj L)))
  have hγ : QuasiIso γ := by
    have := hηS (EC.obj (IR.obj L))
    dsimp only [γ]
    infer_instance
  have hright : QuasiIso
      (ν.inv.app ((homFixed.{u, v, r} J R P).obj L) ≫
        (comparison.{u, v, r} J R P L).app (underlyingCoefficient.{u, v, r} J φ) ≫
        (homFixed.{u, v, r} J R P).map γ) := by
    have := hom_preserves.{u, v, r} J R P γ hγ
    infer_instance
  have hKI : V.IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max u v r} _ _
  have hUVI : CochainComplex.IsKInjective (UC.obj V) :=
    Functor.PreservesKInjectiveComplexes.isKInjective_map (F := U) V
  have hKIR : (IR.obj (UC.obj V)).IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max u v r} _ _
  have haug : QuasiIso
      (((homComplexFunctor.{u, v, max u v r, max u v r} (R := R)).obj (op P)).map
        ((resolutionUnit.{u, v, r} J R).app (UC.obj V))) := by
    have := hηR (UC.obj V)
    let : CochainComplex.IsKInjective (UC.obj V) := hUVI
    let : CochainComplex.IsKInjective (IR.obj (UC.obj V)) := hKIR
    have hh := quasiIso_homComplex_mapOfUniverses.{u, v, r}
      (I' := UC.obj V) (I := IR.obj (UC.obj V))
      ((resolutionUnit.{u, v, r} J R).app (UC.obj V)) (𝟙 P)
    rw [show (𝟙 P).op = 𝟙 (op P) from rfl,
      (homComplexFunctor.{u, v, max u v r, max u v r} (R := R)).map_id,
      NatTrans.id_app, Category.id_comp] at hh
    exact hh
  have hrest : QuasiIso (UC.map (scalarComparison.{u, v, r} J φ E h hmap P L)) := by
    have hcomp : QuasiIso
        (UC.map (scalarComparison.{u, v, r} J φ E h hmap P L) ≫ (θ P V).hom ≫
          ((homComplexFunctor (R := R)).obj (op P)).map
            ((resolutionUnit.{u, v, r} J R).app (UC.obj V))) := by
      exact (hsquare P L).symm ▸ hright
    have hcomp' := quasiIso_of_comp_right
      (UC.map (scalarComparison.{u, v, r} J φ E h hmap P L))
      ((θ P V).hom ≫ ((homComplexFunctor (R := R)).obj (op P)).map
        ((resolutionUnit.{u, v, r} J R).app (UC.obj V)))
    exact hcomp'
  refine ⟨(HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (scalarComparison.{u, v, r} J φ E h hmap P L) U).mp hrest, ?_⟩
  have := hηR L
  have he : QuasiIso (EC.map ((resolutionUnit.{u, v, r} J R).app L)) := inferInstance
  exact hom_preserves.{u, v, r} J (colimit S) (EC.obj P) _ he

end QuasiIsoProof

attribute [local irreducible] scalarComparison

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
  obtain ⟨D, _⟩ := @SheafOfModules.StrictScalarHom.exists_scalarHomChainIdentification.{u, v, r}
    C _ J inferInstance inferInstance inferInstance
  let d := D R S φ
  have he := extensionFunctor_eq.{u, v, r} J φ d E h hmap
  subst E
  let IR := coefficientHomResolution.{r, u, v} J R
  let IS := coefficientHomResolution.{r, u, v} J S
  let EC := d.extension.complex
  let η := resolutionUnit.{u, v, r} J S
  have hc (P L : CochainComplex (Modules.{u, v, r} J R) ℤ) :
      scalarComparison.{u, v, r} J φ d.extension.functor h hmap P L =
        d.sigma P (IR.obj L) (IS.obj (EC.obj (IR.obj L)))
          (η.app (EC.obj (IR.obj L))) := by
    apply d.sigma_unique
    apply (scalarNormalized_iff.{u, v, r} J φ d h P L).mp
    unfold scalarComparison
    have hh := scalarComparison_existsUnique.{u, v, r} J φ d.extension.functor h hmap P L
    exact hh.exists.choose_spec
  rw [hc P L, hc P' L']
  exact d.sigma_natural P P' (IR.obj L) (IR.obj L')
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
coefficient-diagram naturalities. These are precisely steps 1--11 recorded above. -/
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
