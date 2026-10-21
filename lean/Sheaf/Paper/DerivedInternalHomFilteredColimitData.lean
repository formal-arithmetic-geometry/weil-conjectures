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

/-! # Strict coefficient tensor and internal-Hom roof

The definitions and unique-normalization assertion are shared by the finite-free stage
calculation and the filtered-colimit theorem. They are the unchanged representative
models of `lem-sfb-dc-hom-filtered-colimit`.
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

/-- Transparent type abbreviation for the recorded module category, not a new category.
Source: Stacks, Modules on Sites (blueprint: def-sfb-internal-hom-strict-models). -/
abbrev Modules (R : Sheaf J CommRingCat.{max u v r}) :=
  ringedSiteModules.{max u v r} ((sheafCompose J
    (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R)

/-- The degree-zero coefficient tensor bifunctor, using the recorded total tensor.
Source: Stacks 06YN (blueprint: def-sfb-internal-hom-strict-models). -/
noncomputable def tensor (R : Sheaf J CommRingCat.{max u v r}) :
    Modules.{u, v, r} J R × CochainComplex (Modules.{u, v, r} J R) ℤ ⥤
      CochainComplex (Modules.{u, v, r} J R) ℤ :=
  ((HomologicalComplex.single (Modules.{u, v, r} J R) (ComplexShape.up ℤ) 0).prod (𝟭 _)) ⋙
    coefficientTotalTensor.{r, u, v} J R

/-- Tensor a variable coefficient module with a fixed complex.
Source: Stacks 06YN (blueprint: def-sfb-internal-hom-strict-models). -/
noncomputable def tensorFixed (R : Sheaf J CommRingCat.{max u v r})
    (B : CochainComplex (Modules.{u, v, r} J R) ℤ) :
    Modules.{u, v, r} J R ⥤ CochainComplex (Modules.{u, v, r} J R) ℤ :=
  Prod.sectL _ B ⋙ tensor.{u, v, r} J R

/-- The actual Hom-complex representative with fixed first input and the recorded
functorial K-injective replacement in its second input.
Source: Stacks 0A95 (blueprint: def-sfb-internal-hom-strict-models). -/
noncomputable def homFixed (R : Sheaf J CommRingCat.{max u v r})
    (P : CochainComplex (Modules.{u, v, r} J R) ℤ) :
    CochainComplex (Modules.{u, v, r} J R) ℤ ⥤ CochainComplex (Modules.{u, v, r} J R) ℤ :=
  coefficientHomResolution.{r, u, v} J R ⋙
    (homComplexFunctor.{u, v, max u v r, max u v r} (R := R)).obj (op P)

/-- The tensor generator in degree `(0,n)`, using the actual single-complex comparison.
Source: Stacks 06YN, 03EK (blueprint: def-sfb-internal-hom-strict-models). -/
noncomputable def tensorGenerator (R : Sheaf J CommRingCat.{max u v r})
    (T : Modules.{u, v, r} J R) (B : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (n : ℤ) (U : Cᵒᵖ) (t : T.val.obj U) (b : (B.X n).val.obj U) :
    (((tensor.{u, v, r} J R).obj (T, B)).X n).val.obj U :=
  coefficientTensorGenerator.{r, u, v} J R
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj T) B 0 n n (zero_add n) U
    (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 T).inv).val.app U t) b

/-- Evaluate a Hom-complex component, with no chosen evaluation map.
Source: Stacks 0A8X (blueprint: def-sfb-internal-hom-strict-models). -/
noncomputable def homValue (R : Sheaf J CommRingCat.{max u v r})
    (P Q : CochainComplex (Modules.{u, v, r} J R) ℤ) (n p q : ℤ) (h : p + n = q)
    (U : Cᵒᵖ) (f : ((homComplex (R := R) P Q).X n).val.obj U)
    (x : (P.X p).val.obj U) : (Q.X q).val.obj U :=
  (((homComplexπ.{u, v, max u v r, max u v r} (J := J) (R := R) P Q n p q h).val.app U f).app
    (op (Over.mk (𝟙 U.unop)))).hom x

/-- The actual augmentation of the fixed K-injective replacement.
Source: Stacks 079P (blueprint: def-sfb-internal-hom-strict-models). -/
noncomputable def resolutionUnit (R : Sheaf J CommRingCat.{max u v r}) :
    𝟭 (CochainComplex (Modules.{u, v, r} J R) ℤ) ⟶ coefficientHomResolution.{r, u, v} J R :=
  letI :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u, v, r}
      J R).1
  CochainComplex.toKInjectiveResolution.{max u v r} _


/-- The evaluation normalization of the strict comparison `a_T` in proof step 6.
Source: the node's ring-sheaf argument, step 6; Stacks 08J9
(blueprint: def-sfb-internal-hom-strict-models). -/
def Normalized (R : Sheaf J CommRingCat.{max u v r})
    (P L : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (a : tensorFixed.{u, v, r} J R ((homFixed.{u, v, r} J R P).obj L) ⟶
      tensorFixed.{u, v, r} J R ((coefficientHomResolution.{r, u, v} J R).obj L) ⋙
        homFixed.{u, v, r} J R P) : Prop :=
  ∀ (T : Modules.{u, v, r} J R) (n p q : ℤ) (h : p + n = q) (U : Cᵒᵖ)
    (t : T.val.obj U) (f : (((homFixed.{u, v, r} J R P).obj L).X n).val.obj U)
    (x : (P.X p).val.obj U),
    homValue.{u, v, r} J R P
        ((coefficientHomResolution.{r, u, v} J R).obj
          ((tensor.{u, v, r} J R).obj
            (T, (coefficientHomResolution.{r, u, v} J R).obj L))) n p q h U
        (((a.app T).f n).val.app U (tensorGenerator.{u, v, r} J R T _ n U t f)) x =
      (((resolutionUnit.{u, v, r} J R).app
          ((tensor.{u, v, r} J R).obj
            (T, (coefficientHomResolution.{r, u, v} J R).obj L))).f q).val.app U
        (tensorGenerator.{u, v, r} J R T _ q U t
          (homValue.{u, v, r} J R P
            ((coefficientHomResolution.{r, u, v} J R).obj L) n p q h U f x))

/-- The strict evaluation comparisons exist uniquely, before any colimit or localization.
Source: the node's argument, step 6; Stacks 08J9
(blueprint: lem-sfb-internal-hom-comparison-exists).
Proof: send `t tensor f` to the cochain `x ↦ t tensor f(x)`, followed by the fixed
K-injective augmentation. Balancedness and restrictions give a sheaf map. The Hom
and total-tensor differentials give a chain map, with no sign since t has degree zero.
The same formula for a module map gives strict naturality. Sheafified pure tensors
and Hom-product projections determine every component, hence uniqueness. -/
theorem comparison_existsUnique (R : Sheaf J CommRingCat.{max u v r})
    (P L : CochainComplex (Modules.{u, v, r} J R) ℤ) :
    ∃! a : tensorFixed.{u, v, r} J R ((homFixed.{u, v, r} J R P).obj L) ⟶
      tensorFixed.{u, v, r} J R ((coefficientHomResolution.{r, u, v} J R).obj L) ⋙
        homFixed.{u, v, r} J R P,
      Normalized.{u, v, r} J R P L a := by
  sorry

/-- The uniquely evaluation-normalized comparison, not a choice of an arbitrary map.
Source: the node's argument, step 6 (blueprint: def-sfb-internal-hom-strict-roof). -/
noncomputable def comparison (R : Sheaf J CommRingCat.{max u v r})
    (P L : CochainComplex (Modules.{u, v, r} J R) ℤ) :=
  (comparison_existsUnique.{u, v, r} J R P L).exists.choose

/-- The other arrow of the strict roof: apply Hom with its functorial replacement to
coefficient tensor of the actual augmentation of L.
Source: the node's argument, step 6 (blueprint: def-sfb-internal-hom-strict-roof). -/
noncomputable def roofDenominator (R : Sheaf J CommRingCat.{max u v r})
    (P L : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (T : Modules.{u, v, r} J R) :
    (homFixed.{u, v, r} J R P).obj ((tensor.{u, v, r} J R).obj (T, L)) ⟶
      (homFixed.{u, v, r} J R P).obj ((tensor.{u, v, r} J R).obj
        (T, (coefficientHomResolution.{r, u, v} J R).obj L)) :=
  (homFixed.{u, v, r} J R P).map
    ((tensor.{u, v, r} J R).map (𝟙 T, (resolutionUnit.{u, v, r} J R).app L))

/-- Exact termwise-colimit continuity, expressed using the canonical cocone map.
Source: Bhatt--Scholze 6.8.12 and the node's continuity hypothesis
(blueprint: def-sfb-internal-hom-strict-roof). -/
def Continuous (R : Sheaf J CommRingCat.{max u v r})
    {I : Type (max u v r)} [SmallCategory I] [IsFiltered I]
    [HasColimitsOfShape I (Modules.{u, v, r} J R)]
    (P : CochainComplex (Modules.{u, v, r} J R) ℤ) : Prop :=
  ∀ (M : I ⥤ CochainComplex (Modules.{u, v, r} J R) ℤ) (b : ℤ),
    (∀ (i : I) (n : ℤ), n < b → IsZero ((M.obj i).X n)) →
      QuasiIso (colimit.post M (homFixed.{u, v, r} J R P))

end WeilConjectures.SfbHomFilteredColimit
