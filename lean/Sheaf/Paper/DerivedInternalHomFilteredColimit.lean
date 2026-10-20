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

import WeilConjectures.Algebra.Homology.HomComplexComponents
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
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

/-- Transparent type abbreviation for the recorded module category, not a new category.
Source: Stacks, Modules on Sites (blueprint: lem-sfb-dc-hom-filtered-colimit). -/
abbrev Modules (R : Sheaf J CommRingCat.{max u v r}) :=
  ringedSiteModules.{max u v r} ((sheafCompose J
    (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R)

/-- The degree-zero coefficient tensor bifunctor, using the recorded total tensor.
Source: Stacks 06YN (blueprint: lem-sfb-dc-hom-filtered-colimit). -/
noncomputable def tensor (R : Sheaf J CommRingCat.{max u v r}) :
    Modules.{u, v, r} J R × CochainComplex (Modules.{u, v, r} J R) ℤ ⥤
      CochainComplex (Modules.{u, v, r} J R) ℤ :=
  ((HomologicalComplex.single (Modules.{u, v, r} J R) (ComplexShape.up ℤ) 0).prod (𝟭 _)) ⋙
    coefficientTotalTensor.{r, u, v} J R

/-- Tensor a variable coefficient module with a fixed complex.
Source: Stacks 06YN (blueprint: lem-sfb-dc-hom-filtered-colimit). -/
noncomputable def tensorFixed (R : Sheaf J CommRingCat.{max u v r})
    (B : CochainComplex (Modules.{u, v, r} J R) ℤ) :
    Modules.{u, v, r} J R ⥤ CochainComplex (Modules.{u, v, r} J R) ℤ :=
  Prod.sectL _ B ⋙ tensor.{u, v, r} J R

/-- The actual Hom-complex representative with fixed first input and the recorded
functorial K-injective replacement in its second input.
Source: Stacks 0A95 (blueprint: lem-sfb-dc-hom-filtered-colimit). -/
noncomputable def homFixed (R : Sheaf J CommRingCat.{max u v r})
    (P : CochainComplex (Modules.{u, v, r} J R) ℤ) :
    CochainComplex (Modules.{u, v, r} J R) ℤ ⥤ CochainComplex (Modules.{u, v, r} J R) ℤ :=
  coefficientHomResolution.{r, u, v} J R ⋙
    (homComplexFunctor.{u, v, max u v r, max u v r} (R := R)).obj (op P)

/-- The tensor generator in degree `(0,n)`, using the actual single-complex comparison.
Source: Stacks 06YN, 03EK (blueprint: lem-sfb-dc-hom-filtered-colimit). -/
noncomputable def tensorGenerator (R : Sheaf J CommRingCat.{max u v r})
    (T : Modules.{u, v, r} J R) (B : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (n : ℤ) (U : Cᵒᵖ) (t : T.val.obj U) (b : (B.X n).val.obj U) :
    (((tensor.{u, v, r} J R).obj (T, B)).X n).val.obj U :=
  coefficientTensorGenerator.{r, u, v} J R
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj T) B 0 n n (zero_add n) U
    (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 T).inv).val.app U t) b

/-- Evaluate a Hom-complex component, with no chosen evaluation map.
Source: Stacks 0A8X (blueprint: lem-sfb-dc-hom-filtered-colimit). -/
noncomputable def homValue (R : Sheaf J CommRingCat.{max u v r})
    (P Q : CochainComplex (Modules.{u, v, r} J R) ℤ) (n p q : ℤ) (h : p + n = q)
    (U : Cᵒᵖ) (f : ((homComplex (R := R) P Q).X n).val.obj U)
    (x : (P.X p).val.obj U) : (Q.X q).val.obj U :=
  (((coefficientHomComponent.{r, u, v} J R P Q n p q h).val.app U f).app
    (op (Over.mk (𝟙 U.unop)))).hom x

/-- The actual augmentation of the fixed K-injective replacement.
Source: Stacks 079P (blueprint: lem-sfb-dc-hom-filtered-colimit). -/
noncomputable def resolutionUnit (R : Sheaf J CommRingCat.{max u v r}) :
    𝟭 (CochainComplex (Modules.{u, v, r} J R) ℤ) ⟶ coefficientHomResolution.{r, u, v} J R :=
  letI :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u, v, r}
      J R).1
  CochainComplex.toKInjectiveResolution.{max u v r} _


/-- The evaluation normalization of the strict comparison `a_T` in proof step 6.
Source: the node's ring-sheaf argument, step 6; Stacks 08J9
(blueprint: lem-sfb-dc-hom-filtered-colimit). -/
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
(blueprint: lem-sfb-dc-hom-filtered-colimit).
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
Source: the node's argument, step 6 (blueprint: lem-sfb-dc-hom-filtered-colimit). -/
noncomputable def comparison (R : Sheaf J CommRingCat.{max u v r})
    (P L : CochainComplex (Modules.{u, v, r} J R) ℤ) :=
  (comparison_existsUnique.{u, v, r} J R P L).exists.choose

/-- The other arrow of the strict roof: apply Hom with its functorial replacement to
coefficient tensor of the actual augmentation of L.
Source: the node's argument, step 6 (blueprint: lem-sfb-dc-hom-filtered-colimit). -/
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
(blueprint: lem-sfb-dc-hom-filtered-colimit). -/
def Continuous (R : Sheaf J CommRingCat.{max u v r})
    {I : Type (max u v r)} [SmallCategory I] [IsFiltered I]
    [HasColimitsOfShape I (Modules.{u, v, r} J R)]
    (P : CochainComplex (Modules.{u, v, r} J R) ℤ) : Prop :=
  ∀ (M : I ⥤ CochainComplex (Modules.{u, v, r} J R) ℤ) (b : ℤ),
    (∀ (i : I) (n : ℤ), n < b → IsZero ((M.obj i).X n)) →
      QuasiIso (colimit.post M (homFixed.{u, v, r} J R P))

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
  sorry


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

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem extensionPresheafUnit_locallySurjective
    {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings (J := J) φ M)
    (M : Modules.{u, v, r} J R) :
    Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map
      (extensionPresheafUnit.{u, v, r} J φ E h M)) := by
  let A := SheafOfModules.changeOfRingsPresheaf.{v, u, max u v r} (J := J) φ M
  let F := SheafOfModules.forget.{max u v r}
    ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj S) ⋙
      PresheafOfModules.toPresheaf _
  let c := F.map (eqToHom (h M).symm)
  have : IsIso c := by dsimp only [c]; infer_instance
  have he : (PresheafOfModules.toPresheaf _).map
      (extensionPresheafUnit.{u, v, r} J φ E h M) = toSheafify J A.presheaf ≫ c := by
    unfold extensionPresheafUnit
    rfl
  rw [he]
  let : Presheaf.IsLocallySurjective J (toSheafify J A.presheaf) :=
    (J.W_toSheafify A.presheaf).isLocallySurjective
  let : Presheaf.IsLocallySurjective J c := Presheaf.isLocallySurjective_of_iso J c
  exact Presheaf.isLocallySurjective_comp J _ c

private theorem extensionUnit_exists {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings (J := J) φ M)
    (hmap : ∀ {M N : Modules.{u, v, r} J R} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom (J := J) φ M f ≫ eqToHom (h N).symm)
    [E.Additive] :
    ∃ η : 𝟭 (Modules.{u, v, r} J R) ⟶ E ⋙ SheafOfModules.restrictScalars.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).map φ),
      ∀ (M : Modules.{u, v, r} J R) (U : Cᵒᵖ) (x : M.val.obj U),
        (η.app M).val.app U x = extensionGenerator.{u, v, r} J φ E h M U 1 x := by
  obtain ⟨_, _, hh⟩ :=
    SheafOfModules.sheafRingCoefficientOrdinaryAdjunction.{max u v r, u, v} (J := J) φ
  obtain ⟨a, ha⟩ := hh E h hmap
  refine ⟨a.unit, ?_⟩
  intro M U x
  have hx := ha M (E.obj M) (eqToHom (h M).symm) U x
  simpa only [eqToHom_trans, eqToHom_refl, a.homEquiv_id, extensionGenerator] using hx

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem extensionGenerator_map {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings (J := J) φ M)
    (hmap : ∀ {M N : Modules.{u, v, r} J R} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom (J := J) φ M f ≫ eqToHom (h N).symm)
    [E.Additive] {M N : Modules.{u, v, r} J R} (f : M ⟶ N)
    (U : Cᵒᵖ) (x : M.val.obj U) :
    (E.map f).val.app U (extensionGenerator.{u, v, r} J φ E h M U 1 x) =
      extensionGenerator.{u, v, r} J φ E h N U 1 (f.val.app U x) := by
  obtain ⟨η, hη⟩ := extensionUnit_exists.{u, v, r} J φ E h hmap
  have hx := congrArg
    (fun k : M ⟶ _ ↦ k.val.app U x) (η.naturality f)
  change (η.app N).val.app U (f.val.app U x) =
    (E.map f).val.app U ((η.app M).val.app U x) at hx
  rw [hη M U x, hη N U (f.val.app U x)] at hx
  exact hx.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem extensionGenerator_restrict {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings (J := J) φ M)
    (hmap : ∀ {M N : Modules.{u, v, r} J R} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom (J := J) φ M f ≫ eqToHom (h N).symm)
    [E.Additive] (M : Modules.{u, v, r} J R) {U V : Cᵒᵖ} (i : U ⟶ V)
    (x : M.val.obj U) :
    (E.obj M).val.map i (extensionGenerator.{u, v, r} J φ E h M U 1 x) =
      extensionGenerator.{u, v, r} J φ E h M V 1 (M.val.map i x) := by
  obtain ⟨η, hη⟩ := extensionUnit_exists.{u, v, r} J φ E h hmap
  have hx := PresheafOfModules.naturality_apply (η.app M).val i x
  change (η.app M).val.app V (M.val.map i x) =
    (E.obj M).val.map i ((η.app M).val.app U x) at hx
  rw [hη M V (M.val.map i x), hη M U x] at hx
  exact hx.symm

omit [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restricted_hom_ext (R : Sheaf J CommRingCat.{max u v r})
    (A : PresheafOfModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R).obj)
    (M N : Modules.{u, v, r} J R)
    (η : A ⟶ (PresheafOfModules.restrictScalars (𝟙
      ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R).obj)).obj
        M.val)
    [Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map η)]
    (U : C) (a b : (PresheafOfModules.restrictOver R.obj U).obj M.val ⟶
      (PresheafOfModules.restrictOver R.obj U).obj N.val)
    (hab : ∀ (W : (Over U)ᵒᵖ) (x : A.obj (op W.unop.left)),
      a.app W (η.app (op W.unop.left) x) = b.app W (η.app (op W.unop.left) x)) :
    a = b := by
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply N.isSheaf.isSeparated _ _
    (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map η) z)
  rintro V f ⟨y, hy⟩
  let W' : (Over U)ᵒᵖ := op (Over.mk (f ≫ W.unop.hom))
  let k : W ⟶ W' := (Over.homMk f : W'.unop ⟶ W.unop).op
  have ha := PresheafOfModules.naturality_apply a k z
  have hb := PresheafOfModules.naturality_apply b k z
  change a.app W' (M.val.map f.op z) = N.val.map f.op (a.app W z) at ha
  change b.app W' (M.val.map f.op z) = N.val.map f.op (b.app W z) at hb
  change η.app (op V) y = M.val.map f.op z at hy
  change N.val.map f.op (a.app W z) = N.val.map f.op (b.app W z)
  exact ha.symm.trans ((congrArg (fun t : M.val.obj (op V) ↦ a.app W' t) hy).symm.trans
    ((hab W' y).trans ((congrArg (fun t : M.val.obj (op V) ↦ b.app W' t) hy).trans hb)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem extension_local_ext {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings (J := J) φ M)
    (M : Modules.{u, v, r} J R) (N : Modules.{u, v, r} J S) (U : C)
    (a b : (PresheafOfModules.restrictOver S.obj U).obj (E.obj M).val ⟶
      (PresheafOfModules.restrictOver S.obj U).obj N.val)
    (hab : ∀ (W : (Over U)ᵒᵖ) (x : M.val.obj (op W.unop.left)),
      a.app W (extensionGenerator.{u, v, r} J φ E h M (op W.unop.left) 1 x) =
        b.app W (extensionGenerator.{u, v, r} J φ E h M (op W.unop.left) 1 x)) : a = b := by
  have := extensionPresheafUnit_locallySurjective.{u, v, r} J φ E h M
  refine restricted_hom_ext.{u, v, r} J S
    (A := SheafOfModules.changeOfRingsPresheaf.{v, u, max u v r} (J := J) φ M)
    (M := E.obj M) (N := N) (η := extensionPresheafUnit.{u, v, r} J φ E h M)
    (U := U) (a := a) (b := b) ?_
  intro W y
  have hh : (extensionPresheafUnit.{u, v, r} J φ E h M).app (op W.unop.left) ≫
      a.app W =
    (extensionPresheafUnit.{u, v, r} J φ E h M).app (op W.unop.left) ≫ b.app W := by
    apply ModuleCat.ExtendScalars.hom_ext (f := (φ.hom.app (op W.unop.left)).hom)
    intro x
    simp only [ModuleCat.comp_apply]
    erw [extensionPresheafUnit_apply.{u, v, r} J φ E h M (op W.unop.left) 1 x]
    exact hab W x
  exact congrArg (fun k : (SheafOfModules.changeOfRingsPresheaf (J := J) φ M).obj
      (op W.unop.left) ⟶ ((PresheafOfModules.restrictOver S.obj U).obj N.val).obj W ↦
    k y) hh

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem extension_hom_ext {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings (J := J) φ M)
    (M : Modules.{u, v, r} J R) (N : Modules.{u, v, r} J S)
    (a b : E.obj M ⟶ N)
    (hab : ∀ (U : Cᵒᵖ) (x : M.val.obj U),
      a.val.app U (extensionGenerator.{u, v, r} J φ E h M U 1 x) =
        b.val.app U (extensionGenerator.{u, v, r} J φ E h M U 1 x)) : a = b := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  have hh := extension_local_ext.{u, v, r} J φ E h M N U.unop
    ((PresheafOfModules.restrictOver S.obj U.unop).map a.val)
    ((PresheafOfModules.restrictOver S.obj U.unop).map b.val)
    (fun W x ↦ hab (op W.unop.left) x)
  exact congrArg
    (fun k : (PresheafOfModules.restrictOver S.obj U.unop).obj (E.obj M).val ⟶
        (PresheafOfModules.restrictOver S.obj U.unop).obj N.val ↦
      k.app (op (Over.mk (𝟙 U.unop)))) hh

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem extension_to_homObj_ext {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings (J := J) φ M)
    (hmap : ∀ {M N : Modules.{u, v, r} J R} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom (J := J) φ M f ≫ eqToHom (h N).symm)
    [E.Additive] (M N : Modules.{u, v, r} J R) (V : Modules.{u, v, r} J S)
    (a b : E.obj M ⟶ SheafOfModules.homObj (J := J) (R := S) (E.obj N) V)
    (hab : ∀ (U : Cᵒᵖ) (z : M.val.obj U) (x : N.val.obj U),
      ((a.val.app U (extensionGenerator.{u, v, r} J φ E h M U 1 z)).app
        (op (Over.mk (𝟙 U.unop)))).hom
          (extensionGenerator.{u, v, r} J φ E h N U 1 x) =
      ((b.val.app U (extensionGenerator.{u, v, r} J φ E h M U 1 z)).app
        (op (Over.mk (𝟙 U.unop)))).hom
          (extensionGenerator.{u, v, r} J φ E h N U 1 x)) : a = b := by
  apply extension_hom_ext.{u, v, r} J φ E h M _ a b
  intro U z
  apply extension_local_ext.{u, v, r} J φ E h N V U.unop
  intro W x
  have ha := PresheafOfModules.naturality_apply a.val
    W.unop.hom.op (extensionGenerator.{u, v, r} J φ E h M U 1 z)
  have hb := PresheafOfModules.naturality_apply b.val
    W.unop.hom.op (extensionGenerator.{u, v, r} J φ E h M U 1 z)
  have hh := hab (op W.unop.left)
    (M.val.map W.unop.hom.op z) x
  rw [← extensionGenerator_restrict.{u, v, r} J φ E h hmap M W.unop.hom.op z] at hh
  change ((a.val.app (op W.unop.left)
        ((E.obj M).val.map W.unop.hom.op
          (extensionGenerator.{u, v, r} J φ E h M U 1 z))).app
        (op (Over.mk (𝟙 W.unop.left)))).hom
      (extensionGenerator.{u, v, r} J φ E h N (op W.unop.left) 1 x) =
    ((b.val.app (op W.unop.left)
        ((E.obj M).val.map W.unop.hom.op
          (extensionGenerator.{u, v, r} J φ E h M U 1 z))).app
        (op (Over.mk (𝟙 W.unop.left)))).hom
      (extensionGenerator.{u, v, r} J φ E h N (op W.unop.left) 1 x) at hh
  rw [ha, hb] at hh
  change ((a.val.app U
        (extensionGenerator.{u, v, r} J φ E h M U 1 z)).app
        (op (Over.mk (𝟙 W.unop.left ≫ W.unop.hom)))).hom
      (extensionGenerator.{u, v, r} J φ E h N (op W.unop.left) 1 x) =
    ((b.val.app U
        (extensionGenerator.{u, v, r} J φ E h M U 1 z)).app
        (op (Over.mk (𝟙 W.unop.left ≫ W.unop.hom)))).hom
      (extensionGenerator.{u, v, r} J φ E h N (op W.unop.left) 1 x) at hh
  have hca := PresheafOfModules.restrictOver_hom_app_congr
    (R := S.obj) (M := (E.obj N).val) (N := V.val)
    (a.val.app U (extensionGenerator.{u, v, r} J φ E h M U 1 z))
    (Category.id_comp W.unop.hom)
    (extensionGenerator.{u, v, r} J φ E h N (op W.unop.left) 1 x)
  have hcb := PresheafOfModules.restrictOver_hom_app_congr
    (R := S.obj) (M := (E.obj N).val) (N := V.val)
    (b.val.app U (extensionGenerator.{u, v, r} J φ E h M U 1 z))
    (Category.id_comp W.unop.hom)
    (extensionGenerator.{u, v, r} J φ E h N (op W.unop.left) 1 x)
  exact hca.symm.trans (hh.trans hcb)

omit [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}] in
set_option backward.isDefEq.respectTransparency true in
private theorem coefficientHomComponent_eq (R : Sheaf J CommRingCat.{max u v r})
    (P Q : CochainComplex (Modules.{u, v, r} J R) ℤ) (n p q : ℤ) (hpq : p + n = q) :
    coefficientHomComponent.{r, u, v} J R P Q n p q hpq =
      homComplexπ.{u, v, max u v r, max u v r} (J := J) (R := R) P Q n p q hpq := by
  rfl

attribute [local irreducible] homComplexFunctor

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalar_hom_ext {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings (J := J) φ M)
    (hmap : ∀ {M N : Modules.{u, v, r} J R} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom (J := J) φ M f ≫ eqToHom (h N).symm)
    [E.Additive] (M : Modules.{u, v, r} J R)
    (P : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (Q : CochainComplex (Modules.{u, v, r} J S) ℤ) (n : ℤ)
    (a b : E.obj M ⟶
      (homComplex (J := J) (R := S) ((E.mapHomologicalComplex (.up ℤ)).obj P) Q).X n)
    (hab : ∀ (p q : ℤ) (hpq : p + n = q) (U : Cᵒᵖ)
      (z : M.val.obj U) (x : (P.X p).val.obj U),
      homValue.{u, v, r} J S
          ((E.mapHomologicalComplex (.up ℤ)).obj P) Q n p q hpq U
          (a.val.app U (extensionGenerator.{u, v, r} J φ E h M U 1 z))
          (extensionGenerator.{u, v, r} J φ E h (P.X p) U 1 x) =
        homValue.{u, v, r} J S
          ((E.mapHomologicalComplex (.up ℤ)).obj P) Q n p q hpq U
          (b.val.app U (extensionGenerator.{u, v, r} J φ E h M U 1 z))
          (extensionGenerator.{u, v, r} J φ E h (P.X p) U 1 x)) : a = b := by
  apply homComplex_hom_ext.{u, v, max u v r, max u v r}
    (J := J) (R := S) (L := (E.mapHomologicalComplex (.up ℤ)).obj P) (M := Q) (n := n)
  intro p q hpq
  apply extension_to_homObj_ext.{u, v, r} J φ E h hmap M (P.X p) (Q.X q)
  intro U z x
  have hh := hab p q hpq U z x
  unfold homValue coefficientHomComponent at hh
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app]
  erw [ModuleCat.comp_apply, ModuleCat.comp_apply]
  exact hh

omit [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem homObjMap_evaluate (R : Sheaf J CommRingCat.{max u v r})
    {M M' N N' : Modules.{u, v, r} J R} (f : M' ⟶ M) (g : N ⟶ N')
    (U : Cᵒᵖ) (z : (SheafOfModules.homObj (J := J) (R := R) M N).val.obj U)
    (x : M'.val.obj U) :
    ((((SheafOfModules.homObjMap (J := J) (R := R) f g).val.app U z).app
      (op (Over.mk (𝟙 U.unop)))).hom x) =
      g.val.app U ((z.app (op (Over.mk (𝟙 U.unop)))).hom (f.val.app U x)) := by
  rfl

omit [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}] in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem homValue_map (R : Sheaf J CommRingCat.{max u v r})
    {P P' Q Q' : CochainComplex (Modules.{u, v, r} J R) ℤ}
    (f : P' ⟶ P) (g : Q ⟶ Q') (n p q : ℤ) (hpq : p + n = q)
    (U : Cᵒᵖ) (z : ((homComplex (J := J) (R := R) P Q).X n).val.obj U)
    (x : (P'.X p).val.obj U) :
    homValue.{u, v, r} J R P' Q' n p q hpq U
        ((((Functor.uncurry.obj
          (homComplexFunctor.{u, v, max u v r, max u v r} (J := J) (R := R))).map
            (X := (op P, Q)) (Y := (op P', Q')) (f.op, g)).f n).val.app U z) x =
      (g.f q).val.app U
        (homValue.{u, v, r} J R P Q n p q hpq U z ((f.f p).val.app U x)) := by
  have he :
      (((Functor.uncurry.obj
        (homComplexFunctor.{u, v, max u v r, max u v r} (J := J) (R := R))).map
          (X := (op P, Q)) (Y := (op P', Q')) (f.op, g)).f n) ≫
          coefficientHomComponent.{r, u, v} J R P' Q' n p q hpq =
        coefficientHomComponent.{r, u, v} J R P Q n p q hpq ≫
          SheafOfModules.homObjMap (J := J) (R := R) (f.f p) (g.f q) := by
    simpa only [coefficientHomComponent_eq.{u, v, r} J R, Functor.uncurry] using!
      (homComplexFunctor_map_f_π.{u, v, max u v r, max u v r}
        (J := J) (R := R) f g n p q hpq)
  have hh := congrArg
    (fun k : (homComplex (J := J) (R := R) P Q).X n ⟶
      SheafOfModules.homObj (J := J) (R := R) (P'.X p) (Q'.X q) ↦
      ((k.val.app U z).app (op (Over.mk (𝟙 U.unop)))).hom x) he
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app] at hh
  erw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hh
  unfold homValue
  exact hh.trans (homObjMap_evaluate.{u, v, r} J R
    (M := P.X p) (M' := P'.X p) (N := Q.X q) (N' := Q'.X q)
    (f.f p) (g.f q) U
    ((coefficientHomComponent.{r, u, v} J R P Q n p q hpq).val.app U z) x)

private def ScalarEvaluation {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings (J := J) φ M)
    [E.Additive] (P Q : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (V : CochainComplex (Modules.{u, v, r} J S) ℤ)
    (τ : (E.mapHomologicalComplex (.up ℤ)).obj Q ⟶ V)
    (α : (E.mapHomologicalComplex (.up ℤ)).obj
        (homComplex (J := J) (R := R) P Q) ⟶
      homComplex (J := J) (R := S) ((E.mapHomologicalComplex (.up ℤ)).obj P) V) : Prop :=
  ∀ (n p q : ℤ) (hpq : p + n = q) (U : Cᵒᵖ)
    (z : ((homComplex (J := J) (R := R) P Q).X n).val.obj U)
    (x : (P.X p).val.obj U),
    homValue.{u, v, r} J S ((E.mapHomologicalComplex (.up ℤ)).obj P) V n p q hpq U
        ((α.f n).val.app U (extensionGenerator.{u, v, r} J φ E h
          ((homComplex (J := J) (R := R) P Q).X n) U 1 z))
        (extensionGenerator.{u, v, r} J φ E h (P.X p) U 1 x) =
      (τ.f q).val.app U (extensionGenerator.{u, v, r} J φ E h (Q.X q) U 1
        (homValue.{u, v, r} J R P Q n p q hpq U z x))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalar_map_naturality {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings (J := J) φ M)
    (hmap : ∀ {M N : Modules.{u, v, r} J R} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom (J := J) φ M f ≫ eqToHom (h N).symm)
    [E.Additive] {P P' Q Q' : CochainComplex (Modules.{u, v, r} J R) ℤ}
    {V V' : CochainComplex (Modules.{u, v, r} J S) ℤ}
    (f : P' ⟶ P) (g : Q ⟶ Q') (k : V ⟶ V')
    (τ : (E.mapHomologicalComplex (.up ℤ)).obj Q ⟶ V)
    (τ' : (E.mapHomologicalComplex (.up ℤ)).obj Q' ⟶ V')
    (hsq : (E.mapHomologicalComplex (.up ℤ)).map g ≫ τ' = τ ≫ k)
    (α : (E.mapHomologicalComplex (.up ℤ)).obj
        (homComplex (J := J) (R := R) P Q) ⟶
      homComplex (J := J) (R := S) ((E.mapHomologicalComplex (.up ℤ)).obj P) V)
    (α' : (E.mapHomologicalComplex (.up ℤ)).obj
        (homComplex (J := J) (R := R) P' Q') ⟶
      homComplex (J := J) (R := S) ((E.mapHomologicalComplex (.up ℤ)).obj P') V')
    (hn : ScalarEvaluation.{u, v, r} J φ E h P Q V τ α)
    (hn' : ScalarEvaluation.{u, v, r} J φ E h P' Q' V' τ' α') :
    (E.mapHomologicalComplex (.up ℤ)).map
        ((Functor.uncurry.obj
          (homComplexFunctor.{u, v, max u v r, max u v r} (J := J) (R := R))).map
            (X := (op P, Q)) (Y := (op P', Q')) (f.op, g)) ≫ α' =
      α ≫ (Functor.uncurry.obj
        (homComplexFunctor.{u, v, max u v r, max u v r} (J := J) (R := S))).map
          (X := (op ((E.mapHomologicalComplex (.up ℤ)).obj P), V))
          (Y := (op ((E.mapHomologicalComplex (.up ℤ)).obj P'), V'))
          (((E.mapHomologicalComplex (.up ℤ)).map f).op, k) := by
  let EC := E.mapHomologicalComplex (.up ℤ)
  let kR := (Functor.uncurry.obj
    (homComplexFunctor.{u, v, max u v r, max u v r} (J := J) (R := R))).map
      (X := (op P, Q)) (Y := (op P', Q')) (f.op, g)
  let kS := (Functor.uncurry.obj
    (homComplexFunctor.{u, v, max u v r, max u v r} (J := J) (R := S))).map
      (X := (op (EC.obj P), V)) (Y := (op (EC.obj P'), V')) ((EC.map f).op, k)
  change EC.map kR ≫ α' = α ≫ kS
  apply HomologicalComplex.hom_ext
  intro n
  change E.map (kR.f n) ≫ α'.f n = α.f n ≫ kS.f n
  apply scalar_hom_ext.{u, v, r} J φ E h hmap
    ((homComplex (J := J) (R := R) P Q).X n) P' V' n
  intro p q hpq U z x
  change homValue.{u, v, r} J S (EC.obj P') V' n p q hpq U
      ((α'.f n).val.app U ((E.map (kR.f n)).val.app U
        (extensionGenerator.{u, v, r} J φ E h ((homComplex (J := J) (R := R) P Q).X n) U 1 z)))
      (extensionGenerator.{u, v, r} J φ E h (P'.X p) U 1 x) =
    homValue.{u, v, r} J S (EC.obj P') V' n p q hpq U
      ((kS.f n).val.app U ((α.f n).val.app U
        (extensionGenerator.{u, v, r} J φ E h ((homComplex (J := J) (R := R) P Q).X n) U 1 z)))
      (extensionGenerator.{u, v, r} J φ E h (P'.X p) U 1 x)
  let v := homValue.{u, v, r} J R P Q n p q hpq U z ((f.f p).val.app U x)
  let u := (α.f n).val.app U (extensionGenerator.{u, v, r} J φ E h
    ((homComplex (J := J) (R := R) P Q).X n) U 1 z)
  have hgR := extensionGenerator_map.{u, v, r} J φ E h hmap
    (M := (homComplex (J := J) (R := R) P Q).X n)
    (N := (homComplex (J := J) (R := R) P' Q').X n) (kR.f n) U z
  have hl₁ := congrArg
    (fun y : (E.obj ((homComplex (J := J) (R := R) P' Q').X n)).val.obj U ↦
      homValue.{u, v, r} J S (EC.obj P') V' n p q hpq U
        ((α'.f n).val.app U y) (extensionGenerator.{u, v, r} J φ E h (P'.X p) U 1 x)) hgR
  have hl₂ : homValue.{u, v, r} J S (EC.obj P') V' n p q hpq U
      ((α'.f n).val.app U (extensionGenerator.{u, v, r} J φ E h
        ((homComplex (J := J) (R := R) P' Q').X n) U 1
        ((kR.f n).val.app U z)))
      (extensionGenerator.{u, v, r} J φ E h (P'.X p) U 1 x) =
    (τ'.f q).val.app U
      (extensionGenerator.{u, v, r} J φ E h (Q'.X q) U 1
        (homValue.{u, v, r} J R P' Q' n p q hpq U ((kR.f n).val.app U z) x)) := by
    exact hn' n p q hpq U ((kR.f n).val.app U z) x
  have hmR := homValue_map.{u, v, r} J R
    (P := P) (P' := P') (Q := Q) (Q' := Q') f g n p q hpq U z x
  have hl₃ := congrArg
    (fun y : (Q'.X q).val.obj U ↦ (τ'.f q).val.app U
      (extensionGenerator.{u, v, r} J φ E h (Q'.X q) U 1 y)) hmR
  have heRaw := congrArg
    (fun k : EC.obj Q ⟶ V' ↦
      (k.f q).val.app U (extensionGenerator.{u, v, r} J φ E h (Q.X q) U 1 v))
    hsq
  change (τ'.f q).val.app U
      ((E.map (g.f q)).val.app U
        (extensionGenerator.{u, v, r} J φ E h (Q.X q) U 1 v)) =
    (k.f q).val.app U ((τ.f q).val.app U
      (extensionGenerator.{u, v, r} J φ E h (Q.X q) U 1 v)) at heRaw
  have heGen := congrArg
    (fun y : (E.obj (Q'.X q)).val.obj U ↦ (τ'.f q).val.app U y)
    (extensionGenerator_map.{u, v, r} J φ E h hmap
      (M := Q.X q) (N := Q'.X q) (g.f q) U v)
  have he := heGen.symm.trans heRaw
  have hmS := homValue_map.{u, v, r} J S
    (P := EC.obj P) (P' := EC.obj P') (Q := V) (Q' := V') (EC.map f) k n p q hpq U u
    (extensionGenerator.{u, v, r} J φ E h (P'.X p) U 1 x)
  have hf := congrArg
    (fun y : (E.obj (P.X p)).val.obj U ↦
      homValue.{u, v, r} J S (EC.obj P) V n p q hpq U u y)
    (extensionGenerator_map.{u, v, r} J φ E h hmap
      (M := P'.X p) (N := P.X p) (f.f p) U x)
  have hα : homValue.{u, v, r} J S (EC.obj P) V n p q hpq U u
      (extensionGenerator.{u, v, r} J φ E h (P.X p) U 1 ((f.f p).val.app U x)) =
    (τ.f q).val.app U
      (extensionGenerator.{u, v, r} J φ E h (Q.X q) U 1 v) := by
    exact hn n p q hpq U z ((f.f p).val.app U x)
  have hr := hmS.trans ((congrArg (fun y : (V.X q).val.obj U ↦
    (k.f q).val.app U y) hf).trans (congrArg
      (fun y : (V.X q).val.obj U ↦ (k.f q).val.app U y) hα))
  exact (hl₁.trans (hl₂.trans (hl₃.trans he))).trans hr.symm

attribute [local semireducible] homComplexFunctor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarNormalized_evaluation {R S : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ S) (E : Modules.{u, v, r} J R ⥤ Modules.{u, v, r} J S)
    (h : ∀ M : Modules.{u, v, r} J R, E.obj M = SheafOfModules.changeOfRings (J := J) φ M)
    [E.Additive] (P L : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (α : (E.mapHomologicalComplex (.up ℤ)).obj ((homFixed.{u, v, r} J R P).obj L) ⟶
      (homFixed.{u, v, r} J S ((E.mapHomologicalComplex (.up ℤ)).obj P)).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj
          ((coefficientHomResolution.{r, u, v} J R).obj L)))
    (hn : ScalarNormalized.{u, v, r} J φ E h P L α) :
    ScalarEvaluation.{u, v, r} J φ E h P ((coefficientHomResolution.{r, u, v} J R).obj L)
      ((coefficientHomResolution.{r, u, v} J S).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj
          ((coefficientHomResolution.{r, u, v} J R).obj L)))
      ((resolutionUnit.{u, v, r} J S).app
        ((E.mapHomologicalComplex (.up ℤ)).obj
          ((coefficientHomResolution.{r, u, v} J R).obj L))) α := by
  intro n p q hpq U z x
  simpa only [one_mul] using! hn n p q hpq U 1 1 z x

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
  sorry

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


/-- Filtered finite-free scalar extension preserves derived internal Hom for every
bounded-below second input. The two assertions are precisely the numerator and
invertible denominator of the canonical comparison roof over S.
Source: Bhatt--Scholze 6.8.12, 6.8.14 and 6.8.15, conditional argument in the node
(blueprint: lem-sfb-dc-hom-filtered-colimit).
Proof:
1--9. Apply filteredColimit_comparison to the underlying module diagram. Its strict
cocone squares identify the colimit roof with evaluation, independently of finite bases.
10. The ordinary scalar adjunction sends an S-linear cochain f to `x ↦ f(1 tensor x)`.
After restriction, the normalized scalarComparison has the same evaluation formula as
the R-linear comparison. Functorial K-injective comparison identifies their roofs;
this is the evaluation-normalized derived scalar-adjunction identification of
lem-sfb-dc-hom-scalar-adjunction. Restriction is conservative, so the numerator is a
quasi-isomorphism. Exactness of scalar extension makes E(eta_L) a quasi-isomorphism;
Hom into functorial K-injectives preserves it (lem-pur-rhom-well-defined), giving the
denominator. Their quotient is the canonical comparison, not an unspecified isomorphism.
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
  sorry


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
  sorry

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
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types false in
    let EC := E.mapHomologicalComplex (.up ℤ)
    let IR := coefficientHomResolution.{r, u, v} J R
    let IS := coefficientHomResolution.{r, u, v} J S
    let η := resolutionUnit.{u, v, r} J S
    have hn (A B : CochainComplex (Modules.{u, v, r} J R) ℤ) :
        ScalarEvaluation.{u, v, r} J φ E h A (IR.obj B) (IS.obj (EC.obj (IR.obj B)))
          (η.app (EC.obj (IR.obj B))) (scalarComparison.{u, v, r} J φ E h hmap A B) := by
      apply scalarNormalized_evaluation.{u, v, r} J φ E h A B
      unfold scalarComparison
      exact (scalarComparison_existsUnique.{u, v, r} J φ E h hmap A B).exists.choose_spec
    exact scalar_map_naturality.{u, v, r} J φ E h hmap f (IR.map g)
      (IS.map (EC.map (IR.map g))) (η.app (EC.obj (IR.obj L)))
      (η.app (EC.obj (IR.obj L'))) (η.naturality (EC.map (IR.map g)))
      (scalarComparison.{u, v, r} J φ E h hmap P L)
      (scalarComparison.{u, v, r} J φ E h hmap P' L') (hn P L) (hn P' L')

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
