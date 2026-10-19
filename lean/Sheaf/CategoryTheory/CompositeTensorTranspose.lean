/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q83 and Q144
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Double transpose of composite tensor-counit maps

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-cohsm/thm-pur-cohomological-smoothness.proof.md, second paragraph, sentence
on transposing the two tensor transformations; Stacks Tag 0037 for adjunction
transpose conventions (blueprint: lem-pur-composite-tensor-transpose).

The helpers construct the two maps and their proposed common inverse transpose
using the recorded projection-formula structure and Mathlib's composite adjunction.
-/

@[expose] public section

set_option autoImplicit false

universe uX vX uY vY uZ vZ

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Functor
open scoped CategoryTheory.Obj

namespace SecSmoothPurity

/-- The counit transpose determined by a projection formula.
Source: blueprint sec-six-functors-basics/sk-prop-cohsm, second paragraph
(blueprint: lem-pur-composite-tensor-transpose). -/
noncomputable def tensorCounitTranspose
    {C : Type uX} [Category.{vX} C] [MonoidalCategory C]
    {D : Type uY} [Category.{vY} D] [MonoidalCategory D]
    (S : D ⥤ C) (P : C ⥤ D) (G : D ⥤ C)
    [S.Monoidal] (adj : P ⊣ G)
    (pf : S.ProjectionFormula P) (B : D) :
    S.obj B ⊗ G.obj (𝟙_ D) ⟶ G.obj B :=
  pf.theta adj B (𝟙_ D) ≫ G.map (ρ_ B).hom

/-- The composite projection isomorphism.
Source: blueprint sec-six-functors-basics/sk-prop-cohsm
(blueprint: lem-pur-composite-tensor-transpose). -/
noncomputable def compositeProjectionIso
    {C : Type uX} [Category.{vX} C] [MonoidalCategory C]
    {D : Type uY} [Category.{vY} D] [MonoidalCategory D]
    {E : Type uZ} [Category.{vZ} E] [MonoidalCategory E]
    (S₁ : D ⥤ C) (S₂ : E ⥤ D)
    (P₁ : C ⥤ D) (P₂ : D ⥤ E)
    [S₁.Monoidal] [S₂.Monoidal]
    (pf : S₁.ProjectionFormula P₁)
    (pg : S₂.ProjectionFormula P₂)
    (K : E) (M : C) :
    (P₁ ⋙ P₂).obj ((S₂ ⋙ S₁).obj K ⊗ M) ≅
      K ⊗ (P₁ ⋙ P₂).obj M :=
  (P₂.mapIso (pf.iso (S₂.obj K) M)).trans (pg.iso K (P₁.obj M))


/-- The tensor source identified with the composite strong-monoidal source.
Source: blueprint sec-six-functors-basics/sk-prop-cohsm
(blueprint: lem-pur-composite-tensor-transpose). -/
noncomputable def compositeTensorSource
    {C : Type uX} [Category.{vX} C] [MonoidalCategory C]
    {D : Type uY} [Category.{vY} D] [MonoidalCategory D]
    {E : Type uZ} [Category.{vZ} E] [MonoidalCategory E]
    (S₁ : D ⥤ C) (S₂ : E ⥤ D) (G₁ : D ⥤ C) (G₂ : E ⥤ D)
    (K : E) : C :=
  S₁.obj (S₂.obj K ⊗ G₂.obj (𝟙_ E)) ⊗ G₁.obj (𝟙_ D)

/-- The first iterated counit-transpose map.
Source: blueprint sec-six-functors-basics/sk-prop-cohsm
(blueprint: lem-pur-composite-tensor-transpose). -/
noncomputable def compositeTensorFirst
    {C : Type uX} [Category.{vX} C] [MonoidalCategory C]
    {D : Type uY} [Category.{vY} D] [MonoidalCategory D]
    {E : Type uZ} [Category.{vZ} E] [MonoidalCategory E]
    (S₁ : D ⥤ C) (S₂ : E ⥤ D) (P₁ : C ⥤ D) (P₂ : D ⥤ E)
    (G₁ : D ⥤ C) (G₂ : E ⥤ D)
    [S₁.Monoidal] [S₂.Monoidal]
    (adj₁ : P₁ ⊣ G₁) (adj₂ : P₂ ⊣ G₂)
    (pf : S₁.ProjectionFormula P₁) (pg : S₂.ProjectionFormula P₂)
    (K : E) :
    compositeTensorSource S₁ S₂ G₁ G₂ K ⟶ (G₂ ⋙ G₁).obj K :=
  (S₁.map (tensorCounitTranspose S₂ P₂ G₂ adj₂ pg K) ▷
      G₁.obj (𝟙_ D)) ≫
    tensorCounitTranspose S₁ P₁ G₁ adj₁ pf (G₂.obj K)


/-- The composite counit-transpose map using the composite projection formula.
Source: blueprint sec-six-functors-basics/sk-prop-cohsm
(blueprint: lem-pur-composite-tensor-transpose). -/
noncomputable def compositeTensorSecond
    {C : Type uX} [Category.{vX} C] [MonoidalCategory C]
    {D : Type uY} [Category.{vY} D] [MonoidalCategory D]
    {E : Type uZ} [Category.{vZ} E] [MonoidalCategory E]
    (S₁ : D ⥤ C) (S₂ : E ⥤ D) (P₁ : C ⥤ D) (P₂ : D ⥤ E)
    (G₁ : D ⥤ C) (G₂ : E ⥤ D)
    [S₁.Monoidal] [S₂.Monoidal]
    (adj₁ : P₁ ⊣ G₁) (adj₂ : P₂ ⊣ G₂)
    (pf : S₁.ProjectionFormula P₁) (pg : S₂.ProjectionFormula P₂)
    (K : E) :
    compositeTensorSource S₁ S₂ G₁ G₂ K ⟶ ((G₂ ⋙ G₁).obj K) :=
  ((Functor.Monoidal.μIso S₁ (S₂.obj K) (G₂.obj (𝟙_ E))).inv ▷ G₁.obj (𝟙_ D)) ≫
    (α_ ((S₂ ⋙ S₁).obj K) (S₁.obj (G₂.obj (𝟙_ E))) (G₁.obj (𝟙_ D))).hom ≫
    ((S₂ ⋙ S₁).obj K ◁ tensorCounitTranspose S₁ P₁ G₁ adj₁ pf (G₂.obj (𝟙_ E))) ≫
    (adj₁.comp adj₂).homEquiv _ K
      ((compositeProjectionIso S₁ S₂ P₁ P₂ pf pg K ((G₂ ⋙ G₁).obj (𝟙_ E))).hom ≫
        K ◁ (adj₁.comp adj₂).counit.app (𝟙_ E) ≫ (ρ_ K).hom)

/-- The explicit inverse transpose composite of the two projection maps and counits.
Source: blueprint sec-six-functors-basics/sk-prop-cohsm
(blueprint: lem-pur-composite-tensor-transpose). -/
noncomputable def compositeTensorInverseTranspose
    {C : Type uX} [Category.{vX} C] [MonoidalCategory C]
    {D : Type uY} [Category.{vY} D] [MonoidalCategory D]
    {E : Type uZ} [Category.{vZ} E] [MonoidalCategory E]
    (S₁ : D ⥤ C) (S₂ : E ⥤ D) (P₁ : C ⥤ D) (P₂ : D ⥤ E)
    (G₁ : D ⥤ C) (G₂ : E ⥤ D)
    [S₁.Monoidal] [S₂.Monoidal]
    (adj₁ : P₁ ⊣ G₁) (adj₂ : P₂ ⊣ G₂)
    (pf : S₁.ProjectionFormula P₁) (pg : S₂.ProjectionFormula P₂)
    (K : E) :
    (P₁ ⋙ P₂).obj (compositeTensorSource S₁ S₂ G₁ G₂ K) ⟶ K :=
  P₂.map (pf.iso (S₂.obj K ⊗ G₂.obj (𝟙_ E)) (G₁.obj (𝟙_ D))).hom ≫
    P₂.map (((S₂.obj K ⊗ G₂.obj (𝟙_ E)) ◁ adj₁.counit.app (𝟙_ D)) ≫
      (ρ_ (S₂.obj K ⊗ G₂.obj (𝟙_ E))).hom) ≫
    (pg.iso K (G₂.obj (𝟙_ E))).hom ≫
    (K ◁ adj₂.counit.app (𝟙_ E)) ≫
    (ρ_ K).hom

private theorem tensor_counit_assoc
    {D : Type uY} [Category.{vY} D] [MonoidalCategory D]
    (A V W : D) (e : W ⟶ 𝟙_ D) :
    (α_ A V W).hom ≫ A ◁ (V ◁ e ≫ (ρ_ V).hom) =
      (A ⊗ V) ◁ e ≫ (ρ_ (A ⊗ V)).hom := by
  rw [MonoidalCategory.whiskerLeft_comp, ← associator_naturality_right_assoc,
    ← rightUnitor_tensor_hom]

private theorem tensorCounitTranspose_symm
    {C : Type uX} [Category.{vX} C] [MonoidalCategory C]
    {D : Type uY} [Category.{vY} D] [MonoidalCategory D]
    (S : D ⥤ C) (P : C ⥤ D) (G : D ⥤ C)
    [S.Monoidal] (adj : P ⊣ G) (pf : S.ProjectionFormula P) (B : D) :
    (adj.homEquiv _ _).symm (tensorCounitTranspose S P G adj pf B) =
      (pf.iso B (G.obj (𝟙_ D))).hom ≫ B ◁ adj.counit.app (𝟙_ D) ≫ (ρ_ B).hom := by
  rw [tensorCounitTranspose, adj.homEquiv_naturality_right_symm,
    pf.homEquiv_symm_theta, Category.assoc]

/--
The two tensor-counit maps obtained from coherent projection formulas for two
successive adjunctions have the same transpose under the composite adjunction.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-cohsm/thm-pur-cohomological-smoothness.proof.md, second paragraph;
Stacks Tag 0037 (blueprint: lem-pur-composite-tensor-transpose).

Proof:
1. The defining Hom-bijection equation for each tensor-counit transpose gives
   its projection isomorphism followed by the counit at the unit and the right
   unitor. In `tensorCounitTranspose`, this is also `pf.theta` followed by the
   right adjoint applied to that unitor, by Hom-bijection naturality.
2. Inverse-transpose `compositeTensorFirst` successively through the two
   adjunctions. Naturality of the first projection family moves the image of
   the second transpose past that projection; right-unitor naturality then
   makes it adjacent to the second inverse transpose. Substitute its defining
   equation to obtain `compositeTensorInverseTranspose`.
3. Inverse-transpose `compositeTensorSecond`. Expand the composite projection
   and the composite counit, which is the second left functor applied to the
   first counit followed by the second counit. Move the factor involving `q`
   through the projections by right naturality. The associativity equation
   for `pf` absorbs the inverse tensorator and associator in the source.
   Substitute the defining transpose equation for `q`. Projection unit
   coherence and unitor naturality leave precisely the same composite as in
   step 2, with the two counits in their adjunction order.
4. These computations give the two asserted equalities. The inverse Hom
   bijection is injective, so the original maps agree as well. The computation
   uses only the displayed objects and the naturality/coherence equations;
   it remains the same after restricting the data to full domains on which
   these expressions and equations are defined and hold. No invertibility of
   either transpose, of `q`, or of the right-adjoint images of the units is used.
-/
theorem composite_tensor_transpose
    {C : Type uX} [Category.{vX} C] [MonoidalCategory C]
    {D : Type uY} [Category.{vY} D] [MonoidalCategory D]
    {E : Type uZ} [Category.{vZ} E] [MonoidalCategory E]
    (S₁ : D ⥤ C) (S₂ : E ⥤ D) (P₁ : C ⥤ D) (P₂ : D ⥤ E)
    (G₁ : D ⥤ C) (G₂ : E ⥤ D)
    [S₁.Monoidal] [S₂.Monoidal]
    (adj₁ : P₁ ⊣ G₁) (adj₂ : P₂ ⊣ G₂)
    (pf : S₁.ProjectionFormula P₁) (pg : S₂.ProjectionFormula P₂)
    (K : E) :
    ((adj₁.comp adj₂).homEquiv (compositeTensorSource S₁ S₂ G₁ G₂ K) K).symm
        (compositeTensorFirst S₁ S₂ P₁ P₂ G₁ G₂ adj₁ adj₂ pf pg K) =
      compositeTensorInverseTranspose S₁ S₂ P₁ P₂ G₁ G₂ adj₁ adj₂ pf pg K ∧
    ((adj₁.comp adj₂).homEquiv (compositeTensorSource S₁ S₂ G₁ G₂ K) K).symm
        (compositeTensorSecond S₁ S₂ P₁ P₂ G₁ G₂ adj₁ adj₂ pf pg K) =
      compositeTensorInverseTranspose S₁ S₂ P₁ P₂ G₁ G₂ adj₁ adj₂ pf pg K := by
  rw [Adjunction.comp_homEquiv]
  simp only [Equiv.symm_trans_apply]
  dsimp only [compositeTensorFirst, compositeTensorSecond, compositeTensorSource,
    Functor.comp_obj]
  constructor
  · unfold compositeTensorInverseTranspose
    rw [adj₁.homEquiv_naturality_left_symm, tensorCounitTranspose_symm,
      ← Category.assoc, pf.natural_left]
    simp only [Category.assoc]
    rw [← whisker_exchange_assoc]
    dsimp only [Functor.id_obj]
    erw [rightUnitor_naturality]
    erw [← Category.assoc, ← Category.assoc,
      adj₂.homEquiv_naturality_left_symm, tensorCounitTranspose_symm]
    simp only [Functor.map_comp, Category.assoc]
  · unfold compositeTensorInverseTranspose
    rw [Adjunction.comp_homEquiv]
    simp only [Equiv.trans_apply]
    rw [adj₁.homEquiv_naturality_left_symm,
      adj₁.homEquiv_naturality_left_symm,
      adj₁.homEquiv_naturality_left_symm, Equiv.symm_apply_apply,
      adj₂.homEquiv_naturality_left_symm, adj₂.homEquiv_naturality_left_symm,
      adj₂.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
    simp only [compositeProjectionIso, Iso.trans_hom, Functor.mapIso_hom,
      Adjunction.comp_counit_app, Functor.comp_obj, Category.assoc]
    rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, ← pg.natural_right_assoc]
    have hq :
        P₁.map (S₁.obj (S₂.obj K) ◁
            tensorCounitTranspose S₁ P₁ G₁ adj₁ pf (G₂.obj (𝟙_ E))) ≫
          (pf.iso (S₂.obj K) (G₁.obj (G₂.obj (𝟙_ E)))).hom ≫
          S₂.obj K ◁ adj₁.counit.app (G₂.obj (𝟙_ E)) =
        (pf.iso (S₂.obj K) (S₁.obj (G₂.obj (𝟙_ E)) ⊗ G₁.obj (𝟙_ D))).hom ≫
          S₂.obj K ◁ ((pf.iso (G₂.obj (𝟙_ E)) (G₁.obj (𝟙_ D))).hom ≫
            G₂.obj (𝟙_ E) ◁ adj₁.counit.app (𝟙_ D) ≫ (ρ_ (G₂.obj (𝟙_ E))).hom) := by
      rw [pf.natural_right_assoc, ← MonoidalCategory.whiskerLeft_comp]
      erw [← adj₁.homEquiv_counit, tensorCounitTranspose_symm]
    simp only [← P₂.map_comp_assoc]
    rw [hq]
    simp only [MonoidalCategory.whiskerLeft_comp]
    erw [← P₁.map_comp_assoc, ← pf.assoc_assoc]
    rw [← associator_naturality_right_assoc]
    dsimp only [Functor.id_obj]
    erw [← rightUnitor_tensor_hom]

/-! ## The calculation on full domains of definition

The local data below name just the objects and projection instances in the calculation.
`X`, `Y`, and `R` are arbitrary full domains for the two left functors and the first
pullback functor. They need not be closed under tensor products. No functor or Hom
bijection is requested at an object outside these domains. The three objects `A`,
`V`, `T` stand for `S_g K`, `G_g 𝟙`, `G_g K`; `W`, `U`, `H` stand for `G_f 𝟙`,
`G_f V`, `G_f T`. The selected tensor comparison is the inverse strong tensorator.
-/

/-- The finite diagram of functors, Hom bijections and projection isomorphisms used in
both transposes. The functors are defined only on the indicated full domains.
Source: blueprint sec-six-functors-basics/sk-prop-cohsm, second paragraph, restricted
Hom-bijection interpretation (blueprint: lem-pur-composite-tensor-transpose). -/
structure CompositeTensorLocalData
    (C : Type uX) [Category.{vX} C] [MonoidalCategory C]
    (D : Type uY) [Category.{vY} D] [MonoidalCategory D]
    (E : Type uZ) [Category.{vZ} E] [MonoidalCategory E] where
  /-- Full domain of `P_f`. -/
  X : ObjectProperty C
  /-- Full domain of `P_g`. -/
  Y : ObjectProperty D
  /-- Full domain of `S_f`. -/
  R : ObjectProperty D
  /-- The first left functor on its domain. -/
  P : X.FullSubcategory ⥤ D
  /-- The second left functor on its domain. -/
  Q : Y.FullSubcategory ⥤ E
  /-- The first pullback functor on its domain. -/
  S : R.FullSubcategory ⥤ C
  /-- The target object. -/
  K : E
  /-- The objects `S_g K`, `G_g 𝟙`, and `G_g K`. -/
  A : R.FullSubcategory
  V : R.FullSubcategory
  T : R.FullSubcategory
  /-- The objects `G_f 𝟙`, `G_f V`, and `G_f T`. -/
  W : X.FullSubcategory
  U : X.FullSubcategory
  H : X.FullSubcategory
  /-- The coefficient tensor is in the domain of `S_f`. -/
  hAV : R (A.obj ⊗ V.obj)
  /-- The inverse tensorator of the specified strong monoidal comparison. -/
  delta : S.obj ⟨A.obj ⊗ V.obj, hAV⟩ ≅ S.obj A ⊗ S.obj V
  /-- Memberships of the five tensor sources in the domain of `P_f`. -/
  hN : X (S.obj ⟨A.obj ⊗ V.obj, hAV⟩ ⊗ W.obj)
  hVW : X (S.obj V ⊗ W.obj)
  hTW : X (S.obj T ⊗ W.obj)
  hAU : X (S.obj A ⊗ U.obj)
  hAVW : X (S.obj A ⊗ (S.obj V ⊗ W.obj))
  /-- Memberships of the seven sources in the domain of `P_g`. -/
  hPN : Y (P.obj ⟨S.obj ⟨A.obj ⊗ V.obj, hAV⟩ ⊗ W.obj, hN⟩)
  hPAU : Y (P.obj ⟨S.obj A ⊗ U.obj, hAU⟩)
  hAPU : Y (A.obj ⊗ P.obj U)
  hPU : Y (P.obj U)
  hV : Y V.obj
  hAVY : Y (A.obj ⊗ V.obj)
  hAVPW : Y ((A.obj ⊗ V.obj) ⊗ P.obj W)
  /-- The first adjunction Hom bijections, at the three target objects used. -/
  homFOne (M : X.FullSubcategory) : (P.obj M ⟶ 𝟙_ D) ≃ (M.obj ⟶ W.obj)
  homFV (M : X.FullSubcategory) : (P.obj M ⟶ V.obj) ≃ (M.obj ⟶ U.obj)
  homFT (M : X.FullSubcategory) : (P.obj M ⟶ T.obj) ≃ (M.obj ⟶ H.obj)
  /-- The second adjunction Hom bijections, at the two target objects used. -/
  homGOne (L : Y.FullSubcategory) : (Q.obj L ⟶ 𝟙_ E) ≃ (L.obj ⟶ V.obj)
  homGK (L : Y.FullSubcategory) : (Q.obj L ⟶ K) ≃ (L.obj ⟶ T.obj)
  /-- Contravariant naturality of the first Hom bijections at `V`. -/
  naturalFV {M M' : X.FullSubcategory} (a : M ⟶ M') (b : M'.obj ⟶ U.obj) :
    (homFV M).symm (a.hom ≫ b) = P.map a ≫ (homFV M').symm b
  /-- Contravariant naturality of the first Hom bijections at `G_g K`. -/
  naturalFT {M M' : X.FullSubcategory} (a : M ⟶ M') (b : M'.obj ⟶ H.obj) :
    (homFT M).symm (a.hom ≫ b) = P.map a ≫ (homFT M').symm b
  /-- Contravariant naturality of the second Hom bijections at `K`. -/
  naturalGK {L L' : Y.FullSubcategory} (a : L ⟶ L') (b : L'.obj ⟶ T.obj) :
    (homGK L).symm (a.hom ≫ b) = Q.map a ≫ (homGK L').symm b
  /-- The five instances of the first projection formula used in the calculation. -/
  pfAV : P.obj ⟨S.obj ⟨A.obj ⊗ V.obj, hAV⟩ ⊗ W.obj, hN⟩ ≅
    (A.obj ⊗ V.obj) ⊗ P.obj W
  pfT : P.obj ⟨S.obj T ⊗ W.obj, hTW⟩ ≅ T.obj ⊗ P.obj W
  pfV : P.obj ⟨S.obj V ⊗ W.obj, hVW⟩ ≅ V.obj ⊗ P.obj W
  pfAQ : P.obj ⟨S.obj A ⊗ (S.obj V ⊗ W.obj), hAVW⟩ ≅
    A.obj ⊗ P.obj ⟨S.obj V ⊗ W.obj, hVW⟩
  pfAU : P.obj ⟨S.obj A ⊗ U.obj, hAU⟩ ≅ A.obj ⊗ P.obj U
  /-- The two instances of the second projection formula used in the calculation. -/
  pgV : Q.obj ⟨A.obj ⊗ V.obj, hAVY⟩ ≅ K ⊗ Q.obj ⟨V.obj, hV⟩
  pgU : Q.obj ⟨A.obj ⊗ P.obj U, hAPU⟩ ≅ K ⊗ Q.obj ⟨P.obj U, hPU⟩

namespace CompositeTensorLocalData

variable {C : Type uX} [Category.{vX} C] [MonoidalCategory C]
  {D : Type uY} [Category.{vY} D] [MonoidalCategory D]
  {E : Type uZ} [Category.{vZ} E] [MonoidalCategory E]
  (d : CompositeTensorLocalData C D E)

/-- The first counit at the unit, obtained from the specified local Hom bijection.
Source: Stacks Tag 0037 (blueprint: lem-pur-composite-tensor-transpose). -/
def counitFOne : d.P.obj d.W ⟶ 𝟙_ D :=
  (d.homFOne d.W).symm (𝟙 d.W.obj)

/-- The first counit at `G_g 𝟙`, obtained from the specified local Hom bijection.
Source: Stacks Tag 0037 (blueprint: lem-pur-composite-tensor-transpose). -/
def counitFV : d.P.obj d.U ⟶ d.V.obj :=
  (d.homFV d.U).symm (𝟙 d.U.obj)

/-- The second counit at the unit, obtained from the specified local Hom bijection.
Source: Stacks Tag 0037 (blueprint: lem-pur-composite-tensor-transpose). -/
def counitGOne : d.Q.obj ⟨d.V.obj, d.hV⟩ ⟶ 𝟙_ E :=
  (d.homGOne ⟨d.V.obj, d.hV⟩).symm (𝟙 d.V.obj)

/-- The local tensor-counit transpose `τ_g K`.
Source: blueprint sec-six-functors-basics/sk-prop-cohsm, second paragraph
(blueprint: lem-pur-composite-tensor-transpose). -/
def tauG : d.A.obj ⊗ d.V.obj ⟶ d.T.obj :=
  d.homGK ⟨d.A.obj ⊗ d.V.obj, d.hAVY⟩
    (d.pgV.hom ≫ d.K ◁ d.counitGOne ≫ (ρ_ d.K).hom)

/-- The local tensor-counit transpose `q = τ_f V`.
Source: blueprint sec-six-functors-basics/sk-prop-cohsm, second paragraph
(blueprint: lem-pur-composite-tensor-transpose). -/
def q : d.S.obj d.V ⊗ d.W.obj ⟶ d.U.obj :=
  d.homFV ⟨d.S.obj d.V ⊗ d.W.obj, d.hVW⟩
    (d.pfV.hom ≫ d.V.obj ◁ d.counitFOne ≫ (ρ_ d.V.obj).hom)

/-- The first composite, formed using only local Hom bijections.
Source: blueprint sec-six-functors-basics/sk-prop-cohsm, second paragraph
(blueprint: lem-pur-composite-tensor-transpose). -/
def first : d.S.obj ⟨d.A.obj ⊗ d.V.obj, d.hAV⟩ ⊗ d.W.obj ⟶ d.H.obj :=
  (d.S.map (ObjectProperty.homMk d.tauG) ▷ d.W.obj) ≫
    d.homFT ⟨d.S.obj d.T ⊗ d.W.obj, d.hTW⟩
      (d.pfT.hom ≫ d.T.obj ◁ d.counitFOne ≫ (ρ_ d.T.obj).hom)

/-- The second composite, using the composite projection and composite counit.
Source: blueprint sec-six-functors-basics/sk-prop-cohsm, second paragraph
(blueprint: lem-pur-composite-tensor-transpose). -/
def second : d.S.obj ⟨d.A.obj ⊗ d.V.obj, d.hAV⟩ ⊗ d.W.obj ⟶ d.H.obj :=
  (d.delta.hom ▷ d.W.obj) ≫ (α_ (d.S.obj d.A) (d.S.obj d.V) d.W.obj).hom ≫
    (d.S.obj d.A ◁ d.q) ≫
    d.homFT ⟨d.S.obj d.A ⊗ d.U.obj, d.hAU⟩
      (d.homGK ⟨d.P.obj ⟨d.S.obj d.A ⊗ d.U.obj, d.hAU⟩, d.hPAU⟩
        (d.Q.map (ObjectProperty.homMk d.pfAU.hom) ≫ d.pgU.hom ≫
          (d.K ◁ (d.Q.map (ObjectProperty.homMk d.counitFV) ≫ d.counitGOne)) ≫
          (ρ_ d.K).hom))

/-- The explicit four-arrow inverse transpose on the local domains.
Source: blueprint sec-six-functors-basics/sk-prop-cohsm, second paragraph
(blueprint: lem-pur-composite-tensor-transpose). -/
def inverseTranspose : d.Q.obj
    ⟨d.P.obj ⟨d.S.obj ⟨d.A.obj ⊗ d.V.obj, d.hAV⟩ ⊗ d.W.obj, d.hN⟩, d.hPN⟩ ⟶ d.K :=
  d.Q.map (ObjectProperty.homMk
    (Y := ⟨(d.A.obj ⊗ d.V.obj) ⊗ d.P.obj d.W, d.hAVPW⟩) d.pfAV.hom) ≫
    d.Q.map (ObjectProperty.homMk
      (((d.A.obj ⊗ d.V.obj) ◁ d.counitFOne) ≫ (ρ_ (d.A.obj ⊗ d.V.obj)).hom)) ≫
    d.pgV.hom ≫ (d.K ◁ d.counitGOne) ≫ (ρ_ d.K).hom

/-- The particular naturality and projection-associativity equations used by the two
composites. They are instances of `Functor.ProjectionFormula`, not equations assuming
that the transposes are equal. No projection instance outside the local domains is required.
Source: blueprint sec-six-functors-basics/sk-prop-cohsm, second paragraph;
`def-sfb-projection-formula` (blueprint: lem-pur-composite-tensor-transpose). -/
structure Coherence : Prop where
  /-- Naturality of the first projection in the coefficient `τ_g K`. -/
  natural_left :
    d.P.map (ObjectProperty.homMk (d.S.map (ObjectProperty.homMk d.tauG) ▷ d.W.obj)) ≫
      d.pfT.hom = d.pfAV.hom ≫ d.tauG ▷ d.P.obj d.W
  /-- Naturality of the first projection in its second factor `q`. -/
  natural_right :
    d.P.map (ObjectProperty.homMk (d.S.obj d.A ◁ d.q)) ≫ d.pfAU.hom =
      d.pfAQ.hom ≫ d.A.obj ◁ d.P.map (ObjectProperty.homMk d.q)
  /-- Associativity of the first projection for the coefficients `S_g K`, `V`. -/
  assoc :
    d.pfAV.hom ≫ (α_ d.A.obj d.V.obj (d.P.obj d.W)).hom =
      d.P.map (ObjectProperty.homMk
        ((d.delta.hom ▷ d.W.obj) ≫
          (α_ (d.S.obj d.A) (d.S.obj d.V) d.W.obj).hom)) ≫
        d.pfAQ.hom ≫ d.A.obj ◁ d.pfV.hom
  /-- Naturality of the second projection in the first counit at `V`. -/
  natural_counit :
    d.Q.map (ObjectProperty.homMk (d.A.obj ◁ d.counitFV)) ≫ d.pgV.hom =
      d.pgU.hom ≫ d.K ◁ d.Q.map (ObjectProperty.homMk d.counitFV)

/-- The restricted-domain clause of the double-transpose calculation. The composite
inverse Hom bijection is literally the succession of the two given inverse Hom
bijections. This statement needs neither an ambient right adjoint nor monoidal closure
of the left functors' full domains.
Source: blueprint sec-six-functors-basics/sk-prop-cohsm, second paragraph; Stacks Tag 0037
(blueprint: lem-pur-composite-tensor-transpose).

Proof:
1. Expand `first`. Apply `naturalFT` to its initial arrow and cancel the first
   Hom bijection with its inverse. Use `Coherence.natural_left`, then right-unitor
   naturality, to put `tauG` after the first projection and counit. Apply `naturalGK`
   and cancel its defining Hom bijection. This gives `inverseTranspose`.
2. Expand `second` and cancel both Hom bijections after using `naturalFT` and
   `naturalGK`. Its counit is `Q(counitFV)` followed by `counitGOne` by construction.
   Use `Coherence.natural_right` to move `q` through the first projection, and
   `Coherence.natural_counit` to move the first counit through the second projection.
3. Use `naturalFV` on the arrow `q` and the identity of `U` to identify
   `P(q)` followed by `counitFV` with the defining inverse transpose of `q`.
   Substitute it and use `Coherence.assoc` and right-unitor naturality.
   The result is again `inverseTranspose`. Every map used has its domain membership
   recorded in `d`, so no value or equation outside those domains enters the proof.
4. The two asserted equations follow. Injectivity of the composite inverse Hom
   bijection also gives equality of the two original maps, without any invertibility
   assumption on `q`, either transpose, or the images of the unit objects.
-/
theorem composite_tensor_transpose_restricted (h : d.Coherence) :
    (d.homGK ⟨d.P.obj
        ⟨d.S.obj ⟨d.A.obj ⊗ d.V.obj, d.hAV⟩ ⊗ d.W.obj, d.hN⟩, d.hPN⟩).symm
      ((d.homFT ⟨d.S.obj ⟨d.A.obj ⊗ d.V.obj, d.hAV⟩ ⊗ d.W.obj, d.hN⟩).symm d.first) =
      d.inverseTranspose ∧
    (d.homGK ⟨d.P.obj
        ⟨d.S.obj ⟨d.A.obj ⊗ d.V.obj, d.hAV⟩ ⊗ d.W.obj, d.hN⟩, d.hPN⟩).symm
      ((d.homFT ⟨d.S.obj ⟨d.A.obj ⊗ d.V.obj, d.hAV⟩ ⊗ d.W.obj, d.hN⟩).symm d.second) =
      d.inverseTranspose := by
  have hfirst :
      (d.homFT ⟨_, d.hN⟩).symm d.first =
        d.pfAV.hom ≫ (d.A.obj ⊗ d.V.obj) ◁ d.counitFOne ≫
          (ρ_ (d.A.obj ⊗ d.V.obj)).hom ≫ d.tauG := by
    unfold first
    erw [d.naturalFT, Equiv.symm_apply_apply]
    rw [← Category.assoc]
    erw [h.natural_left]
    simp only [Category.assoc]
    rw [← whisker_exchange_assoc, rightUnitor_naturality]
  constructor
  · rw [hfirst, ← Category.assoc, ← Category.assoc]
    erw [d.naturalGK, Equiv.symm_apply_apply]
    unfold inverseTranspose
    simp only [← d.Q.map_comp_assoc, Category.assoc]
    rfl
  · let a : (⟨_, d.hN⟩ : d.X.FullSubcategory) ⟶ ⟨_, d.hAU⟩ :=
      ObjectProperty.homMk ((d.delta.hom ▷ d.W.obj) ≫
        (α_ (d.S.obj d.A) (d.S.obj d.V) d.W.obj).hom ≫ d.S.obj d.A ◁ d.q)
    have hs : d.second = a.hom ≫ d.homFT ⟨_, d.hAU⟩
        (d.homGK ⟨_, d.hPAU⟩
          (d.Q.map (ObjectProperty.homMk d.pfAU.hom) ≫ d.pgU.hom ≫
            (d.K ◁ (d.Q.map (ObjectProperty.homMk d.counitFV) ≫ d.counitGOne)) ≫
            (ρ_ d.K).hom)) := by
      simp only [second, a, ObjectProperty.homMk_hom, Category.assoc]
    rw [hs, d.naturalFT, Equiv.symm_apply_apply]
    erw [d.naturalGK, Equiv.symm_apply_apply]
    rw [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    have hq : d.P.map (ObjectProperty.homMk d.q) ≫ d.counitFV =
        d.pfV.hom ≫ d.V.obj ◁ d.counitFOne ≫ (ρ_ d.V.obj).hom := by
      have hn := d.naturalFV
        (ObjectProperty.homMk (X := ⟨_, d.hVW⟩) (Y := d.U) d.q) (𝟙 d.U.obj)
      simpa only [ObjectProperty.homMk_hom, Category.comp_id, q,
        Equiv.symm_apply_apply, counitFV] using hn.symm
    let c : (⟨_, d.hN⟩ : d.X.FullSubcategory) ⟶ ⟨_, d.hAVW⟩ :=
      ObjectProperty.homMk ((d.delta.hom ▷ d.W.obj) ≫
        (α_ (d.S.obj d.A) (d.S.obj d.V) d.W.obj).hom)
    let b : (⟨_, d.hAVW⟩ : d.X.FullSubcategory) ⟶ ⟨_, d.hAU⟩ :=
      ObjectProperty.homMk (d.S.obj d.A ◁ d.q)
    have ha : a = c ≫ b := by
      apply ObjectProperty.hom_ext
      simp only [a, b, c, ObjectProperty.homMk_hom,
        ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
    have hr : d.P.map b ≫ d.pfAU.hom =
        d.pfAQ.hom ≫ d.A.obj ◁ d.P.map (ObjectProperty.homMk d.q) := by
      exact h.natural_right
    have hc : d.P.map a ≫ d.pfAU.hom ≫ d.A.obj ◁ d.counitFV =
        d.pfAV.hom ≫ (d.A.obj ⊗ d.V.obj) ◁ d.counitFOne ≫
          (ρ_ (d.A.obj ⊗ d.V.obj)).hom := by
      rw [ha, d.P.map_comp, Category.assoc, ← Category.assoc (d.P.map b), hr]
      simp only [Category.assoc]
      rw [← MonoidalCategory.whiskerLeft_comp, hq,
        MonoidalCategory.whiskerLeft_comp, ← Category.assoc]
      rw [← Category.assoc (d.P.map c ≫ d.pfAQ.hom)]
      have hassoc : d.pfAV.hom ≫ (α_ d.A.obj d.V.obj (d.P.obj d.W)).hom =
          (d.P.map c ≫ d.pfAQ.hom) ≫ d.A.obj ◁ d.pfV.hom := by
        simpa only [c, Category.assoc] using h.assoc
      rw [← hassoc, Category.assoc, tensor_counit_assoc]
    rw [← Category.assoc d.pgU.hom]
    erw [← h.natural_counit]
    simp only [← d.Q.map_comp_assoc]
    unfold inverseTranspose
    simp only [Category.assoc, ← d.Q.map_comp_assoc]
    congr 1
    apply congrArg d.Q.map
    apply ObjectProperty.hom_ext
    simpa only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      Category.assoc] using hc

end CompositeTensorLocalData

end SecSmoothPurity
