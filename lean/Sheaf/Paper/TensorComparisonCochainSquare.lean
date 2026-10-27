/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SemilinearSystemModels
import all Sheaf.Paper.SystemCochainTensorReduction

/-! # Cochain compatibility of four normalized tensor models

Source: Stacks 07A4, lemma-pullback-tensor-product.
(blueprint: lem-coef-semilinear-tensor-comparison-cochain-square)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option genInjectivity false
set_option genSizeOfSpec false
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  HasDerivedCategory.standard DerivedCategory SheafOfModules.monoidalCategory
  CoefficientClosedStructure.tensor

variable {C₀ C₁ C₂ C₃ : Type c}
  [Category.{v} C₀] [Category.{v} C₁] [Category.{v} C₂] [Category.{v} C₃]
  [EssentiallySmall.{max c v r} C₀] [EssentiallySmall.{max c v r} C₁]
  [EssentiallySmall.{max c v r} C₂] [EssentiallySmall.{max c v r} C₃]
  (J₀ : GrothendieckTopology C₀) (J₁ : GrothendieckTopology C₁)
  (J₂ : GrothendieckTopology C₂) (J₃ : GrothendieckTopology C₃)
  (R₀ : Sheaf J₀ CommRingCat.{max c v r}) (R₁ : Sheaf J₁ CommRingCat.{max c v r})
  (R₂ : Sheaf J₂ CommRingCat.{max c v r}) (R₃ : Sheaf J₃ CommRingCat.{max c v r})
  (F : Mod.{c, v, max c v r} J₀ R₀ ⥤ Mod.{c, v, max c v r} J₁ R₁)
  (G : Mod.{c, v, max c v r} J₁ R₁ ⥤ Mod.{c, v, max c v r} J₃ R₃)
  (H : Mod.{c, v, max c v r} J₀ R₀ ⥤ Mod.{c, v, max c v r} J₂ R₂)
  (I : Mod.{c, v, max c v r} J₂ R₂ ⥤ Mod.{c, v, max c v r} J₃ R₃)
  [F.Additive] [G.Additive] [H.Additive] [I.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I]
  (S₀ : Closed.{c, v, r} J₀ R₀) (S₁ : Closed.{c, v, r} J₁ R₁)
  (S₂ : Closed.{c, v, r} J₂ R₂) (S₃ : Closed.{c, v, r} J₃ R₃)
  (T₀ : Models.{c, v, r} J₀ R₀ S₀) (T₁ : Models.{c, v, r} J₁ R₁ S₁)
  (T₂ : Models.{c, v, r} J₂ R₂ S₂) (T₃ : Models.{c, v, r} J₃ R₃ S₃)
  (μF : S₀.tensor ⋙ F.mapDerivedCategory ≅
    (F.mapDerivedCategory.prod F.mapDerivedCategory) ⋙ S₁.tensor)
  (μG : S₁.tensor ⋙ G.mapDerivedCategory ≅
    (G.mapDerivedCategory.prod G.mapDerivedCategory) ⋙ S₃.tensor)
  (μH : S₀.tensor ⋙ H.mapDerivedCategory ≅
    (H.mapDerivedCategory.prod H.mapDerivedCategory) ⋙ S₂.tensor)
  (μI : S₂.tensor ⋙ I.mapDerivedCategory ≅
    (I.mapDerivedCategory.prod I.mapDerivedCategory) ⋙ S₃.tensor)
  (tF : TensorComparisonModel.{c, v, r} J₀ J₁ R₀ R₁ F S₀ S₁ T₀ T₁ μF)
  (tG : TensorComparisonModel.{c, v, r} J₁ J₃ R₁ R₃ G S₁ S₃ T₁ T₃ μG)
  (tH : TensorComparisonModel.{c, v, r} J₀ J₂ R₀ R₂ H S₀ S₂ T₀ T₂ μH)
  (tI : TensorComparisonModel.{c, v, r} J₂ J₃ R₂ R₃ I S₂ S₃ T₂ T₃ μI)
  (θ : F ⋙ G ≅ H ⋙ I)
  (ho : ∀ M N,
    G.map (tF.ordinary M N).hom ≫ (tG.ordinary (F.obj M) (F.obj N)).hom ≫
      ordinaryTensorHom.{c, v, r} J₃ R₃ (θ.hom.app M) (θ.hom.app N) =
    θ.hom.app (ordinaryTensor.{c, v, r} J₀ R₀ M N) ≫
      I.map (tH.ordinary M N).hom ≫ (tI.ordinary (H.obj M) (H.obj N)).hom)


include ho in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Compatibility of four ordinary tensor comparisons implies compatibility of
these comparisons on total tensor cochain complexes.
Source: Stacks 07A4, lemma-pullback-tensor-product, the signed total comparison.
(blueprint: lem-coef-semilinear-tensor-comparison-cochain-square).

Proof: compare the degree-k maps on every (p,q) summand. The four model summand
formulas reduce the two routes to the inverse ordinary comparison square.
Naturality of θ moves the source summand inclusion through θ. Inverting the
ordinary square by its two composite isomorphisms and postcomposing with the
mapped inclusion proves the summand equation. Extensionality for the total tensor
and then for homological-complex morphisms proves the result. All comparisons
are already cochain maps, so no additional differential compatibility is needed. -/
theorem tensorComparisonCochainSquare
    (P Q : CochainComplex (Mod.{c, v, max c v r} J₀ R₀) ℤ) :
    tG.chain ((F.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.mapHomologicalComplex (.up ℤ)).obj Q) ≫
      (G.mapHomologicalComplex (.up ℤ)).map (tF.chain P Q) ≫
      (NatTrans.mapHomologicalComplex θ.hom (.up ℤ)).app
        ((totalTensor.{c, v, r} J₀ R₀).obj (P, Q)) =
    (totalTensor.{c, v, r} J₃ R₃).map
        (Prod.mkHom ((NatTrans.mapHomologicalComplex θ.hom (.up ℤ)).app P)
          ((NatTrans.mapHomologicalComplex θ.hom (.up ℤ)).app Q)) ≫
      tI.chain ((H.mapHomologicalComplex (.up ℤ)).obj P)
        ((H.mapHomologicalComplex (.up ℤ)).obj Q) ≫
      (I.mapHomologicalComplex (.up ℤ)).map (tH.chain P Q) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R₃
  let := SheafOfModules.monoidalCategory R₃
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R₃
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R₃
  apply HomologicalComplex.hom_ext
  intro k
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  change tensorSummand.{c, v, r} J₃ R₃ _ _ p q k hpq ≫ _ =
    tensorSummand.{c, v, r} J₃ R₃ _ _ p q k hpq ≫ _
  erw [reassoc_of% (tG.summand ((F.mapHomologicalComplex (.up ℤ)).obj P)
    ((F.mapHomologicalComplex (.up ℤ)).obj Q) p q k hpq)]
  have hsF := congrArg G.map (tF.summand P Q p q k hpq)
  simp only [G.map_comp] at hsF
  erw [reassoc_of% hsF]
  have hn := θ.hom.naturality (tensorSummand.{c, v, r} J₀ R₀ P Q p q k hpq)
  dsimp only [Functor.comp_map] at hn
  erw [hn]
  erw [reassoc_of% (tensorSummand_map.{c, v, r} J₃ R₃
    ((NatTrans.mapHomologicalComplex θ.hom (.up ℤ)).app P)
    ((NatTrans.mapHomologicalComplex θ.hom (.up ℤ)).app Q) p q k hpq)]
  conv_rhs => erw [reassoc_of% (tI.summand ((H.mapHomologicalComplex (.up ℤ)).obj P)
    ((H.mapHomologicalComplex (.up ℤ)).obj Q) p q k hpq)]
  have hsH := congrArg I.map (tH.summand P Q p q k hpq)
  simp only [I.map_comp] at hsH
  erw [hsH]
  change (tG.ordinary (F.obj (P.X p)) (F.obj (Q.X q))).inv ≫
      G.map (tF.ordinary (P.X p) (Q.X q)).inv ≫
      θ.hom.app (ordinaryTensor.{c, v, r} J₀ R₀ (P.X p) (Q.X q)) ≫
      I.map (H.map (tensorSummand.{c, v, r} J₀ R₀ P Q p q k hpq)) =
    ordinaryTensorHom.{c, v, r} J₃ R₃ (θ.hom.app (P.X p)) (θ.hom.app (Q.X q)) ≫
      (tI.ordinary (H.obj (P.X p)) (H.obj (Q.X q))).inv ≫
      I.map (tH.ordinary (P.X p) (Q.X q)).inv ≫
      I.map (H.map (tensorSummand.{c, v, r} J₀ R₀ P Q p q k hpq))
  let u := G.mapIso (tF.ordinary (P.X p) (Q.X q)) ≪≫
    tG.ordinary (F.obj (P.X p)) (F.obj (Q.X q))
  let w := I.mapIso (tH.ordinary (P.X p) (Q.X q)) ≪≫
    tI.ordinary (H.obj (P.X p)) (H.obj (Q.X q))
  have hi : u.inv ≫ θ.hom.app (ordinaryTensor.{c, v, r} J₀ R₀ (P.X p) (Q.X q)) =
      ordinaryTensorHom.{c, v, r} J₃ R₃ (θ.hom.app (P.X p)) (θ.hom.app (Q.X q)) ≫
        w.inv := by
    apply (Iso.inv_comp_eq u).2
    rw [← Category.assoc]
    apply (Iso.eq_comp_inv w).2
    exact (ho (P.X p) (Q.X q)).symm
  simpa only [u, w, Iso.trans_inv, Functor.mapIso_inv, Category.assoc] using
    congrArg (fun f ↦ f ≫
      I.map (H.map (tensorSummand.{c, v, r} J₀ R₀ P Q p q k hpq))) hi


end WeilConjectures.SemilinearSections
