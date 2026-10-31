/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionModels
public import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.SixFunctors.IntegralHom.Evaluation.IntegralHomEvaluationNaturality

/-! # Naturality of the normalized tensor adjoint comparison

Source: the normalized tensor-presentation argument in paragraph 5 of the finite
coefficient extension proof; Stacks Project, Tags 07A4 and 08J9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures.IntegralFiniteExtension

private theorem parameter_uncurry
    {D : Type v} [Category.{w} D] (F : D ⥤ D ⥤ D) (H : Dᵒᵖ ⥤ D ⥤ D)
    (ad : ∀ K, F.obj K ⊣ H.obj (op K))
    (hn : ∀ (K K' W : D) (f : K' ⟶ K),
      (F.obj K').map ((H.map f.op).app W) ≫ (ad K').counit.app W =
        (F.map f).app ((H.obj (op K)).obj W) ≫ (ad K).counit.app W)
    {K K' N W : D} (f : K' ⟶ K) (q : N ⟶ (H.obj (op K)).obj W) :
    ((ad K').homEquiv N W).symm (q ≫ (H.map f.op).app W) =
      (F.map f).app N ≫ ((ad K).homEquiv N W).symm q := by
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  rw [Functor.map_comp, Category.assoc, hn, ← Category.assoc,
    (F.map f).naturality q, Category.assoc]

private theorem parameter_curry
    {D : Type v} [Category.{w} D] (F : D ⥤ D ⥤ D) (H : Dᵒᵖ ⥤ D ⥤ D)
    (ad : ∀ K, F.obj K ⊣ H.obj (op K))
    (hn : ∀ (K K' W : D) (f : K' ⟶ K),
      (F.obj K').map ((H.map f.op).app W) ≫ (ad K').counit.app W =
        (F.map f).app ((H.obj (op K)).obj W) ≫ (ad K).counit.app W)
    {K K' N W : D} (f : K' ⟶ K) (g : (F.obj K).obj N ⟶ W) :
    (ad K').homEquiv N W ((F.map f).app N ≫ g) =
      (ad K).homEquiv N W g ≫ (H.map f.op).app W := by
  apply ((ad K').homEquiv N W).symm.injective
  rw [Equiv.symm_apply_apply, parameter_uncurry F H ad hn, Equiv.symm_apply_apply]

private theorem comparison_curry
    {D : Type v} [Category.{w} D] {T U : D ⥤ D} {H : D ⥤ D}
    (ad : T ⊣ H) (bd : U ⊣ H) (N W : D) (g : U.obj N ⟶ W) :
    ad.homEquiv N W ((Adjunction.leftAdjointUniq ad bd).hom.app N ≫ g) =
      bd.homEquiv N W g := by
  rw [ad.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    Adjunction.homEquiv_unit]

private theorem parameter_comparison
    {D : Type v} [Category.{w} D] (F G : D ⥤ D ⥤ D) (H : Dᵒᵖ ⥤ D ⥤ D)
    (ad : ∀ K, F.obj K ⊣ H.obj (op K))
    (bd : ∀ K, G.obj K ⊣ H.obj (op K))
    (ha : ∀ (K K' W : D) (f : K' ⟶ K),
      (F.obj K').map ((H.map f.op).app W) ≫ (ad K').counit.app W =
        (F.map f).app ((H.obj (op K)).obj W) ≫ (ad K).counit.app W)
    (hb : ∀ (K K' W : D) (f : K' ⟶ K),
      (G.obj K').map ((H.map f.op).app W) ≫ (bd K').counit.app W =
        (G.map f).app ((H.obj (op K)).obj W) ≫ (bd K).counit.app W)
    (P Q : D × D) (f : P ⟶ Q) :
    (Functor.uncurry.obj F).map f ≫
        (Adjunction.leftAdjointUniq (ad Q.1) (bd Q.1)).hom.app Q.2 =
      (Adjunction.leftAdjointUniq (ad P.1) (bd P.1)).hom.app P.2 ≫
        (Functor.uncurry.obj G).map f := by
  have hfirst : (F.map f.1).app P.2 ≫
        (Adjunction.leftAdjointUniq (ad Q.1) (bd Q.1)).hom.app P.2 =
      (Adjunction.leftAdjointUniq (ad P.1) (bd P.1)).hom.app P.2 ≫ (G.map f.1).app P.2 := by
    apply ((ad P.1).homEquiv P.2 _).injective
    rw [parameter_curry F H ad ha, comparison_curry,
      Adjunction.homEquiv_leftAdjointUniq_hom_app]
    have h := parameter_curry G H bd hb f.1 (𝟙 ((G.obj Q.1).obj P.2))
    simpa only [Category.comp_id, Adjunction.homEquiv_id] using h.symm
  have hsecond := (Adjunction.leftAdjointUniq (ad Q.1) (bd Q.1)).hom.naturality f.2
  change ((F.map f.1).app P.2 ≫ (F.obj Q.1).map f.2) ≫ _ =
    _ ≫ (G.map f.1).app P.2 ≫ (G.obj Q.1).map f.2
  rw [Category.assoc, hsecond, ← Category.assoc, hfirst, Category.assoc]

/-- The pointwise unique comparisons of left adjoints are natural in both inputs.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/
lem-coef-integral-finite-extension.proof.md, paragraph 5; Stacks Tags 07A4 and 08J9.

Proof: evaluation_naturality for a and for scalarIntegralClosed first gives
naturality of inverse transposition in the parameter: expand the inverse Hom
bijection as the tensor map followed by the counit; use evaluation_naturality
and the naturality of the tensor map. Apply the forward bijection to obtain
parameter naturality of transposition. The unique left-adjoint comparison
intertwines the two Hom bijections. Thus, after applying the bijection for a,
the first-variable naturality square becomes the same parameter identity on
both sides. Injectivity proves that square. Naturality of leftAdjointUniq in
its ordinary input supplies the second-variable square. Factor a morphism of
the product category into its first- and second-variable maps and paste the
two squares. This uses no scalar extension or finite-free calculation.
(blueprint: new-sf-integral-hom-tensor-adjoint-naturality). -/
theorem tensorAdjointComparison_naturality
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u})
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (P Q : IntegralVerdier.Ambient l E X × IntegralVerdier.Ambient l E X)
    (f : P ⟶ Q) :
    a.tensor.map f ≫
        (Adjunction.leftAdjointUniq (a.adjunction Q.1)
          ((scalarIntegralClosed l E X).adjunction Q.1)).hom.app Q.2 =
      (Adjunction.leftAdjointUniq (a.adjunction P.1)
          ((scalarIntegralClosed l E X).adjunction P.1)).hom.app P.2 ≫
        (scalarIntegralClosed l E X).tensor.map (Prod.mkHom f.2 f.1) := by
  let S := scalarIntegralClosed l E X
  let := S.monoidal
  have h := parameter_comparison (Functor.curry.obj a.tensor)
    (MonoidalCategory.curriedTensor _).flip
    (Functor.curry.obj (IntegralHom.hom.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X)))
    a.adjunction S.adjunction (IntegralHom.evaluation_naturality X _ a)
    S.evaluation_naturality P Q f
  have hm : (Functor.uncurry.obj (Functor.curry.obj a.tensor)).map f = a.tensor.map f := by
    simp only [Functor.uncurry_obj_map, Functor.curry_obj_map_app,
      Functor.curry_obj_obj_map, ← Functor.map_comp, prod_comp,
      Category.comp_id, Category.id_comp]
    congr 1
  rw [hm] at h
  simpa only [Functor.uncurry_obj_map, Functor.flip_map_app, Functor.flip_obj_map,
    MonoidalCategory.curriedTensor_obj_map, MonoidalCategory.curriedTensor_map_app,
    CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map,
    MonoidalCategory.tensorHom_def'] using h

/-- The explicitly constructed tensor comparison: its components are the unique
left-adjoint comparisons, and only their naturality uses the preceding theorem.
Source: Stacks Tags 07A4 and 08J9
(blueprint: new-sf-integral-hom-tensor-adjoint-naturality). -/
def tensorAdjointComparison
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u})
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X)) :
    a.tensor ≅
      CategoryTheory.Prod.swap (IntegralVerdier.Ambient l E X) (IntegralVerdier.Ambient l E X) ⋙
        (scalarIntegralClosed l E X).tensor :=
  NatIso.ofComponents
    (fun P ↦ (Adjunction.leftAdjointUniq (a.adjunction P.1)
      ((scalarIntegralClosed l E X).adjunction P.1)).app P.2)
    (fun f ↦ tensorAdjointComparison_naturality l E X a _ _ f)

end WeilConjectures.IntegralFiniteExtension
