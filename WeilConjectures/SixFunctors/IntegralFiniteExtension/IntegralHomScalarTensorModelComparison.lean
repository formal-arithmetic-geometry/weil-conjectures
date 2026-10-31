/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionModels
public import WeilConjectures.TraceFormula.Integral.IntegralScalarOrdinaryModelComparison
public import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.SixFunctors.IntegralFiniteExtension.IntegralHomScalarTensorRepresentativeComparison

/-! # Tensor normalization under a change of integral Hom presentations

This comparison concerns the tensor bifunctors, before taking an internal-Hom mate.
Source: the representative normalization in paragraph 5 of the finite coefficient
extension proof; Stacks Project, Tags 06YY, 07A4 and 08J9.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension

/-- Normalized scalar tensor comparisons commute with the unique comparisons of
left adjoints to the same internal Hom.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/
lem-coef-integral-finite-extension.proof.md, paragraph 5, transport through the
normalized tensor presentations; Stacks Project, Tags 06YY, 07A4 and 08J9.

Proof: for each K use uniqueness of left adjoints to compare a.tensor(K,-) with
scalarIntegralClosed.tensor(-,K). The comparison preserves the counits by
leftAdjointUniq_hom_app_counit. On K-flat representatives P,Q it carries
a.representative(P,Q) to the native representative for (Q,P), preceded by the
Koszul interchange P tensor Q to Q tensor P. To check this equality, test maps
into a K-injective complex I. Represent maps from Q to Hom(P,I) by chain maps;
Hom(P,I) is K-injective because P is K-flat. TensorPresentation.evaluation and
coefficientTensorCurry_normalize identify their uncurrying on both sides.
Their pure-section formulas agree: the Koszul interchange supplies exactly
(-1)^(degree(P)*degree(Q)), the sign in the supplied evaluation. The adjunction
bijections and K-injective resolution then give equality of the comparisons.
This also makes the comparison natural in both tensor variables.

Apply the same argument to b. On each pair of flat-term K-flat representatives,
the pure-section hypothesis on t identifies the two ordinary scalar tensor
comparisons, including their interchange maps. The hypothesis on e identifies
their derived counits. Substitute these identities and the representative
comparisons just obtained into the normalization of scalarClosedTensor. The
result is the defining representative square of PurCompactSupport.scalarTensor.
Uniqueness of that normalized comparison, followed by resolving both inputs,
gives the displayed tensor square. No finite-free Hom computation or
invertibility of an internal-Hom comparison is used. Zero inputs, equal fields
and the empty scheme satisfy the same representative equations.
(blueprint: lem-sf-integral-hom-scalar-tensor-model-comparison). -/
theorem scalarTensor_model_comparison
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (t : integralOrdinaryScalar l E L ι X ≅
      completedOrdinaryScalarExtension.{u, u} l E L ι X)
    (e : integralOrdinaryDerivedScalar l E L ι X ≅
      completedDerivedScalarExtension.{u, u} l E L ι X)
    (ht : ∀ (N : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj U)
      (x : N.val.obj U),
      (t.hom.app N).val.app U (integralOrdinaryTensorSection l E L ι X N U s x) =
        completedScalarTensorSection.{u, u} l E L ι X N U s x)
    (he : ∀ P : CochainComplex (integralTowerModules l E X) ℤ,
      e.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit.{u, u} l E L ι X P =
        (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex t (.up ℤ)).hom.app P))
    (K N : IntegralVerdier.Ambient l E X) :
    (pbcDerivedExtend (completedCoefficientMap l E L ι X)).map
        ((Adjunction.leftAdjointUniq (a.adjunction K)
          ((scalarIntegralClosed l E X).adjunction K)).hom.app N) ≫
      (Functor.isoWhiskerLeft (scalarIntegralClosed l E X).tensor e.symm ≪≫
        scalarClosedTensor l E L ι X ≪≫
        Functor.isoWhiskerRight (NatIso.prod e e) (scalarIntegralClosed l L X).tensor).hom.app
          (N, K) =
    (PurCompactSupport.scalarTensor (completedCoefficientMap l E L ι X)
        (tensorModel X a) (tensorModel X b)).hom.app (K, N) ≫
      (Adjunction.leftAdjointUniq
        (b.adjunction ((pbcDerivedExtend (completedCoefficientMap l E L ι X)).obj K))
        ((scalarIntegralClosed l L X).adjunction
          ((pbcDerivedExtend (completedCoefficientMap l E L ι X)).obj K))).hom.app
            ((pbcDerivedExtend (completedCoefficientMap l E L ι X)).obj N) := by
  have hμ : scalarTensorTransport l E L ι X a b e =
      PurCompactSupport.scalarTensor (completedCoefficientMap l E L ι X)
        (tensorModel X a) (tensorModel X b) := by
    apply (PurCompactSupport.scalarTensor_existsUnique
      (completedCoefficientMap l E L ι X) (tensorModel X a) (tensorModel X b)).unique
    · exact scalarTensorTransport_normalization l E L ι X a b t e ht he
    · exact (PurCompactSupport.scalarTensor_existsUnique
        (completedCoefficientMap l E L ι X)
        (tensorModel X a) (tensorModel X b)).exists.choose_spec
  apply (cancel_mono ((tensorAdjointComparison l L X b).inv.app
    ((pbcDerivedExtend (completedCoefficientMap l E L ι X)).obj K,
      (pbcDerivedExtend (completedCoefficientMap l E L ι X)).obj N))).1
  change _ = (_ ≫ (tensorAdjointComparison l L X b).hom.app
    ((pbcDerivedExtend (completedCoefficientMap l E L ι X)).obj K,
      (pbcDerivedExtend (completedCoefficientMap l E L ι X)).obj N)) ≫
      (tensorAdjointComparison l L X b).inv.app
        ((pbcDerivedExtend (completedCoefficientMap l E L ι X)).obj K,
          (pbcDerivedExtend (completedCoefficientMap l E L ι X)).obj N)
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  exact congrArg (fun μ ↦ μ.hom.app (K, N)) hμ

end WeilConjectures.IntegralFiniteExtension
