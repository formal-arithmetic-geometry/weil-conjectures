/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M8
-/
module

public import Sheaf.SixFunctors.IntegralHomTensorAdjointNaturality
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison

/-! # Representative normalization of the transported scalar tensor comparison

Source: paragraph 5 of the finite coefficient extension proof; Stacks Project,
Tags 06YY, 07A4 and 08J9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u a₀ b₀ v₀ w₀
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension

/-- Conjugate a tensor comparison by two tensor isomorphisms with swapped inputs.
Source: the formal transport in Stacks Tags 06YY and 07A4
(blueprint: new-sf-integral-hom-scalar-tensor-representatives). -/
def scalarTensorTransportOfSwap
    {A : Type a₀} [Category.{v₀} A] {B : Type b₀} [Category.{w₀} B]
    {TA SA : A × A ⥤ A} {TB SB : B × B ⥤ B}
    (i : TA ≅ CategoryTheory.Prod.swap A A ⋙ SA)
    (j : TB ≅ CategoryTheory.Prod.swap B B ⋙ SB)
    (G : A ⥤ B) (μ : SA ⋙ G ≅ G.prod G ⋙ SB) :
    TA ⋙ G ≅ G.prod G ⋙ TB :=
  Functor.isoWhiskerRight i G ≪≫
    Functor.isoWhiskerLeft (CategoryTheory.Prod.swap A A) μ ≪≫
    Functor.isoWhiskerLeft (G.prod G) j.symm

attribute [local irreducible] scalarIntegralClosed integralDerivedInternalHom
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  HasDerivedCategory.standard tensorAdjointComparison

/-- Transport the canonical tensor comparison using the explicitly specified
adjoint comparisons in both coefficient categories. No witness is chosen here.
Source: Stacks Tags 06YY and 07A4
(blueprint: new-sf-integral-hom-scalar-tensor-representatives). -/
def scalarTensorTransport
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (e : integralOrdinaryDerivedScalar l E L ι X ≅
      completedDerivedScalarExtension.{u, u} l E L ι X) :
    a.tensor ⋙ pbcDerivedExtend (completedCoefficientMap l E L ι X) ≅
      ((pbcDerivedExtend (completedCoefficientMap l E L ι X)).prod
        (pbcDerivedExtend (completedCoefficientMap l E L ι X))) ⋙ b.tensor :=
  scalarTensorTransportOfSwap (tensorAdjointComparison l E X a) (tensorAdjointComparison l L X b)
    (pbcDerivedExtend (completedCoefficientMap l E L ι X))
    (Functor.isoWhiskerLeft (scalarIntegralClosed l E X).tensor e.symm ≪≫
      scalarClosedTensor l E L ι X ≪≫
      Functor.isoWhiskerRight (NatIso.prod e e) (scalarIntegralClosed l L X).tensor)

/-- On flat-term K-flat representatives the transported comparison is normalized
by the ordinary scalar tensor map and the fixed cochain counits.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/
lem-coef-integral-finite-extension.proof.md, paragraph 5; Stacks Tags 06YY, 07A4, 08J9.

Proof: first identify the source adjoint comparison on a K-flat pair (P,Q) with
its canonical reversed representative after Koszul interchange. Test maps into
a K-injective complex and apply TensorPresentation.evaluation and
coefficientTensorCurry_normalize. The same argument applies over L to the
termwise scalar-extended pair. Base change preserves flat terms and K-flatness,
so these target representatives are allowed. The section equation ht identifies
the ordinary scalar extension units, hence identifies the ordinary scalar tensor
maps: check their values on s tensor (x tensor y), which generate after module
sheafification. Naturality of t and the signed interchange then give the same
equality on total tensor complexes. The two Koszul interchanges cancel, since
their signs multiply to one. The cochain equation he identifies the two derived
counits. Substitute these equations in scalarClosedTensorNormalization and use
naturality of the two representative isomorphisms to move the termwise map t
across them. The adjacent inverse comparison maps cancel, leaving exactly the
displayed representative square. This is a calculation on the stated complexes;
it does not identify global natural transformations or use scalarTensor itself.
Zero complexes, zero coefficient rings and the empty scheme require no exception.
(blueprint: new-sf-integral-hom-scalar-tensor-representatives). -/
theorem scalarTensorTransport_normalization
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
    (P Q : CochainComplex (integralTowerModules l E X) ℤ)
    (hp : proEtaleFlatRepresentatives X
      (completedIntegralCommRingSheafUnrestricted l E X) P)
    (hq : proEtaleFlatRepresentatives X
      (completedIntegralCommRingSheafUnrestricted l E X) Q) :
    ∃ (hp' : proEtaleFlatRepresentatives X
          (completedIntegralCommRingSheafUnrestricted l L X)
          (((pbcExtend (completedCoefficientMap l E L ι X)).mapHomologicalComplex
            (.up ℤ)).obj P))
      (hq' : proEtaleFlatRepresentatives X
          (completedIntegralCommRingSheafUnrestricted l L X)
          (((pbcExtend (completedCoefficientMap l E L ι X)).mapHomologicalComplex
            (.up ℤ)).obj Q)),
      (pbcDerivedExtend (completedCoefficientMap l E L ι X)).map
          ((tensorModel X a).representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
        (scalarTensorTransport l E L ι X a b e).hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        b.tensor.map (Prod.mkHom (pbcComplexCounit (completedCoefficientMap l E L ι X) P)
          (pbcComplexCounit (completedCoefficientMap l E L ι X) Q)) =
      pbcComplexCounit (completedCoefficientMap l E L ι X)
          (((IntegralHom.totalTensor.{u, u} X
            (completedIntegralCommRingSheafUnrestricted l E X)).obj P).obj Q) ≫
        DerivedCategory.Q.map
          (@inv _ _ _ _ (PurCompactSupport.scalarTensorTotal
              (completedCoefficientMap l E L ι X) P Q)
            (PurCompactSupport.scalarTensorTotal_isIso
              (completedCoefficientMap l E L ι X) P Q)) ≫
        (tensorModel X b).representative.hom.app (⟨_, hp'⟩, ⟨_, hq'⟩) := by sorry

end WeilConjectures.IntegralFiniteExtension
