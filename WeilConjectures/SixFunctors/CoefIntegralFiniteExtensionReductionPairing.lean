/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefIntegralFiniteExtensionCore
import WeilConjectures.SixFunctors.CoefIntegralFiniteExtensionDeltaSquare
import WeilConjectures.SixFunctors.CoefIntegralFiniteExtensionHomReductionSquare
import WeilConjectures.SixFunctors.CoefIntegralFiniteExtensionBetaReductionSquare

/-! # Canonical integral finite-extension comparisons

Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower, order 2494
(blueprint: lem-coef-integral-finite-extension).

The defining comparisons are publicly re-exported from the models module.
This module fixes the maps and predicates independently of their compatibility theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.derivedInternalHomOfUniverses
  CategoryTheory.homComplexFunctor
  WeilConjectures.IntegralHom.totalTensor WeilConjectures.IntegralHom.homModelMap
  WeilConjectures.IntegralHom.projection WeilConjectures.IntegralHom.evaluate

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
  (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

variable (wE : DualizingDatum l X D hl E) (wL : DualizingDatum l X D hl L)

/-- Simultaneous signed presentations make scalar extension commute with the actual
bidual map and the evaluation-defined finite reduction maps. This asserts the three
compatibility squares, without invertibility or coefficient unit/composition equations.
Source: current blueprint lem-coef-integral-finite-extension.proof.md, paragraphs 5-7
(blueprint: lem-sf-integral-finite-extension-reduction-pairing).

Proof: use the normalized signed tensor-Hom presentations simultaneously over the
two completed rings and every finite quotient. The Koszul swaps and currying on
K-flat/K-injective representatives give first-variable evaluation naturality. The
scalar tensorator multiplies coefficient factors; it respects these swaps because
the coefficients have degree zero. Transpose the scalar-extended evaluation pairing
in each tensor input. Both transposes are the displayed double-dual composites,
which therefore agree by the tensor-Hom bijection. For reduction, tensor the same
evaluation representative with each quotient. Balancing identifies its transpose
with finite homMap, conjugated by the specified quotient isomorphisms. This is the
v square at every exponent, including those between ramification multiples.
Postcomposition with the counit-defined finite dualizing map gives the beta square:
use u_reduction and naturality of internal Hom in its second argument. All maps
are obtained on the same simultaneous representatives before localization; equality
is not inferred solely from equality of finite evaluations. Zero inputs, identity
extensions, the residue level and empty X use the same formulas.
The finite target presentations are also assumed natural in the first variable
(signedCalculus supplies this); otherwise their adjunctions are free off K-flat
complexes and the finite comparison squares could change sign. -/
theorem reductionPairing
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (sE : IntegralVerdier.SignedSymmetry X _ a)
    (sL : IntegralVerdier.SignedSymmetry X _ b)
    (mE : ∀ n : ℕ, IntegralHom.ReductionPresentation l E X D hl a n)
    (mL : ∀ n : ℕ, IntegralHom.ReductionPresentation l L X D hl b n)
    (hnatE : ∀ (K M K' M' : IntegralVerdier.Ambient l E X)
      (f : K ⟶ K') (g : M ⟶ M'),
      a.tensor.map (Prod.mkHom f g) ≫ (sE.swap K' M').hom =
        (sE.swap K M).hom ≫ a.tensor.map (Prod.mkHom g f))
    (hnatL : ∀ (K M K' M' : IntegralVerdier.Ambient l L X)
      (f : K ⟶ K') (g : M ⟶ M'),
      b.tensor.map (Prod.mkHom f g) ≫ (sL.swap K' M').hom =
        (sL.swap K M).hom ≫ b.tensor.map (Prod.mkHom g f))
    (hevalE : ∀ (K K' M : IntegralVerdier.Ambient l E X) (f : K' ⟶ K),
      a.tensor.map (Prod.mkHom (𝟙 K')
          ((IntegralHom.hom.{u, u} X
            (completedIntegralCommRingSheafUnrestricted l E X)).map
            (Prod.mkHom f.op (𝟙 M)))) ≫ (a.adjunction K').counit.app M =
        a.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (a.adjunction K).counit.app M)
    (hevalL : ∀ (K K' M : IntegralVerdier.Ambient l L X) (f : K' ⟶ K),
      b.tensor.map (Prod.mkHom (𝟙 K')
          ((IntegralHom.hom.{u, u} X
            (completedIntegralCommRingSheafUnrestricted l L X)).map
            (Prod.mkHom f.op (𝟙 M)))) ≫ (b.adjunction K').counit.app M =
        b.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (b.adjunction K).counit.app M)
    (hfinE : ∀ (n : ℕ) (K K' W : DerivedCategory (scalarReductionTarget l E X n))
      (f : K' ⟶ K),
      (mE n).target.tensor.map (Prod.mkHom (𝟙 K')
        ((IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l E X n)).map
          (Prod.mkHom f.op (𝟙 W)))) ≫ ((mE n).target.adjunction K').counit.app W =
      (mE n).target.tensor.map (Prod.mkHom f (𝟙 _)) ≫
        ((mE n).target.adjunction K).counit.app W)
    (hfinL : ∀ (n : ℕ) (K K' W : DerivedCategory (scalarReductionTarget l L X n))
      (f : K' ⟶ K),
      (mL n).target.tensor.map (Prod.mkHom (𝟙 K')
        ((IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l L X n)).map
          (Prod.mkHom f.op (𝟙 W)))) ≫ ((mL n).target.adjunction K').counit.app W =
      (mL n).target.tensor.map (Prod.mkHom f (𝟙 _)) ≫
        ((mL n).target.adjunction K).counit.app W) :
    let T := integralScalarExtensionOfUniverses l E L ι X
    let HE := IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l E X)
    let DE := IntegralVerdier.dual l E X wE.omega.obj
    let DL := IntegralVerdier.dual l L X wL.omega.obj
    (∀ K : sfIntegralConstructibleCategory l E X,
      IntegralVerdier.delta X b sL wL.omega.obj (T.obj K.obj) ≫
          DL.map (beta l E L ι X D hl wE wL a b K.obj K.property.1).op =
        T.map (IntegralVerdier.delta X a sE wE.omega.obj K.obj) ≫
          beta l E L ι X D hl wE wL a b (DE.obj (op K.obj))
            (scalarInternalHom_complete l E X K.obj wE.omega.obj wE.omega.property.1)) ∧
    (∀ (n : ℕ) (K M : sfIntegralConstructibleCategory l E X),
      let rE := scalarReductionDerivedExtension l E X n
      let rL := scalarReductionDerivedExtension l L X n
      let F := pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)
      let Hn := IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l L X n)
      rL.map (v l E L ι X a b K.obj M.obj K.property.1 M.property.1) ≫
          IntegralHom.comparison l L X D hl (mL n) (T.obj K.obj) (T.obj M.obj) =
        (quotient l E L ι X n (HE.obj (op K.obj, M.obj))
          (scalarInternalHom_complete l E X K.obj M.obj M.property.1)).hom ≫
          F.map (IntegralHom.comparison l E X D hl (mE n) K.obj M.obj) ≫
          homMap X (integralScalarQuotientSheafMap l E L ι X n)
            (mE n).target (mL n).target (rE.obj K.obj) (rE.obj M.obj) ≫
          Hn.map (Prod.mkHom (quotient l E L ι X n K.obj K.property.1).hom.op
            (quotient l E L ι X n M.obj M.property.1).inv)) ∧
    (∀ (n : ℕ) (K : sfIntegralConstructibleCategory l E X),
      let rE := scalarReductionDerivedExtension l E X n
      let rL := scalarReductionDerivedExtension l L X n
      let F := pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)
      let Hn := IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l L X n)
      rL.map (beta l E L ι X D hl wE wL a b K.obj K.property.1) ≫
          IntegralVerdier.comparison l L X D hl (mL n) wL.omega wL.reduction (T.obj K.obj) =
        (quotient l E L ι X n (DE.obj (op K.obj))
          (scalarInternalHom_complete l E X K.obj wE.omega.obj wE.omega.property.1)).hom ≫
          F.map (IntegralVerdier.comparison l E X D hl (mE n) wE.omega wE.reduction K.obj) ≫
          homMap X (integralScalarQuotientSheafMap l E L ι X n)
            (mE n).target (mL n).target (rE.obj K.obj) (integralDualizingFiniteTerm l E D X n) ≫
          Hn.map (Prod.mkHom (quotient l E L ι X n K.obj K.property.1).hom.op
            (finiteU l E L ι X D n))) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · exact CoefIntegralFiniteExtensionDeltaSquare l E L ι X D hl wE wL a b sE sL mE mL
      hnatE hnatL hevalE hevalL hfinE hfinL
  · exact CoefIntegralFiniteExtensionHomReductionSquare l E L ι X D hl wE wL a b sE sL mE mL
      hnatE hnatL hevalE hevalL hfinE hfinL
  · exact CoefIntegralFiniteExtensionBetaReductionSquare l E L ι X D hl wE wL a b sE sL mE mL
      hnatE hnatL hevalE hevalL hfinE hfinL

end WeilConjectures.IntegralFiniteExtension
