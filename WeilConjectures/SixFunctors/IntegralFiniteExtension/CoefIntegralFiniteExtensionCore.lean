/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionModels
import WeilConjectures.SixFunctors.Integral.IntegralConstructibleReductionHom
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteDualizingCoherence
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructibleIntrinsic

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

/-- The finite-counit characterization determines the integral dualizing map uniquely.
Source: blueprint order 2494, second and third paragraphs
(blueprint: lem-coef-integral-finite-extension).
Proof: use finiteEtaleU at every target level, including the intermediate ramified
quotients. The counit composition equations make these a coherent system. Realize
it in the coefficient sequence category and take its total derived limit. The
normalized reduction counits give exactly the displayed squares. For uniqueness,
apply the coherent reduction/limit adjunction; the constructible mapping groups at
finite levels are finite, hence the inverse system is Mittag-Leffler and its lim-one
term vanishes. Thus equality of all these reductions determines the map. -/
theorem u_existsUnique :
    ∃! f : (integralScalarExtensionOfUniverses l E L ι X).obj wE.omega.obj ⟶ wL.omega.obj,
      ∀ n : ℕ,
        (scalarReductionDerivedExtension l L X n).map f ≫ (wL.reduction n).hom =
          (quotient l E L ι X n wE.omega.obj wE.omega.property.1).hom ≫
            (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)).map
              (wE.reduction n).hom ≫ finiteU l E L ι X D n := by
  let f := fun n : ℕ ↦
    (quotient l E L ι X n wE.omega.obj wE.omega.property.1).hom ≫
      (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)).map
        (wE.reduction n).hom ≫ finiteU l E L ι X D n ≫ (wL.reduction n).inv
  let K : sfIntegralConstructibleCategory l L X :=
    ⟨(integralScalarExtensionOfUniverses l E L ι X).obj wE.omega.obj,
      sfIntegralScalarExtension_constructible D.p l hl E L ι X
        wE.omega.obj wE.omega.property⟩
  obtain ⟨g, hg, huniq⟩ := integralConstructibleReductionHom D l hl L X K wL.omega f
    (finiteDualizing_reduction_coherent l E L ι X D hl wE wL)
  refine ⟨g, ?_, ?_⟩
  · intro n
    rw [hg n]
    simp only [f, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · intro g' hg'
    apply huniq g'
    intro n
    apply (cancel_mono (wL.reduction n).hom).1
    rw [hg' n]
    simp only [f, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The canonical u, chosen from a theorem determining the actual morphism uniquely.
Source: blueprint order 2494 (blueprint: lem-coef-integral-finite-extension). -/
def u : (integralScalarExtensionOfUniverses l E L ι X).obj wE.omega.obj ⟶ wL.omega.obj :=
  (u_existsUnique l E L ι X D hl wE wL).exists.choose

/-- Beta is v followed by RHom(TK,u); it is not independent comparison data.
Source: blueprint order 2494, third displayed comparison
(blueprint: lem-coef-integral-finite-extension). -/
def beta (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (K : IntegralVerdier.Ambient l E X) (hK : IsSfDerivedComplete l E X K) :
    (integralScalarExtensionOfUniverses l E L ι X).obj
        ((IntegralVerdier.dual l E X wE.omega.obj).obj (op K)) ⟶
      (IntegralVerdier.dual l L X wL.omega.obj).obj
        (op ((integralScalarExtensionOfUniverses l E L ι X).obj K)) :=
  v l E L ι X a b K wE.omega.obj hK wE.omega.property.1 ≫
    (IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l L X)).map
      (Prod.mkHom (𝟙 _) (u l E L ι X D hl wE wL))

/-- The identity-extension comparison is multiplication, conjugated by completion.
Source: blueprint order 2494, last paragraph
(blueprint: lem-coef-integral-finite-extension). -/
def unit (K : IntegralVerdier.Ambient l E X) (hK : IsSfDerivedComplete l E X K) :
    (integralScalarExtensionOfUniverses l E E (AlgHom.id (Padic l) E) X).obj K ≅ K :=
  (completion l E E (AlgHom.id (Padic l) E) X K hK).symm ≪≫
    (eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ)
      (PurCompactSupport.completedMap_identity l E X))).app K ≪≫
    (PurCompactSupport.tensorIdentity
      (completedIntegralCommRingSheafUnrestricted l E X)).app K

/-- The tensor associator, conjugated by the three specified completion comparisons.
Source: blueprint order 2494, last paragraph
(blueprint: lem-coef-integral-finite-extension). -/
def comp (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (j : L →ₐ[Padic l] F) (K : IntegralVerdier.Ambient l E X)
    (hK : IsSfDerivedComplete l E X K) :
    (integralScalarExtensionOfUniverses l L F j X).obj
        ((integralScalarExtensionOfUniverses l E L ι X).obj K) ≅
      (integralScalarExtensionOfUniverses l E F (j.comp ι) X).obj K :=
  (completion l L F j X _ (extension_complete l E L ι X K hK)).symm ≪≫
    (pbcDerivedExtend (completedCoefficientMap l L F j X)).mapIso
      (completion l E L ι X K hK).symm ≪≫
    (PurCompactSupport.tensorComposition (completedCoefficientMap l E L ι X)
      (completedCoefficientMap l L F j X) (completedCoefficientMap l E F (j.comp ι) X)
      (PurCompactSupport.completedMap_composition l E L ι F j X)).app K ≪≫
    completion l E F (j.comp ι) X K hK

/-- Scalar-extended evaluation, with all three completion comparisons displayed.
Source: blueprint order 2494, evaluation clause
(blueprint: lem-coef-integral-finite-extension). -/
def extendedEvaluation
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (K M : IntegralVerdier.Ambient l E X)
    (hK : IsSfDerivedComplete l E X K) (hM : IsSfDerivedComplete l E X M) :
    b.tensor.obj ((integralScalarExtensionOfUniverses l E L ι X).obj K,
      (integralScalarExtensionOfUniverses l E L ι X).obj
        ((IntegralHom.hom.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l E X)).obj (op K, M))) ⟶
      (integralScalarExtensionOfUniverses l E L ι X).obj M :=
  b.tensor.map (Prod.mkHom (completion l E L ι X K hK).inv
      (completion l E L ι X _ (scalarInternalHom_complete l E X K M hM)).inv) ≫
    (PurCompactSupport.scalarTensor (completedCoefficientMap l E L ι X)
      (tensorModel X a) (tensorModel X b)).inv.app
        (K, (IntegralHom.hom.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l E X)).obj (op K, M)) ≫
    (pbcDerivedExtend (completedCoefficientMap l E L ι X)).map
      ((a.adjunction K).counit.app M) ≫ (completion l E L ι X M hM).hom

/-- The single-extension assertions, including equations for the actual evaluation,
double dual and all three finite reductions. All Hom isomorphism assertions have
constructible inputs. Tensor presentations retain their representative normalizations.
Source: blueprint order 2494 (blueprint: lem-coef-integral-finite-extension). -/
def Conclusion
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (sE : IntegralVerdier.SignedSymmetry X _ a)
    (sL : IntegralVerdier.SignedSymmetry X _ b)
    (mE : ∀ n : ℕ, IntegralHom.ReductionPresentation l E X D hl a n)
    (mL : ∀ n : ℕ, IntegralHom.ReductionPresentation l L X D hl b n) : Prop :=
  let T := integralScalarExtensionOfUniverses l E L ι X
  let HE := IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l E X)
  let DE := IntegralVerdier.dual l E X wE.omega.obj
  let DL := IntegralVerdier.dual l L X wL.omega.obj
  (∃ (_ : T.CommShift ℤ), T.IsTriangulated) ∧
  (∀ K : sfIntegralConstructibleCategory l E X, sfIntegralConstructible l L X (T.obj K.obj)) ∧
  IsIso (u l E L ι X D hl wE wL) ∧
  (∀ K M : sfIntegralConstructibleCategory l E X,
    IsIso (v l E L ι X a b K.obj M.obj K.property.1 M.property.1)) ∧
  (∀ K : sfIntegralConstructibleCategory l E X,
    IsIso (beta l E L ι X D hl wE wL a b K.obj K.property.1)) ∧
  (∀ K M : sfIntegralConstructibleCategory l E X,
    b.tensor.map (Prod.mkHom (𝟙 (T.obj K.obj))
        (v l E L ι X a b K.obj M.obj K.property.1 M.property.1)) ≫
        (b.adjunction (T.obj K.obj)).counit.app (T.obj M.obj) =
      extendedEvaluation l E L ι X a b K.obj M.obj K.property.1 M.property.1) ∧
  (∀ K : sfIntegralConstructibleCategory l E X,
    b.tensor.map (Prod.mkHom (𝟙 (T.obj K.obj))
        (beta l E L ι X D hl wE wL a b K.obj K.property.1)) ≫
        (b.adjunction (T.obj K.obj)).counit.app wL.omega.obj =
      extendedEvaluation l E L ι X a b K.obj wE.omega.obj
        K.property.1 wE.omega.property.1 ≫ u l E L ι X D hl wE wL) ∧
  (∀ K : sfIntegralConstructibleCategory l E X,
    IntegralVerdier.delta X b sL wL.omega.obj (T.obj K.obj) ≫
        DL.map (beta l E L ι X D hl wE wL a b K.obj K.property.1).op =
      T.map (IntegralVerdier.delta X a sE wE.omega.obj K.obj) ≫
        beta l E L ι X D hl wE wL a b (DE.obj (op K.obj))
          (scalarInternalHom_complete l E X K.obj wE.omega.obj wE.omega.property.1)) ∧
  (∀ n : ℕ,
    (scalarReductionDerivedExtension l L X n).map (u l E L ι X D hl wE wL) ≫
        (wL.reduction n).hom =
      (quotient l E L ι X n wE.omega.obj wE.omega.property.1).hom ≫
        (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)).map
          (wE.reduction n).hom ≫ finiteU l E L ι X D n) ∧
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
          (finiteU l E L ι X D n)))

/-- The three identity-extension equations use the specified multiplication unit.
Source: blueprint order 2494, identity-extension clause
(blueprint: lem-coef-integral-finite-extension). -/
def IdentityConclusion
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X)) : Prop :=
  let H := IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l E X)
  let DE := IntegralVerdier.dual l E X wE.omega.obj
  u l E E (AlgHom.id (Padic l) E) X D hl wE wE =
      (unit l E X wE.omega.obj wE.omega.property.1).hom ∧
  (∀ K M : sfIntegralConstructibleCategory l E X,
    v l E E (AlgHom.id (Padic l) E) X a a K.obj M.obj K.property.1 M.property.1 ≫
        H.map (Prod.mkHom (unit l E X K.obj K.property.1).inv.op
          (unit l E X M.obj M.property.1).hom) =
      (unit l E X (H.obj (op K.obj, M.obj))
        (scalarInternalHom_complete l E X K.obj M.obj M.property.1)).hom) ∧
  (∀ K : sfIntegralConstructibleCategory l E X,
    beta l E E (AlgHom.id (Padic l) E) X D hl wE wE a a K.obj K.property.1 ≫
        DE.map (unit l E X K.obj K.property.1).inv.op =
      (unit l E X (DE.obj (op K.obj))
        (scalarInternalHom_complete l E X K.obj wE.omega.obj wE.omega.property.1)).hom)

/-- Composition of u, v and beta, with the actual tensor associator at every endpoint.
The final clause is the associator pentagon on the unchanged ambient morphisms.
Source: blueprint order 2494, composition clause
(blueprint: lem-coef-integral-finite-extension). -/
def CompositionConclusion
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (j : L →ₐ[Padic l] F) (wF : DualizingDatum l X D hl F)
    (c : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l F X)) : Prop :=
  let T := integralScalarExtensionOfUniverses l E L ι X
  let U := integralScalarExtensionOfUniverses l L F j X
  let HE := IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l E X)
  let HF := IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l F X)
  let DE := IntegralVerdier.dual l E X wE.omega.obj
  let DF := IntegralVerdier.dual l F X wF.omega.obj
  (∀ K : sfIntegralConstructibleCategory l E X,
    (comp l E E (AlgHom.id (Padic l) E) X L ι K.obj K.property.1).hom =
      T.map (unit l E X K.obj K.property.1).hom) ∧
  (∀ K : sfIntegralConstructibleCategory l E X,
    (comp l E L ι X L (AlgHom.id (Padic l) L) K.obj K.property.1).hom =
      (unit l L X (T.obj K.obj)
        (extension_complete l E L ι X K.obj K.property.1)).hom) ∧
  U.map (u l E L ι X D hl wE wL) ≫ u l L F j X D hl wL wF =
      (comp l E L ι X F j wE.omega.obj wE.omega.property.1).hom ≫
        u l E F (j.comp ι) X D hl wE wF ∧
  (∀ K M : sfIntegralConstructibleCategory l E X,
    U.map (v l E L ι X a b K.obj M.obj K.property.1 M.property.1) ≫
        v l L F j X b c (T.obj K.obj) (T.obj M.obj)
          (extension_complete l E L ι X K.obj K.property.1)
          (extension_complete l E L ι X M.obj M.property.1) ≫
        HF.map (Prod.mkHom (comp l E L ι X F j K.obj K.property.1).inv.op
          (comp l E L ι X F j M.obj M.property.1).hom) =
      (comp l E L ι X F j (HE.obj (op K.obj, M.obj))
        (scalarInternalHom_complete l E X K.obj M.obj M.property.1)).hom ≫
        v l E F (j.comp ι) X a c K.obj M.obj K.property.1 M.property.1) ∧
  (∀ K : sfIntegralConstructibleCategory l E X,
    U.map (beta l E L ι X D hl wE wL a b K.obj K.property.1) ≫
        beta l L F j X D hl wL wF b c (T.obj K.obj)
          (extension_complete l E L ι X K.obj K.property.1) ≫
        DF.map (comp l E L ι X F j K.obj K.property.1).inv.op =
      (comp l E L ι X F j (DE.obj (op K.obj))
        (scalarInternalHom_complete l E X K.obj wE.omega.obj wE.omega.property.1)).hom ≫
        beta l E F (j.comp ι) X D hl wE wF a c K.obj K.property.1) ∧
  (∀ (G : Type u) [Field G] [Algebra (Padic l) G] [FiniteDimensional (Padic l) G]
    (k : F →ₐ[Padic l] G) (K : sfIntegralConstructibleCategory l E X),
    (integralScalarExtensionOfUniverses l F G k X).map
        (comp l E L ι X F j K.obj K.property.1).hom ≫
        (comp l E F (j.comp ι) X G k K.obj K.property.1).hom =
      (comp l L F j X G k (T.obj K.obj)
        (extension_complete l E L ι X K.obj K.property.1)).hom ≫
        (comp l E L ι X G (k.comp j) K.obj K.property.1).hom)

/-- The canonical map has precisely the prescribed finite counit reductions.
Source: blueprint finite dualizing comparison (blueprint: lem-coef-integral-finite-extension). -/
theorem u_reduction (n : ℕ) :
    (scalarReductionDerivedExtension l L X n).map (u l E L ι X D hl wE wL) ≫
        (wL.reduction n).hom =
      (quotient l E L ι X n wE.omega.obj wE.omega.property.1).hom ≫
        (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)).map
          (wE.reduction n).hom ≫ finiteU l E L ι X D n := by
  exact (u_existsUnique l E L ι X D hl wE wL).exists.choose_spec n

end WeilConjectures.IntegralFiniteExtension
