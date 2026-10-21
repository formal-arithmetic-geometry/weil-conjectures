module

public import Sheaf.SixFunctors.IntegralVerdier
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison

import Sheaf.Paper.IntegralConstructibleInternalHom
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import Sheaf.Paper.SfIntegralConstructible
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.Paper.SfDerivedComplete
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
import Sheaf.SixFunctors.FiniteDualizing
import Sheaf.Paper.IntegralResidueTor
import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
import Sheaf.Paper.FiniteFieldFiber
import Sheaf.Paper.FiniteTorAmplitude
import Sheaf.Paper.NormalizedDVREffectivity
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.Paper.CoefficientRingedTensorHomModel
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.SixFunctors.IntegralDualizing
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Paper.FiniteCoefficientHomChange
import Sheaf.Paper.SemilinearDerivedSections
import Sheaf.Paper.FiniteFreeCoefficientExtension

/-! # Integral duality under finite coefficient extension

Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower, order 2494
(blueprint: lem-coef-integral-finite-extension).

All comparisons below are fixed before invertibility is asserted. Finite dualizing
maps are counit transposes. Internal-Hom maps are evaluation transposes, and the
integral dualizing map is characterized by the coherent finite counit squares.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.IntegralFiniteExtension

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (X : Scheme.{u})

/-- The existing tensor presentation restricted to flat-term K-flat representatives.
Source: blueprint order 2494, tensor calculation
(blueprint: lem-coef-integral-finite-extension). -/
def tensorModel {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : IntegralHom.TensorPresentation.{u, u} X R) : ProEtaleTensorModel X R where
  tensor := a.tensor
  representative := Functor.isoWhiskerLeft
    (((IntegralHom.flat.{u, u} X R).lift (proEtaleFlatRepresentatives X R).ι
      (fun P ↦ P.property.1)).prod
      ((IntegralHom.flat.{u, u} X R).lift (proEtaleFlatRepresentatives X R).ι
        (fun P ↦ P.property.1))) a.representative

/-- The actual evaluation transpose for an arbitrary change of coefficient sheaves.
Source: blueprint order 2494, internal-Hom comparison
(blueprint: lem-coef-integral-finite-extension). -/
def homMap {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (a : IntegralHom.TensorPresentation.{u, u} X R)
    (b : IntegralHom.TensorPresentation.{u, u} X S)
    (K M : IntegralHom.Derived.{u, u} X R) :
    (pbcDerivedExtend φ).obj ((IntegralHom.hom.{u, u} X R).obj (op K, M)) ⟶
      (IntegralHom.hom.{u, u} X S).obj
        (op ((pbcDerivedExtend φ).obj K), (pbcDerivedExtend φ).obj M) :=
  (b.adjunction ((pbcDerivedExtend φ).obj K)).homEquiv _ _
    ((PurCompactSupport.scalarTensor φ (tensorModel X a) (tensorModel X b)).inv.app
        (K, (IntegralHom.hom.{u, u} X R).obj (op K, M)) ≫
      (pbcDerivedExtend φ).map ((a.adjunction K).counit.app M))

/-- Completeness in the intrinsic category makes the specified completion map invertible.
Source: blueprint order 2494, first paragraph
(blueprint: lem-coef-integral-finite-extension).
Proof: compare the intrinsic Roos completeness unit with the unrestricted one on a
flat-term K-flat resolution. Both have quotient components x ↦ 1 tensor x and zero
shifted coordinate. The finite-free completed-scalar comparison applies to this
same unit; hence its localized map is invertible. -/
theorem completion_isIso (K : IntegralVerdier.Ambient l E X)
    (hK : IsSfDerivedComplete l E X K) :
    IsIso ((completedScalarComparison l E L ι X).app K) := by
  sorry

/-- The fixed completion comparison on a complete input.
Source: blueprint order 2494 (blueprint: lem-coef-integral-finite-extension). -/
def completion (K : IntegralVerdier.Ambient l E X)
    (hK : IsSfDerivedComplete l E X K) :
    (pbcDerivedExtend (completedCoefficientMap l E L ι X)).obj K ≅
      (integralScalarExtensionOfUniverses l E L ι X).obj K :=
  letI := completion_isIso l E L ι X K hK
  asIso ((completedScalarComparison l E L ι X).app K)

/-- The canonical tensor/restriction identification of a finite reduction of T.
Source: blueprint order 2494, displayed quotient identification
(blueprint: lem-coef-integral-finite-extension). -/
def quotient (n : ℕ) (K : IntegralVerdier.Ambient l E X)
    (hK : IsSfDerivedComplete l E X K) :
    (scalarReductionDerivedExtension l L X n).obj
        ((integralScalarExtensionOfUniverses l E L ι X).obj K) ≅
      (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)).obj
        ((scalarReductionDerivedExtension l E X n).obj K) :=
  (scalarReductionDerivedExtension l L X n).mapIso (completion l E L ι X K hK).symm ≪≫
    (PurCompactSupport.finiteReductionIso l L X n).symm.app _ ≪≫
    (PurCompactSupport.tensorSquare (completedCoefficientMap l E L ι X)
      (integralScalarQuotientSheafMap l E L ι X n)
      (completedIntegralCommRingProjectionUnrestricted l E X n)
      (completedIntegralCommRingProjectionUnrestricted l L X n)
      ((completedCoefficientMap_existsUnique l E L ι X).exists.choose_spec n)).app K ≪≫
    (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)).mapIso
      ((PurCompactSupport.finiteReductionIso l E X n).app K)

/-- The canonical v: scalar-extended evaluation, transported through completion.
Source: blueprint order 2494, fourth paragraph
(blueprint: lem-coef-integral-finite-extension). -/
def v (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (K M : IntegralVerdier.Ambient l E X)
    (hK : IsSfDerivedComplete l E X K) (hM : IsSfDerivedComplete l E X M) :
    (integralScalarExtensionOfUniverses l E L ι X).obj
        ((IntegralHom.hom.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l E X)).obj (op K, M)) ⟶
      (IntegralHom.hom.{u, u} X
        (completedIntegralCommRingSheafUnrestricted l L X)).obj
        (op ((integralScalarExtensionOfUniverses l E L ι X).obj K),
          (integralScalarExtensionOfUniverses l E L ι X).obj M) :=
  (completion l E L ι X _ (scalarInternalHom_complete l E X K M hM)).inv ≫
    homMap X (completedCoefficientMap l E L ι X) a b K M ≫
    (IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l L X)).map
      (Prod.mkHom (completion l E L ι X K hK).inv.op
        (completion l E L ι X M hM).hom)

/-- Cross-field restriction commutes with the prescribed comparison-site realization.
Source: blueprint order 2494, finite counit comparisons
(blueprint: lem-coef-integral-finite-extension). -/
def finiteRealizationRestriction (n : ℕ) :
    finiteDualizingRealization l L X n ⋙
        pbcDerivedRestrict (integralScalarQuotientSheafMap l E L ι X n) ≅
      Sheaf.derivedRestrictScalars X.smallEtaleTopology
        (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n)) ⋙
        finiteDualizingRealization l E X n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (finiteDualizingGenericDerivedRestriction X
      (integralScalarQuotientMap l E L ι n)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (ProEtale.pbcDerivedComparisonRestrict X
        (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n))) _ ≪≫
    Functor.associator _ _ _

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The finite cross-field dualizing map is the exceptional-adjunction transpose of
inverse compact-support comparison followed by extension of the counit and the unit.
Source: blueprint order 2494, second paragraph
(blueprint: lem-coef-integral-finite-extension). -/
def finiteEtaleU (n : ℕ) :
    (Etale.scalarExtension
      (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n)) X).obj
        (finiteDualizingEtaleTerm l E D X n) ⟶ finiteDualizingEtaleTerm l L D X n :=
  (finiteDualizingEtaleAdjunction l L D X n).homEquiv _ _
    (Etale.ExceptionalCoefficients.comparisonInverse
        (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n))
        (finiteDualizingCompactification D X) (finiteDualizingEtaleTerm l E D X n) ≫
      (Etale.scalarExtension
        (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n))
        (Spec (.of D.k))).map (finiteDualizingEtaleCounit l E D X n) ≫
      (Etale.ExceptionalCoefficients.unitIso
        (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n))
        (Spec (.of D.k))).hom)

/-- Intrinsic finite u, transported by the scalar-unit-normalized realization square.
Source: blueprint order 2494, second paragraph
(blueprint: lem-coef-integral-finite-extension). -/
def finiteU (n : ℕ) :
    (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)).obj
        (integralDualizingFiniteTerm l E D X n) ⟶ integralDualizingFiniteTerm l L D X n :=
  ((pbcDerivedScalarAdjunction (integralScalarQuotientSheafMap l E L ι X n)).homEquiv
    _ _).symm
      ((finiteDualizingOrigin l E D X n).inv ≫
        (finiteDualizingRealization l E X n).map
          ((Adjunction.ofIsRightAdjoint
            (Sheaf.derivedRestrictScalars X.smallEtaleTopology
              (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n)))).homEquiv
                _ _ (finiteEtaleU l E L ι X D n)) ≫
        (finiteRealizationRestriction l E L ι X n).inv.app
          (finiteDualizingEtaleTerm l L D X n) ≫
        (pbcDerivedRestrict (integralScalarQuotientSheafMap l E L ι X n)).map
          (finiteDualizingOrigin l L D X n).hom)

/-- A presentation of the integral dualizing object with its coherent finite counits.
Coherence is essential: unrelated finite isomorphisms are not dualizing reduction data.
These are the reduction data provided by prop-coef-integral-dualizing.
Source: blueprint order 2494, second paragraph
(blueprint: lem-coef-integral-finite-extension). -/
structure DualizingDatum (F : Type u) [Field F] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) F] where
  omega : sfIntegralConstructibleCategory l F X
  reduction : ∀ n : ℕ,
    (scalarReductionDerivedExtension l F X n).obj omega.obj ≅
      integralDualizingFiniteTerm l F D X n
  coherent : ∀ {m n : ℕ} (h : n ≤ m),
    normalizedDVRReductionTransition l F X D hl h omega.obj ≫
        (normalizedDVRRes l F X h).map (reduction n).hom =
      (reduction m).hom ≫ integralDualizingExceptionalTransition l F D X hl h

/-- The coherent presentations required here exist, with the actual finite counits.
Source: blueprint order 2494, second paragraph
(blueprint: lem-coef-integral-finite-extension).
Proof: choose a dimension bound for the finite-type scheme, then apply the integral
 dualizing proposition. Compose its normalized DVR counit comparisons with its
coherent finite-term origins. Their transition equation is precisely coherent. -/
theorem dualizingDatum_nonempty (F : Type u) [Field F] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) F] : Nonempty (DualizingDatum l X D hl F) := by
  sorry

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
  sorry

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

/-- Completed finite-free extension preserves completeness on all complete inputs.
Source: blueprint order 2494, first paragraph
(blueprint: lem-coef-integral-finite-extension).
Proof: on a flat-term K-flat representative the finite-free basis commutes with
products in the Roos complex. Cofinality of uniformizer powers identifies its
completion unit with the target completion unit, so the latter is invertible. -/
theorem extension_complete (K : IntegralVerdier.Ambient l E X)
    (hK : IsSfDerivedComplete l E X K) : IsSfDerivedComplete l L X
      ((integralScalarExtensionOfUniverses l E L ι X).obj K) := by
  sorry

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

end WeilConjectures.IntegralFiniteExtension

namespace WeilConjectures
open IntegralFiniteExtension

/-- The canonical integral coefficient comparisons and all their normalization equations.
Source: current blueprint sec-smooth-purity/sk-lem-sp-tower, order 2494
(blueprint: lem-coef-integral-finite-extension).
Proof:
1. Finite freeness identifies strict completed extension with ordinary derived tensor
on complete inputs. Ordinary tensor and the Roos completion are triangulated. The
normalized finite quotient calculations preserve the uniform constructible bounds.
2. Construct the finite maps by transposing the compact-support counit comparisons.
Their identity and quotient composition equations give a coherent map on the full
S-tower, including levels between the ramification-multiple exponents. Take its
total limit and use the normalized counits. This gives the map u defined above,
not an arbitrary isomorphism; all its finite reductions are isomorphisms.
3. Finite freeness computes the evaluation transpose on a K-injective representative
as the finite-basis Hom identity. Completion gives precisely v. It is invertible
for constructible inputs. Composing with RHom(TK,u) gives beta and its invertibility.
4. Transpose the scalar-extended evaluation equation under the tensor-Hom adjunction.
The signed symmetry defines the actual delta; its transpose is evaluation, so the
same equation gives the displayed double-dual square. The coefficient tensor
associators identify these transposes after each finite reduction. Together with
the finite counit squares for u this gives all three quotient equations.
5. On local pure tensors, identity extension is multiplication and iterated extension
sends c tensor (b tensor x) to c*j(b) tensor x. These formulas give all three unit
and composition equations. Three successive extensions multiply coefficients in
the same order, proving the associator pentagon. The normalized completion maps
cancel in the intermediate positions. Localization and coherent total limit
preserve these equations. This includes identity fields, zero objects and empty X. -/
theorem coef_integral_finite_extension
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    (wE : DualizingDatum l X D hl E) (wL : DualizingDatum l X D hl L) :
    ∃ (a : IntegralHom.TensorPresentation.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l E X))
      (b : IntegralHom.TensorPresentation.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l L X))
      (sE : IntegralVerdier.SignedSymmetry X _ a)
      (sL : IntegralVerdier.SignedSymmetry X _ b)
      (mE : ∀ n : ℕ, IntegralHom.ReductionPresentation l E X D hl a n)
      (mL : ∀ n : ℕ, IntegralHom.ReductionPresentation l L X D hl b n),
      Conclusion l E L ι X D hl wE wL a b sE sL mE mL ∧
      IdentityConclusion l E X D hl wE a ∧ IdentityConclusion l L X D hl wL b ∧
      (∀ (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
        (j : L →ₐ[Padic l] F) (wF : DualizingDatum l X D hl F)
        (c : IntegralHom.TensorPresentation.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l F X)),
        CompositionConclusion l E L ι X D hl wE wL a b F j wF c) := by
  sorry

end WeilConjectures
