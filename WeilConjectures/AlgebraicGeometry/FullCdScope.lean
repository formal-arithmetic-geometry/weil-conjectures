/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.EllipticGenericFreeAction
public import WeilConjectures.CategoryTheory.Sites.EquivariantEvaluation
public import WeilConjectures.CategoryTheory.ConstantRingModuleSheaves
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.UnboundedCohomologyObstruction.DerivedUnboundedCohomologyObstruction
public import WeilConjectures.AlgebraicGeometry.Ambient.AmbientExceptionalRightAdjoint
public import WeilConjectures.SixFunctors.ProEtale.AmbientCounterexampleCoproducts
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Category.ModuleCat.Products
public import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Skeletal
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleOrigin
public import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginAdjointClass
public import WeilConjectures.AlgebraicGeometry.SfAffineChartPresentation.PurityAffineChartBounds
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExceptionalInverseImageCurrent
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkPropSfRfShriekPreservation
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.AlgebraicGeometry.LocallyConstantPerfectComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CtfLocallyClosedPerfectGeneration
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleTensorConstructibility
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import WeilConjectures.AlgebraicGeometry.SixFunctors.DualityPairing
public import WeilConjectures.Compactification.Dense
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedSiteComparison
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricBidualityInduction
public import WeilConjectures.CategoryTheory.Monoidal.Closed.EvaluationBidualComparisonTransport
public import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.SixFunctors.Etale.Derived.DoubleDual
public import WeilConjectures.AlgebraicGeometry.FiniteCondensedCtfEquivalence
public import WeilConjectures.CategoryTheory.FiniteCondensedNormalizedAdjunction
public import WeilConjectures.AlgebraicGeometry.FiniteNativeTensor.FiniteNativeTensorComparison
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
public import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexDual
public import Mathlib.CategoryTheory.Yoneda
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Triangulated.Opposite.OpOp
public import WeilConjectures.AlgebraicGeometry.Native.NativeDerivedHomSignedExact
public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteStageVerdierBiduality
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.ClosedTensorDualAdjunction
public import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
public import WeilConjectures.AlgebraicGeometry.EtaleModuleRingIsoAdjunction
public import WeilConjectures.AlgebraicGeometry.EtaleModuleInverseImageTransport
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedClosedKernelAdjoint
public import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
public import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
public import WeilConjectures.SixFunctors.OpenClosed.Conservative
public import WeilConjectures.SixFunctors.OpenClosed.Vanishing
public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedTensorProjection
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension
public import Mathlib.Data.ZMod.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.AlgebraicGeometry.Sf.SfOpenExceptionalBaseChange
import Mathlib.NumberTheory.Padics.RingHoms
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# The scope of the full cohomological-dimension counterexample

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-rem-sf-fullcd-scope.md,
"The counterexample and the repair boundary" and "Where the class adjoint stops".
(blueprint: sk-rem-sf-fullcd-scope)

The coefficient ring in the counterexample is an ordinary constant ring. The fixed-ring
module-valued sheaf presentation is the presentation of constant-ring module sheaves given
by `constant_ring_module_sheaves`; it does not replace a topological condensed ring by its
underlying discrete ring. The exact functors below are the existing evaluation and
coevaluation functors, and the sheaf is their actual value on the trivial representation.
The positive degrees are indexed by `n + 1` throughout.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Functor DirectSum

namespace AlgebraicGeometry.ProEtale

/-- The elliptic counterexample for every nonzero ordinary commutative ring.

Source: scope remark, counterexample paragraph and consequences (i)--(iii).
(blueprint: sk-rem-sf-fullcd-scope)

Proof:
1. Base change the elliptic curve from the finite field to its fixed algebraic closure.
   Apply `ellipticGenericFreeAction` to the multiplication-by-r tower. Its character and
   pro-r splitting give the countable free subgroup, injective under the character, acting
   freely on maps from the geometric generic point to affine weakly contractible objects.
2. Those objects cover the pro-etale site. Exact equivariant evaluation and its existing
   coevaluation therefore form an exact adjoint pair; evaluation is cocontinuous. The
   coevaluation section formula is equivariant functions, hence products over free orbits.
   The constant sheaf evaluates to the trivial representation. Set F = V(R).
3. Exact adjunction identifies Ext from the constant sheaf into F with Ext from the trivial
   H-module to itself. These are the ordinary abstract group cohomology modules H^n(H,R),
   nonzero for all positive n by the finite-rank retracts of the countable free group.
   Computing sections on an injective resolution identifies them with evaluated higher
   direct images. This uses no constructibility of F and only R nonzero.
4. Apply `UnboundedCohomologyObstruction.obstruction` to derived direct image and terminal
   evaluation on Spec k. Products of pro-etale module sheaves are exact; terminal evaluation
   is exact and cocontinuous. The sum of the shifts is their product. Its image comparison
   on evaluated H^0 is the nonsurjective inclusion of the direct sum into the product.
   Thus derived direct image fails to preserve countable coproducts and is no left adjoint.
5. Terminal evaluation has an exact right adjoint v. For any injective cogenerator J,
   v(J) is injective and the canonical injectiveHomMap is bijective. Each Hom module is
   nonzero. A right adjoint on D+ would contradict bounded-below orthogonality for large n.
6. For proper f, each compactification candidate is isomorphic to Rf_*; transport the
   coproduct and both adjoint obstructions along this isomorphism. A nonzero higher direct
   image in degree c+1 also contradicts FullCD for every c, already on the original base.
7. For finite invertible-exponent R, the etale-origin bound would force this unbounded
   cohomology to vanish, so F is not of etale origin. Over a field the regular module
   R is an injective cogenerator, giving the stated special case I = v(R).
-/
theorem fullCdScope_counterexample
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (E₀ : Over (Spec (.of D.k₀))) [GrpObj E₀] [IsAbelianVariety E₀]
    (_hDim : IsAbelianVariety.dim E₀ = 1)
    (r : ℕ) [Fact r.Prime] (_hrp : r ≠ D.p)
    (R : Type (u + 1)) [CommRing R] [Nontrivial R] :
    letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
    let E := D.geometricFiber E₀
    letI : GrpObj E :=
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).grpObjObj
    letI : IsAbelianVariety E :=
      IsAbelianVariety.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) E₀
    let H := Multiplicative (ULift.{u + 1} ℕ →₀ ℤ)
    let T := Scheme.ProEt.genericPointSep E.left
    let J := Scheme.ProEt.topology E.left
    letI : IsGrothendieckAbelian.{u + 1} (Sheaf J (ModuleCat.{u + 1} R)) :=
      inferInstance
    letI : IsGrothendieckAbelian.{u + 1}
        (Sheaf (Scheme.ProEt.topology (Spec (.of D.k))) (ModuleCat.{u + 1} R)) :=
      inferInstance
    letI : IsGrothendieckAbelian.{u + 1} (ModuleCat.{u + 1} R) := inferInstance
    letI : HasSheafify J (ModuleCat.{u + 1} R) :=
      GrothendieckTopology.hasSheafify_proEtTopology (ModuleCat.{u + 1} R) E.left
    letI : HasSheafify (Scheme.ProEt.topology (Spec (.of D.k))) (ModuleCat.{u + 1} R) :=
      GrothendieckTopology.hasSheafify_proEtTopology (ModuleCat.{u + 1} R) (Spec (.of D.k))
    letI : HasWeakSheafify J (ModuleCat.{u + 1} R) :=
      HasSheafify.isRightAdjoint
    letI : HasWeakSheafify (Scheme.ProEt.topology (Spec (.of D.k))) (ModuleCat.{u + 1} R) :=
      HasSheafify.isRightAdjoint
    letI : HasGlobalSectionsFunctor (Scheme.ProEt.topology (Spec (.of D.k)))
        (ModuleCat.{u + 1} R) :=
      hasGlobalSectionsFunctor_of_hasTerminal _ _
    let e := Sheaf.Γ.{u + 1, u, u + 2, u + 1}
      (Scheme.ProEt.topology (Spec (.of D.k))) (ModuleCat.{u + 1} R)
    letI := preservesEpimorphisms_sheafSections_of_iso (A := ModuleCat.{u + 1} R)
      (Iso.refl (Spec (.of D.k)))
    letI : e.PreservesEpimorphisms := Functor.PreservesEpimorphisms.of_iso
      (Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId _)).symm
    letI : e.PreservesHomology :=
      Functor.preservesHomology_of_preservesEpis_and_kernels e
    letI : PreservesFiniteColimits e := Functor.preservesFiniteColimits_of_preservesHomology e
    let Q := R((E.hom)_*[ModuleCat.{u + 1} R])
    let Qplus := R+((E.hom)_*[ModuleCat.{u + 1} R])
    IsAffine T.left ∧ J.IsWeaklyContractible.{u + 1} T ∧
    (∀ m : ℕ, IsFinite (𝟙 E ^ (r ^ m)).left ∧
      Etale (𝟙 E ^ (r ^ m)).left ∧ Surjective (𝟙 E ^ (r ^ m)).left) ∧
    ∃ (ρ : (SeparableClosure E.left.functionField ≃ₐ[E.left.functionField]
        SeparableClosure E.left.functionField) →*
          Multiplicative (IsAbelianVariety.tateModule r E))
      (b : IsAbelianVariety.tateModule r E ≃ₗ[ℤ_[r]] (Fin 2 → ℤ_[r]))
      (χ : (SeparableClosure E.left.functionField ≃ₐ[E.left.functionField]
        SeparableClosure E.left.functionField) →ₜ* Multiplicative ℤ_[r])
      (g : SeparableClosure E.left.functionField ≃ₐ[E.left.functionField]
        SeparableClosure E.left.functionField)
      (j : Multiplicative ℤ_[r] →ₜ*
        (SeparableClosure E.left.functionField ≃ₐ[E.left.functionField]
          SeparableClosure E.left.functionField))
      (φ : H →* (SeparableClosure E.left.functionField ≃ₐ[E.left.functionField]
        SeparableClosure E.left.functionField)),
      Continuous ρ ∧ Function.Surjective ρ ∧ Continuous b ∧ Continuous b.symm ∧
      (∀ σ, χ σ = Multiplicative.ofAdd (b (ρ σ).toAdd 0)) ∧
      (∃ x : ℕ → (ellipticGenericOver E ⟶ E),
        (∀ m, x m ≫ (𝟙 E ^ (r ^ m)) = Over.homMk T.hom rfl) ∧
        (∀ m, x (m + 1) ≫ (𝟙 E ^ r) = x m) ∧
        ∀ σ m,
          ((Over.map E.hom).map ((Scheme.ProEt.forget E.left).map
            (Scheme.ProEt.genericPointSepAut E.left σ))) ≫ x m =
            x m * (toUnit (ellipticGenericOver E) ≫
              inv (toUnit (Scheme.specAlgebraicClosure D.k)) ≫
              (((ρ σ).toAdd : ℕ → Additive (Scheme.specAlgebraicClosure D.k ⟶ E))
                m).toMul)) ∧
      Function.Surjective χ ∧ χ g = Multiplicative.ofAdd 1 ∧
      (∀ z, j z ∈ (Subgroup.zpowers g).topologicalClosure) ∧
      (∀ z, χ (j z) = z) ∧ (∀ h, φ h ∈ Set.range j) ∧
      Function.Injective (χ.toMonoidHom.comp φ) ∧
      (∀ W : E.left.ProEt, IsAffine W.left → J.IsWeaklyContractible.{u + 1} W →
        ∀ (h : H) (t : T ⟶ W),
          (Scheme.ProEt.genericPointSepAction E.left φ h).unop ≫ t = t → h = 1) ∧
      let a := Scheme.ProEt.genericPointSepAction E.left φ
      let hT : ∀ ⦃S : Sieve T⦄, S ∈ J T → S (𝟙 T) :=
        fun _ h ↦ Scheme.ProEt.id_mem_genericPointSep E.left h
      let U := Sheaf.evaluationRep a R J
      let V := Sheaf.coevaluationRep a R (J := J) hT
      let F := V.obj (Rep.trivial R H R)
      Nonempty (U ⊣ V) ∧ PreservesFiniteLimits U ∧
      PreservesColimitsOfSize.{u + 1, u + 1} U ∧
      PreservesFiniteLimits V ∧ PreservesFiniteColimits V ∧
      Nonempty (U.obj ((constantSheaf J (ModuleCat.{u + 1} R)).obj
        (ModuleCat.of R R)) ≅ Rep.trivial R H R) ∧
      (∀ (M : Rep.{u + 1} R H) (W : E.left.ProEt),
        Nonempty (((V.obj M).obj.obj (op W)) ≅
          ModuleCat.of R (Presheaf.equivariantFunctions a R M W))) ∧
      (∀ (W : E.left.ProEt), IsAffine W.left → J.IsWeaklyContractible.{u + 1} W →
        ∀ (I : Type (u + 1)) (repr : I → (T ⟶ W)),
          (∀ t : T ⟶ W, ∃! i : I, ∃ h : H, (a h).unop ≫ repr i = t) →
          ∀ M : Rep.{u + 1} R H,
            Nonempty (((V.obj M).obj.obj (op W)) ≅ ModuleCat.of R (I → M))) ∧
      (∀ n : ℕ,
        Nonempty (DerivedCategory.UnboundedCohomologyObstruction.cohomology.{
          u + 2, u + 1, u + 1, u + 2, u + 1, u + 1, u + 1, 0, u + 1} e Q F n ≅
          groupCohomology (Rep.trivial R H R) (n + 1)) ∧
        ¬ IsZero (DerivedCategory.UnboundedCohomologyObstruction.cohomology.{
          u + 2, u + 1, u + 1, u + 2, u + 1, u + 1, u + 1, 0, u + 1} e Q F n)) ∧
      (∀ (_ : Finite R), HasInvertibleExponent R E.left →
        ¬ etaleOrigin (ModuleCat.{u + 1} R) E.left F) ∧
      (∀ c : ℕ, ¬ HasUniformCohomologicalDimensionLE (ModuleCat.{u + 1} R) E.hom c) ∧
      (let K := DerivedCategory.UnboundedCohomologyObstruction.shifts.{
        u + 2, u + 1, u + 1} F
       Nonempty (IsLimit (Fan.mk (∐ K) (Sigma.π K))) ∧
       ∃ (α : ModuleCat.of R
             (⨁ n : ℕ, DerivedCategory.UnboundedCohomologyObstruction.cohomology.{
               u + 2, u + 1, u + 1, u + 2, u + 1, u + 1, u + 1, 0, u + 1} e Q F n) ≅
             (DerivedCategory.UnboundedCohomologyObstruction.evaluation.{
               u + 2, u + 1, u + 1, u + 1, 0, u + 1} e).obj
               (∐ fun n : ℕ ↦ Q.obj (K n)))
         (β : (DerivedCategory.UnboundedCohomologyObstruction.evaluation.{
           u + 2, u + 1, u + 1, u + 1, 0, u + 1} e).obj
             (Q.obj (∐ K)) ≅ ModuleCat.of R
               (∀ n : ℕ, DerivedCategory.UnboundedCohomologyObstruction.cohomology.{
                 u + 2, u + 1, u + 1, u + 2, u + 1, u + 1, u + 1, 0, u + 1} e Q F n)),
         (∀ n : ℕ, ModuleCat.ofHom (DirectSum.lof R ℕ
             (fun z : ℕ ↦ DerivedCategory.UnboundedCohomologyObstruction.cohomology.{
               u + 2, u + 1, u + 1, u + 2, u + 1, u + 1, u + 1, 0, u + 1} e Q F z) n) ≫ α.hom =
           (DerivedCategory.UnboundedCohomologyObstruction.shiftIdentification.{
             u + 2, u + 1, u + 1, u + 2, u + 1, u + 1, u + 1, 0, u + 1} e Q F n).inv ≫
           (DerivedCategory.UnboundedCohomologyObstruction.evaluation.{
             u + 2, u + 1, u + 1, u + 1, 0, u + 1} e).map
             (Sigma.ι (fun z : ℕ ↦ Q.obj (K z)) n)) ∧
         (∀ n : ℕ, β.hom ≫ ModuleCat.ofHom (LinearMap.proj n) =
           (DerivedCategory.UnboundedCohomologyObstruction.evaluation.{
             u + 2, u + 1, u + 1, u + 1, 0, u + 1} e).map
             (Q.map (Sigma.π K n)) ≫
           (DerivedCategory.UnboundedCohomologyObstruction.shiftIdentification.{
             u + 2, u + 1, u + 1, u + 2, u + 1, u + 1, u + 1, 0, u + 1} e Q F n).hom) ∧
         α.hom ≫ (DerivedCategory.UnboundedCohomologyObstruction.evaluation.{
           u + 2, u + 1, u + 1, u + 1, 0, u + 1} e).map
           (sigmaComparison Q K) ≫ β.hom = ModuleCat.ofHom (DirectSum.coeFnLinearMap R)) ∧
      ¬ Function.Surjective (DirectSum.coeFnLinearMap R
        (M := fun n : ℕ ↦ DerivedCategory.UnboundedCohomologyObstruction.cohomology.{
          u + 2, u + 1, u + 1, u + 2, u + 1, u + 1, u + 1, 0, u + 1} e Q F n)) ∧
      ¬ PreservesColimitsOfShape (Discrete ℕ) Q ∧
      ¬ Q.IsLeftAdjoint ∧ ¬ Qplus.IsLeftAdjoint ∧
      (∀ c : Compactification E.hom,
        Nonempty (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c ≅ Q) ∧
        ¬ PreservesColimitsOfShape (Discrete ℕ)
          (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c) ∧
        ¬ (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).IsLeftAdjoint ∧
        ¬ (rightDerivedLowerShriekOfCompactificationPlus
          (ModuleCat.{u + 1} R) c).IsLeftAdjoint) ∧
      ∃ (v : ModuleCat.{u + 1} R ⥤
          Sheaf (Scheme.ProEt.topology (Spec (.of D.k))) (ModuleCat.{u + 1} R))
        (adj : e ⊣ v),
        v.Additive ∧ PreservesFiniteLimits v ∧ PreservesFiniteColimits v ∧
        (∀ (_ : IsField R), Injective (v.obj (ModuleCat.of R R)) ∧ ∀ n : ℕ,
          Function.Bijective (DerivedCategory.UnboundedCohomologyObstruction.injectiveHomMap.{
            u + 2, u + 1, u + 1, u + 2, u + 1, u + 1, u + 1, 0, u + 1} e Q adj F n
              (ModuleCat.of R R)) ∧
          Nontrivial (DerivedCategory.UnboundedCohomologyObstruction.cohomology.{
            u + 2, u + 1, u + 1, u + 2, u + 1, u + 1, u + 1, 0, u + 1} e Q F n ⟶
              ModuleCat.of R R)) ∧
        ∀ I : ModuleCat.{u + 1} R, Injective I → IsCoseparator I →
          Injective (v.obj I) ∧ ∀ n : ℕ,
            Function.Bijective
              (DerivedCategory.UnboundedCohomologyObstruction.injectiveHomMap.{
                u + 2, u + 1, u + 1, u + 2, u + 1, u + 1, u + 1, 0, u + 1} e Q adj F n I) ∧
            Nontrivial
              (DerivedCategory.UnboundedCohomologyObstruction.cohomology.{
                u + 2, u + 1, u + 1, u + 2, u + 1, u + 1, u + 1, 0, u + 1} e Q F n ⟶ I) ∧
            Nontrivial (Q.obj (DerivedCategory.UnboundedCohomologyObstruction.shifts.{
              u + 2, u + 1, u + 1} F n) ⟶
              (DerivedCategory.singleFunctor _ 0).obj (v.obj I)) := by
  sorry

private theorem fullCdScope_residue (r : ℕ) [Fact r.Prime] :
    Nonempty (Padic.coefficientExtensionRing r (Padic r) 1 ≃+* ZMod r) := by
  let O := Padic.coefficientExtensionIntegers r (Padic r)
  let m := Padic.coefficientExtensionMaximalIdeal r (Padic r)
  have hs := (Padic.extension_integers_dvr r (Padic r)
    (Padic.coefficientExtensionAbsoluteValue r (Padic r))
    (spectralNorm_extends (K := Padic r) (L := Padic r))).choose_spec.choose_spec
  have habs (x : Padic r) :
      Padic.coefficientExtensionAbsoluteValue r (Padic r) x = ‖x‖ :=
    spectralNorm_extends (K := Padic r) (L := Padic r) x
  let e : O ≃+* PadicInt r :=
    { toFun := fun x ↦ ⟨x, (habs x) ▸ ((hs.1 x).mp x.property)⟩
      invFun := fun x ↦ ⟨x, (hs.1 x).mpr ((habs x).symm ▸ x.property)⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  let f : O →+* ZMod r := PadicInt.toZMod.comp e.toRingHom
  have hker : RingHom.ker f = Padic.coefficientExtensionIdeal r (Padic r) 1 := by
    have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer r (Padic r)} : Set O) = m :=
      hs.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
    change RingHom.ker f = Ideal.span _ ^ 1
    rw [pow_one, hgen]
    ext x
    change PadicInt.toZMod (e x) = 0 ↔ x ∈ m
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod,
      IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
    change ‖(x : Padic r)‖ < 1 ↔ x ∈ m
    have hm : x ∈ m ↔ Padic.coefficientExtensionAbsoluteValue r (Padic r) x < 1 :=
      hs.2.1 x
    simpa only [habs] using hm.symm
  exact ⟨(Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := f)
      ((ZMod.ringHom_surjective PadicInt.toZMod).comp e.surjective))⟩

/-- The finite coefficient specialization uses precisely the recorded ambient predicates.

Source: the scope remark, choice A = F_r = A_(Q_r,1) and consequence (i).
(blueprint: sk-rem-sf-fullcd-scope)

Proof: identify the chosen DVR quotient of Q_r in degree one with F_r; a uniformizer
of Z_r generates its maximal ideal, so its quotient is Z/r. Since r differs from the
characteristic, it is a unit on the field base. Apply `fullCdScope_counterexample`
to F_r, transporting fixed-ring sheaves to constant-ring modules by the recorded
constant-ring equivalence. Its nonzero higher direct images contradict the first
clause of sfFullCohomologicalDimension for every c. The trivial compactification has
proper part f itself, so its ambient datum cannot exist. For every other presentation,
proper compactification independence transports the failed coproduct preservation
and failed adjunction to sfAmbientCompactSupportCandidate.
-/
theorem fullCdScope_finiteCoefficient
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (E₀ : Over (Spec (.of D.k₀))) [GrpObj E₀] [IsAbelianVariety E₀]
    (_hDim : IsAbelianVariety.dim E₀ = 1)
    (r : ℕ) [Fact r.Prime] (_hrp : r ≠ D.p) :
    letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
    let E := D.geometricFiber E₀
    letI : GrpObj E :=
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).grpObjObj
    letI : IsAbelianVariety E :=
      IsAbelianVariety.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) E₀
    Nonempty (Padic.coefficientExtensionRing r (Padic r) 1 ≃+* ZMod r) ∧
    (∀ x : Spec (.of D.k), IsUnit (r : (Spec (.of D.k)).presheaf.stalk x)) ∧
    (∀ c : ℕ, ¬ Scheme.sfFullCohomologicalDimension E.hom (ULift.{u} (ZMod r)) c) ∧
    ¬ Nonempty (Scheme.SfAmbientExceptionalRightAdjointDatum (ULift.{u} (ZMod r))
      E.hom (Compactification.ofIsProper E.hom)) ∧
    (∀ c : Compactification E.hom,
      ¬ (Scheme.sfAmbientCompactSupportCandidate (ULift.{u} (ZMod r)) c).IsLeftAdjoint ∧
      ¬ PreservesColimitsOfShape (Discrete ℕ)
        (Scheme.sfAmbientCompactSupportCandidate (ULift.{u} (ZMod r)) c)) := by
  classical
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let E := D.geometricFiber E₀
  let : GrpObj E :=
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).grpObjObj
  let : IsAbelianVariety E :=
    IsAbelianVariety.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) E₀
  let A := ULift.{u} (ZMod r)
  let R := ULift.{u + 1, u} A
  let : IsGrothendieckAbelian.{u + 1}
      (Sheaf (Scheme.ProEt.topology E.left) (ModuleCat.{u + 1} R)) := inferInstance
  let : IsGrothendieckAbelian.{u + 1}
      (Sheaf (Scheme.ProEt.topology (Spec (.of D.k))) (ModuleCat.{u + 1} R)) := inferInstance
  let : IsGrothendieckAbelian.{u + 1} (ModuleCat.{u + 1} R) := inferInstance
  let : HasSheafify (Scheme.ProEt.topology E.left) (ModuleCat.{u + 1} R) :=
    GrothendieckTopology.hasSheafify_proEtTopology (ModuleCat.{u + 1} R) E.left
  let : HasSheafify (Scheme.ProEt.topology (Spec (.of D.k))) (ModuleCat.{u + 1} R) :=
    GrothendieckTopology.hasSheafify_proEtTopology (ModuleCat.{u + 1} R) (Spec (.of D.k))
  let : HasWeakSheafify (Scheme.ProEt.topology E.left) (ModuleCat.{u + 1} R) :=
    HasSheafify.isRightAdjoint
  let : HasWeakSheafify (Scheme.ProEt.topology (Spec (.of D.k))) (ModuleCat.{u + 1} R) :=
    HasSheafify.isRightAdjoint
  let : HasGlobalSectionsFunctor (Scheme.ProEt.topology (Spec (.of D.k)))
      (ModuleCat.{u + 1} R) := hasGlobalSectionsFunctor_of_hasTerminal _ _
  have h := fullCdScope_counterexample D E₀ _hDim r _hrp R
  dsimp only at h
  rcases h with ⟨_, _, _, ρ, b, χ, g, j, φ, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩
  rcases h with ⟨_, _, _, _, _, _, _, _, hcoh, _, _, _, _, _, _, _, hcomp, _⟩
  have hfull (c : ℕ) : ¬ Scheme.sfFullCohomologicalDimension E.hom A c := by
    intro hc
    let qX := Scheme.sfIntrinsicModuleEquivalence E.left A
    let qY := Scheme.sfIntrinsicModuleEquivalence (Spec (.of D.k)) A
    let H := Multiplicative (ULift.{u + 1} ℕ →₀ ℤ)
    let a := Scheme.ProEt.genericPointSepAction E.left φ
    let hT : ∀ ⦃S : Sieve (Scheme.ProEt.genericPointSep E.left)⦄,
        S ∈ Scheme.ProEt.topology E.left _ → S (𝟙 _) :=
      fun _ hS ↦ Scheme.ProEt.id_mem_genericPointSep E.left hS
    let F := (Sheaf.coevaluationRep a R hT).obj (Rep.trivial R H R)
    let Q := R((E.hom)_*[ModuleCat.{u + 1} R])
    let K := (DerivedCategory.singleFunctor _ 0).obj F
    let e := Sheaf.Γ.{u + 1, u, u + 2, u + 1}
      (Scheme.ProEt.topology (Spec (.of D.k))) (ModuleCat.{u + 1} R)
    let := preservesEpimorphisms_sheafSections_of_iso (A := ModuleCat.{u + 1} R)
      (Iso.refl (Spec (.of D.k)))
    let : e.PreservesEpimorphisms := Functor.PreservesEpimorphisms.of_iso
      (Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId _)).symm
    let : e.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels e
    let : PreservesFiniteColimits e := Functor.preservesFiniteColimits_of_preservesHomology e
    have hz : IsZero ((DerivedCategory.homologyFunctor _ ((c + 1 : ℕ) : ℤ)).obj
        (Q.obj K)) := by
      apply qY.functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
      let t : qY.functor.mapDerivedCategory.obj (Q.obj K) ≅
          (Scheme.proEtaleConstantDerivedDirectImage E.hom A).obj
            ((DerivedCategory.singleFunctor _ 0).obj (qX.functor.obj F)) :=
        ((Scheme.sfIntrinsicDerivedDirectImageComparison E.hom A).app K).symm ≪≫
          (Scheme.proEtaleConstantDerivedDirectImage E.hom A).mapIso
            ((qX.functor.mapDerivedCategorySingleFunctor 0).app F)
      exact (hc.1 (qX.functor.obj F) (c + 1) (by omega)).of_iso
        ((DerivedCategory.homologyFunctor _ ((c + 1 : ℕ) : ℤ)).mapIso t)
    apply (hcoh c).2
    let : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} R) :=
      HasDerivedCategory.ofIsGrothendieckAbelian _
    dsimp only [DerivedCategory.UnboundedCohomologyObstruction.cohomology]
    exact Functor.isZero_homologyFunctor_mapDerivedCategory_obj.{
      u + 2, u + 2, u + 1, u + 1, u + 1, u + 1} e hz
  have hcand (c : Compactification E.hom) :
      ¬ PreservesColimitsOfShape (Discrete ℕ) (Scheme.sfAmbientCompactSupportCandidate A c) := by
    intro hc
    let := hc
    let eX := Scheme.sfIntrinsicDerivedEquivalence E.left A
    let eY := Scheme.sfIntrinsicDerivedEquivalence (Spec (.of D.k)) A
    have : PreservesColimitsOfShape (Discrete ℕ)
        (eX.functor ⋙ Scheme.sfAmbientCompactSupportCandidate A c) := inferInstance
    have : PreservesColimitsOfShape (Discrete ℕ)
        (sfFixedCompactSupport A c ⋙ eY.functor) :=
      preservesColimitsOfShape_of_natIso (sfIntrinsicCompactSupportComparison A c)
    have : PreservesColimitsOfShape (Discrete ℕ) (sfFixedCompactSupport A c) :=
      preservesColimitsOfShape_of_reflects_of_preserves _ eY.functor
    exact (hcomp c).2.1 this
  refine ⟨fullCdScope_residue r, ?_, hfull, ?_, ?_⟩
  · let : Fintype D.k₀ := Fintype.ofFinite D.k₀
    let : Fact D.p.Prime := ⟨D.prime⟩
    let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
    have hu : IsUnit (r : D.k₀) := (CharP.isUnit_natCast_iff D.prime).2 (by
      intro hd
      exact _hrp ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : r.Prime)).1 hd).symm)
    have hk : IsUnit (r : D.k) := by
      simpa only [map_natCast] using hu.map (algebraMap D.k₀ D.k)
    intro x
    simpa only [map_natCast] using hk.map
      (((Scheme.ΓSpecIso (.of D.k)).inv ≫
        (Spec (.of D.k)).presheaf.germ ⊤ x (by trivial))).hom
  · rintro ⟨d⟩
    obtain ⟨c, hc⟩ := d.fullCD
    exact hfull c hc
  · intro c
    refine ⟨?_, hcand c⟩
    intro hL
    let := hL
    exact hcand c inferInstance

/-!
The remaining scope clauses reuse the imported declarations:

* `Scheme.proEtale_compact_generators` gives compact generation for ordinary rings.
* `isZero_homology_rightDerivedLowerStar_comparisonUpperStar` and
  `constructible_proEtale_origin` give the finite discrete-coefficient comparison domain.
* `exists_comparisonClassAdjunction` is relative to bounded-below etale-origin inputs;
  `Scheme.sf_preservation_class` preserves that finite-coefficient constructible class.
* `CondensedRing.ctfExceptionalInverseImage` and `CondensedRing.ctfExceptionalAdjunction`
  are the restriction of the localizing adjunction, with their own coefficient and base
  hypotheses. `CondensedRing.exceptionalInverseImage_exists_current` and
  `CondensedRing.sk_prop_sf_rf_shriek_preservation` give the current existence and finite
  preservation interfaces. None of these assumes an unrestricted ambient datum.
* `CondensedRing.general_verdier_biduality_current`,
  `WeilConjectures.finite_stage_verdier_biduality`, and `boundary_duality_input` retain
  their own stated hypotheses and use the constructible adjoint.

The counterexample takes an ordinary ring R, including discrete Q_l; it makes no
assertion about the topological condensed ring associated to Q_l. In particular 09AK
has not been used to identify a general condensed coefficient object with an etale sheaf.
The tensor-Hom and Kunneth-Verdier references in the remark are statements about the
scope of those consumers, not hypotheses used to construct the counterexample.
-/

end AlgebraicGeometry.ProEtale
