/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.Paper.ContinuousCoefficientModuleEncoding
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction
public import Sheaf.Paper.PbcScalarExtension
import Sheaf.Paper.ContinuousCoefficientRealizations
import Sheaf.Paper.ContinuousModuleEncodingScalarExtension
import Sheaf.CategoryTheory.ScalarLocalizationSheafExact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.AlgebraicGeometry.BoundedConstructibleExtendScalars
import Sheaf.CategoryTheory.ScalarLocalization
import Sheaf.CategoryTheory.ScalarLocalizationTriangulated
import Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import Sheaf.UpstreamExtra.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory

/-! # Actual scalar extension on raw integral rationalizations

Source: Bhatt--Scholze, Lemma 6.8.2 and Propositions 6.8.11(3), 6.8.14(2).
(blueprint: lem-weil-pbc-realization-scalar-functor)

The coefficient encodings are the published constructions. The record below retains
only the scalar functor and its normalization; it contains no equivalence assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj TensorProduct
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]
variable (T : Scheme.{u}) [IsNoetherian T]
  [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

/-- The coefficient-normalized scalar functor, with the actual extension and restriction
on the ambient derived categories. The integral comparison expresses J(K)=F(K) in
sectionwise coordinates; the fraction equation uses that same comparison.
Source: Bhatt--Scholze, 6.8.2, 6.8.11(3), 6.8.14(2).
(blueprint: lem-weil-pbc-realization-scalar-functor) -/
structure RealizationScalarFunctorData where
  coefficientIso : Mon.mk (condensedRingObj (Profinite.continuousCoefficientRingObj E) T) ≅
    Mon.mk ((sheafCompose (ProEt.topology T) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      (AlgebraicGeometry.ProEtale.continuousCoefficientRingSheaf T E))
  coefficient_normalization : ∀ (S : Profinite.{u}) (f : C(S, E)),
    (((pointUpperStarLowerStarAdjunction.comp
      (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ T))).homEquiv
        _ _ coefficientIso.hom.hom).hom.app (op S)) (ULift.up f) =
      ULift.up (f.comp (profiniteTestProjection T S))
  sectionIso : (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology T)
    (condensedRingObj (Profinite.continuousCoefficientRingObj E) T)) ≅ rationalCoefficientSheaf l T
    E
  section_normalization : ∀ (U : T.ProEtᵒᵖ) (s : ((InternalAbelianSheafModule.sectionRingSheaf.{u +
    1, u + 1, u} (ProEt.topology T) (condensedRingObj (Profinite.continuousCoefficientRingObj E)
    T))).obj.obj U)
      (x : U.unop.left),
    rationalCoefficientValue l E T U (sectionIso.hom.hom.app U s) x =
      (((coefficientIso.hom.hom).hom.app U) s).down x
  integralIso : pbcAdicCompletion T (pbcIntegralDatum l E) ≅
    AlgebraicGeometry.Scheme.integralCoefficientSheaf l T E
  finiteIso : ∀ n : ℕ,
    (pbcAdicRings T (pbcIntegralDatum l E)).obj (op n) ≅
      finiteContinuousCoefficientSheaf l T E n
  finite_normalization : ∀ (n : ℕ) (U : T.ProEtᵒᵖ)
      (a : PbcIntegralRing l E ⧸ (pbcIntegralDatum l E).ideal ^ (n + 1)) (x : U.unop.left),
    finiteContinuousCoefficientValue l E T n U
      ((finiteIso n).hom.hom.app U
        (pbcFunctionScalars T (pbcIntegralDatum l E) n |>.app U |>.hom <| a)) x =
      integralCoefficientULift l E n a
  integral_normalization : ∀ (n : ℕ) (U : T.ProEtᵒᵖ)
      (s : (AlgebraicGeometry.Scheme.integralCoefficientSheaf l T E).obj.obj U) (x : U.unop.left),
    (finiteContinuousCoefficientValue l E T n U
      ((integralIso.inv ≫ pbcAdicProjection T (pbcIntegralDatum l E) n ≫
        (finiteIso n).hom).hom.app U s) x).down =
      Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
        (integralCoefficientValue l E T U s x)
  inclusion : AlgebraicGeometry.Scheme.integralCoefficientSheaf l T E ⟶ rationalCoefficientSheaf
    l T E
  inclusion_normalization : integralRationalCoefficientNormalized l E T inclusion
  [encodingAdditive : ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology T) (condensedRingObj (Profinite.continuousCoefficientRingObj E) T)).trans
    (ringModuleEquivalenceOfIso T ((adicLisseForget T).mapIso sectionIso).symm)).functor.Additive]
  [encodingInverseAdditive : ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology T) (condensedRingObj (Profinite.continuousCoefficientRingObj E) T)).trans
    (ringModuleEquivalenceOfIso T ((adicLisseForget T).mapIso sectionIso).symm)).inverse.Additive]
  extension_exact : PreservesFiniteLimits (pbcExtend (integralIso.hom ≫ inclusion))
  extension_colimits : PreservesFiniteColimits (pbcExtend (integralIso.hom ≫ inclusion))
  restriction_exact : PreservesFiniteLimits (pbcRestrict (integralIso.hom ≫ inclusion))
  restriction_colimits : PreservesFiniteColimits (pbcRestrict (integralIso.hom ≫ inclusion))
  [restriction_shift : (pbcDerivedRestrict (integralIso.hom ≫ inclusion)).CommShift ℤ]
  restriction_derived_exact : (pbcDerivedRestrict (integralIso.hom ≫ inclusion)).IsTriangulated
  [ambient_shift : (pbcDerivedExtend (integralIso.hom ≫ inclusion)).CommShift ℤ]
  ambient_exact : (pbcDerivedExtend (integralIso.hom ≫ inclusion)).IsTriangulated
  unit : ∀ P : CochainComplex (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ,
    (pbcDerivedScalarAdjunction (integralIso.hom ≫ inclusion)).unit.app
        (DerivedCategory.Q.obj P) ≫
      (pbcDerivedRestrict (integralIso.hom ≫ inclusion)).map
        (pbcComplexCounit (integralIso.hom ≫ inclusion) P) ≫
      (pbcRestrict (integralIso.hom ≫ inclusion)).mapDerivedCategoryFactors.hom.app
        (((pbcExtend (integralIso.hom ≫ inclusion)).mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          (pbcScalarAdjunction (integralIso.hom ≫ inclusion)).unit (.up ℤ)).app P)
  computes : ∀ P : CochainComplex (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ,
    IsIso (pbcComplexCounit (integralIso.hom ≫ inclusion) P)
  tensor_unit : ∀ (M : pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E)))
      (U : T.ProEtᵒᵖ) (m : M.val.obj U),
    ((pbcScalarAdjunction (integralIso.hom ≫ inclusion)).unit.app M).val.app U m =
      pbcTensorSection (integralIso.hom ≫ inclusion) M U 1 m
  J : PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E) ⥤ BoundedConstructible
    (condensedRingObj (Profinite.continuousCoefficientRingObj E) T)
  [additive : J.Additive]
  [shift : J.CommShift ℤ]
  exact : J.IsTriangulated
  integral : pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙
      J ⋙ (boundedConstructible (condensedRingObj (Profinite.continuousCoefficientRingObj E) T)).ι ⋙
        ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} (ProEt.topology T)
          (condensedRingObj (Profinite.continuousCoefficientRingObj E) T)).trans
          (ringModuleEquivalenceOfIso T ((adicLisseForget T).mapIso
          sectionIso).symm)).mapDerivedCategory.functor ≅
    ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)) ⋙
      pbcDerivedExtend (integralIso.hom ≫ inclusion)
  linearity : ∀ (K L : PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E)) (f : K ⟶
    L) (a : E),
    (((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} (ProEt.topology T)
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) T)).trans
      (ringModuleEquivalenceOfIso T ((adicLisseForget T).mapIso
      sectionIso).symm)).mapDerivedCategory.functor).map
        (J.map (a • f)).hom =
      @SMul.smul _ _
        (@Linear.homModule _ _ _ _ _
          (@DerivedCategory.instLinear _ _ _ _ _
            (SheafOfModules.homLinear (rationalCoefficientSheaf l T E).obj
              (((adicLisseForget T).obj (rationalCoefficientSheaf l T E)).property)) _)
          _ _).toSMul
        ⟨fun _ ↦ @ContinuousMap.const _ (ULift E) _
          (@ULift.topologicalSpace E
            (coefficientExtensionNormedField l E).toUniformSpace.toTopologicalSpace)
          (ULift.up a), fun _ ↦ rfl⟩
        ((((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} (ProEt.topology
        T) (condensedRingObj (Profinite.continuousCoefficientRingObj E) T)).trans
        (ringModuleEquivalenceOfIso T ((adicLisseForget T).mapIso
        sectionIso).symm)).mapDerivedCategory.functor).map (J.map f).hom)
  fractions : ∀ (K L : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)) (f : K ⟶ L) (n :
    ℕ),
    (((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} (ProEt.topology T)
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) T)).trans
      (ringModuleEquivalenceOfIso T ((adicLisseForget T).mapIso
      sectionIso).symm)).mapDerivedCategory.functor).map
        (J.map ((pbcRationalCoefficientEquiv l E).symm
          (((pbcUniformizer l E).down : E) ^ n)⁻¹ •
            (pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).map f)).hom ≫
      integral.hom.app L =
    integral.hom.app K ≫
      (@SMul.smul _ _
        (@Linear.homModule _ _ _ _ _
          (@DerivedCategory.instLinear _ _ _ _ _
            (SheafOfModules.homLinear (rationalCoefficientSheaf l T E).obj
              (((adicLisseForget T).obj (rationalCoefficientSheaf l T E)).property)) _)
          _ _).toSMul
        ⟨fun _ ↦ @ContinuousMap.const _ (ULift E) _
          (@ULift.topologicalSpace E
            (coefficientExtensionNormedField l E).toUniformSpace.toTopologicalSpace)
          (ULift.up (((pbcUniformizer l E).down : E) ^ n)⁻¹), fun _ ↦ rfl⟩
        ((pbcDerivedExtend (integralIso.hom ≫ inclusion)).map f.hom))

/-- Actual scalar extension is exact, takes integral objects to the archived bounded
constructible category, and factors through the raw rationalization by the stated fractions.
Source: Bhatt--Scholze, 6.8.2, 6.8.11(3), 6.8.14(2).
(blueprint: lem-weil-pbc-realization-scalar-functor)

Proof:
1. Identify the completed coefficient ring with continuous integral functions using
lem-weil-pbc-continuous-coefficients-immersion-restriction, normalized on every finite
quotient. The inclusion is postcomposition with A→E. The continuous coefficient
realization and module encoding identify the specified internal and sectionwise maps.
2. Apply lem-weil-pbc-scalar-localization-sheaf-exact to this sheaf localization.
Exact-functor derived factorization and lem-weil-pbc-exact-functor-derived-functor
identify termwise extension with the total left derived tensor, with its shift comparison.
3. Apply lem-pur-sheaf-ring-derived-coefficient-adjunction on the identity site.
Restriction is exact; the ambient adjunction has the pure-tensor unit. Its K-flat
normalization extends to every complex by naturality and exactness of both functors.
4. Integral stratified perfect characterization gives bounded cohomology with finitely
presented integral local models. Their finite presentations and the module encoding,
followed by bounded constructible exact scalar extension, give the archived local finite
presentation condition in the target. No local freeness characterization is used.
5. Send K to F(K) and u/varpi^n to varpi^(-n) F(u). The localization relation is respected
because varpi acts invertibly in E. Addition, composition, identities and E-linearity
follow from the tensor balancing relation and the common denominator calculation.
6. Integral closure under shifts and cones and scalar localization triangulation identify
every rational distinguished triangle with an integral image. Exactness of F and step 4
show its J-image is distinguished in the full target. Naturality of the shift comparison
extends from integral arrows to fractions. The constructible Serre theorem and bounded
constructible triangulation give the target's induced triangulated structure. -/
theorem realization_scalar_functor (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    [T.Over (Spec (.of k))] [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))] [IsSeparated (T ↘ Spec (.of k))] :
    Nonempty (RealizationScalarFunctorData l E T) := by
  sorry

end WeilConjectures
