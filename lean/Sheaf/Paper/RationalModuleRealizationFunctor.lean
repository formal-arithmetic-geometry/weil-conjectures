/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q86
-/
module

public import Sheaf.Paper.PbcScalarExtension
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
public import Sheaf.Paper.ContinuousConstructibleModule
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.SfCommonStageWeilCohomology
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import Sheaf.CategoryTheory.LocalizationInverseImageCoherence
import Sheaf.CategoryTheory.ScalarLocalizationSheafExact
import Sheaf.CategoryTheory.ScalarLocalizationTriangulated
import Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Construction and cohomology of rational module realization

Source: Bhatt--Scholze, Lemma 6.8.2, Proposition 6.8.11(3), and the construction
in Proposition 6.8.14(2) (blueprint: lem-per-rational-module-realization-functor).

The realization asserted below has no full-faithfulness or essential-image equivalence
requirement. Field linearity is expressed by the canonical constant scalar action.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The actual lifted inclusion of the valuation ring into its field.
Source: Bhatt--Scholze, Section 6.8
(blueprint: lem-per-rational-module-realization-functor). -/
def rationalModuleIntegerInclusion : PbcIntegralRing l E →+* ULift.{u + 1} E :=
  RingHom.ulift (Padic.coefficientExtensionIntegers l E).subtype

/-- Constant field sections, extended through constant-sheaf sheafification.
Source: Bhatt--Scholze, Definition 6.8.1 and Proposition 6.8.14(2)
(blueprint: lem-per-rational-module-realization-functor). -/
def rationalModuleConstantMap (X : Scheme.{u}) :
    adicLisseConstantRing X (ULift.{u + 1} E) ⟶ rationalCoefficientSheaf l X E := by
  letI := coefficientExtensionNormedField l E
  exact ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
    _ _).symm
      { app := fun _ ↦ CommRingCat.ofHom
          { toFun := fun a ↦ ContinuousMap.const _ a
            map_one' := rfl
            map_mul' := fun _ _ ↦ rfl
            map_zero' := rfl
            map_add' := fun _ _ ↦ rfl }
        naturality := fun _ _ _ ↦ rfl }

/-- The rational model `E_X ⊗_E V`, using the existing constant module and sheaf tensor.
Source: Bhatt--Scholze, Definitions 6.8.6 and 6.8.10
(blueprint: lem-per-rational-module-realization-functor). -/
def rationalModuleConstantModel (X : Scheme.{u}) :
    ModuleCat.{u + 1} (ULift.{u + 1} E) ⥤ pbcModules X (rationalCoefficientSheaf l X E) :=
  adicLisseConstantModules X (ULift.{u + 1} E) ⋙ pbcExtend (rationalModuleConstantMap l E X)

/-- The raw realization and its specified scalar-localization computations.
All coefficient maps are fixed by their section or quotient normalizations.
The model clause is an ordinary tensor identity for every finitely presented N,
including torsion N. Its inverse images give the same identity on all stratum covers.
Source: Bhatt--Scholze, Lemma 6.8.2, Proposition 6.8.11(3), and Proposition 6.8.14(2)
(blueprint: lem-per-rational-module-realization-functor). -/
structure RationalModuleRealization (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] where
  /-- The completion is the sheaf of continuous integral functions. -/
  integralIso : pbcAdicCompletion X (pbcIntegralDatum l E) ≅
    integralCoefficientSheaf l X E
  /-- The finite quotients retain the continuous-function presentation. -/
  finiteIso : ∀ n : ℕ,
    (pbcAdicRings X (pbcIntegralDatum l E)).obj (op n) ≅
      finiteContinuousCoefficientSheaf l X E n
  /-- Finite quotient comparisons preserve constant sections. -/
  finite_normalization : ∀ (n : ℕ) (U : X.ProEtᵒᵖ)
      (a : PbcIntegralRing l E ⧸ (pbcIntegralDatum l E).ideal ^ (n + 1))
      (x : U.unop.left),
    finiteContinuousCoefficientValue l E X n U
      ((finiteIso n).hom.hom.app U
        (pbcFunctionScalars X (pbcIntegralDatum l E) n |>.app U |>.hom <| a)) x =
      integralCoefficientULift l E n a
  /-- The inverse-limit comparison is specified by all quotient projections. -/
  integral_normalization : ∀ (n : ℕ) (U : X.ProEtᵒᵖ)
      (s : (integralCoefficientSheaf l X E).obj.obj U) (x : U.unop.left),
    (finiteContinuousCoefficientValue l E X n U
      ((integralIso.inv ≫ pbcAdicProjection X (pbcIntegralDatum l E) n ≫
        (finiteIso n).hom).hom.app U s) x).down =
      Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
        (integralCoefficientValue l E X U s x)
  /-- Sheaf localization, rather than a global denominator condition. -/
  localizationIso : integralCoefficientLocalization l X E ≅
    rationalCoefficientSheaf l X E
  /-- The localization comparison is the map on integral numerators. -/
  localization_normalization :
    integralCoefficientLocalizationNormalized l E X localizationIso.hom
  /-- Scalar inclusion is the actual inclusion of continuous functions. -/
  inclusion : integralCoefficientSheaf l X E ⟶ rationalCoefficientSheaf l X E
  /-- Pointwise normalization fixes the scalar inclusion uniquely. -/
  inclusion_normalization : integralRationalCoefficientNormalized l E X inclusion
  /-- Locally closed restriction preserves both coefficient rings and their scalar map. -/
  restriction : ∀ (S : Scheme.{u}) (h : S ⟶ X) [IsImmersion h],
    ∃ (cA : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
        (integralCoefficientSheaf l X E) ≅ integralCoefficientSheaf l S E)
      (cE : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
        (rationalCoefficientSheaf l X E) ≅ rationalCoefficientSheaf l S E)
      (aS : integralCoefficientSheaf l S E ⟶ rationalCoefficientSheaf l S E),
      integralCoefficientRestrictionNormalized l E h cA.hom ∧
      rationalCoefficientRestrictionNormalized l E h cE.hom ∧
      integralRationalCoefficientNormalized l E S aS ∧
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map inclusion ≫ cE.hom =
        cA.hom ≫ aS
  /-- The module category carries the field action of constant sections. -/
  [moduleLinear : Linear E (pbcModules X (rationalCoefficientSheaf l X E))]
  /-- The field action is fixed on every module map by multiplication by a constant section. -/
  scalar_normalization : ∀ (M N : pbcModules X (rationalCoefficientSheaf l X E))
      (f : M ⟶ N) (a : E) (U : X.ProEtᵒᵖ) (x : M.val.obj U),
    (a • f).val.app U x =
      (rationalModuleConstantMap l E X).hom.app U
        ((toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} E)))).app U
            (ULift.up a)) • f.val.app U x
  /-- Ordinary scalar localization is exact on module sheaves. -/
  ordinary_exact : PreservesFiniteLimits (pbcExtend (integralIso.hom ≫ inclusion)) ∧
    PreservesFiniteColimits (pbcExtend (integralIso.hom ≫ inclusion))
  /-- The prescribed derived scalar extension is triangulated. -/
  derived_exact : ∃ (_ : (pbcDerivedExtend (integralIso.hom ≫ inclusion)).CommShift ℤ),
    (pbcDerivedExtend (integralIso.hom ≫ inclusion)).IsTriangulated
  /-- Cohomology commutes naturally with localization in every integer degree. -/
  cohomology : ∀ r : ℤ,
    pbcDerivedExtend (integralIso.hom ≫ inclusion) ⋙ DerivedCategory.homologyFunctor _ r ≅
      DerivedCategory.homologyFunctor _ r ⋙ pbcExtend (integralIso.hom ≫ inclusion)
  /-- Bounded integral objects have bounded, stratified locally finite free rational cohomology. -/
  constructible : ∀ K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E),
    (∃ a b : ℤ,
      ((pbcDerivedExtend (integralIso.hom ≫ inclusion)).obj K.obj).IsGE a ∧
      ((pbcDerivedExtend (integralIso.hom ≫ inclusion)).obj K.obj).IsLE b) ∧
    ∀ r : ℤ, ∃ s : FiniteLocallyClosedStratification X, ∀ i : Fin s.n,
      ((proEtaleModuleInverseImage (s.immersion i)
        (rationalCoefficientSheaf l X E)).obj
          ((DerivedCategory.homologyFunctor _ r).obj
            ((pbcDerivedExtend (integralIso.hom ≫ inclusion)).obj K.obj))).IsFiniteLocallyFree
  /-- The raw rationalization has its unchanged integral objects. -/
  J : PbcRationalCategory X (pbcIntegralDatum l E) (pbcUniformizer l E) ⥤
    DerivedCategory (pbcModules X (rationalCoefficientSheaf l X E))
  /-- Addition and the canonical E-action are preserved. -/
  [additive : J.Additive]
  /-- E-linearity for the canonical localization action and constant field sections. -/
  [linear : J.Linear E]
  /-- Integer shifts commute with realization. -/
  [shift : J.CommShift ℤ]
  /-- Distinguished triangles are preserved. -/
  triangulated : J.IsTriangulated
  /-- The displayed formula on QK is literal equality of objects. -/
  objects : ∀ K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E),
    J.obj ((pbcRationalization X (pbcIntegralDatum l E)
      (pbcUniformizer l E)).obj K) =
        (pbcDerivedExtend (integralIso.hom ≫ inclusion)).obj K.obj
  /-- The displayed formula on every fraction, with transports for the object equalities. -/
  fractions : ∀ (K L : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E))
      (f : K ⟶ L) (n : ℕ),
    J.map (((pbcRationalCoefficientEquiv l E).symm
      (((pbcUniformizer l E).down.val ^ n)⁻¹)) •
        (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).map f) =
      eqToHom (objects K) ≫
        (((pbcUniformizer l E).down.val ^ n)⁻¹ •
          (pbcDerivedExtend (integralIso.hom ≫ inclusion)).map f.hom) ≫
            eqToHom (objects L).symm
  /-- The integral model localizes to E_X tensor the finite-dimensional space E tensor N. -/
  models : ∀ (N : ModuleCat.{u + 1} (PbcIntegralRing l E)),
    Module.FinitePresentation (PbcIntegralRing l E) N →
      Nonempty ((pbcExtend (integralIso.hom ≫ inclusion)).obj
        ((integralConstantModule X (pbcIntegralDatum l E)).obj N) ≅
          (rationalModuleConstantModel l E X).obj
            ((ModuleCat.extendScalars (rationalModuleIntegerInclusion l E)).obj N)) ∧
      Module.Finite (ULift.{u + 1} E)
        ((ModuleCat.extendScalars (rationalModuleIntegerInclusion l E)).obj N) ∧
      Module.Free (ULift.{u + 1} E)
        ((ModuleCat.extendScalars (rationalModuleIntegerInclusion l E)).obj N)

/-- Scalar localization induces the raw rational module realization, with its
coefficient, cohomology, constructibility and local-model normalizations.
Source: Bhatt--Scholze, Lemma 6.8.2, Definition 6.8.10, Proposition 6.8.11(3),
and the construction of Proposition 6.8.14(2)
(blueprint: lem-per-rational-module-realization-functor).

Proof, following the node's eight steps:
1. Use lem-weil-pbc-continuous-coefficients-immersion-restriction to identify the
completed ring with continuous integral functions and its sheaf localization with
continuous rational functions. Quotient projections fix the constant sections;
normalized pullback gives locally closed restriction and the scalar square.
2. Apply lem-weil-pbc-scalar-localization-sheaf-exact and
lem-weil-pbc-exact-functor-derived-factorization. The K-flat comparison of
lem-pur-derived-change-of-rings identifies derived extension with this exact
termwise functor, since it carries a K-flat resolution to a quasi-isomorphism.
3. Apply lem-weil-pbc-exact-functor-complex-cohomology to cycles and boundaries.
The comparison is natural for cochain maps and inverses of quasi-isomorphisms,
hence descends to roofs. All cohomological vanishing intervals are preserved.
4. Use lem-weil-pbc-integral-stratified-perfect-characterization for boundedness
and finitely presented local integral models, retaining the compatible etale
witnesses. Exact inverse image and slice restriction commute with cohomology
by lem-weil-pbc-local-derived-restriction-comparisons. Apply
lem-weil-pbc-localization-inverse-image-coherence to transport localization to
each stratum and each covering object, with the normalized coefficient maps.
5. By lem-pur-sheaf-ring-coefficient-ordinary-adjunction, successive extension
of scalars is left adjoint to composite restriction. Uniqueness of left adjoints
identifies the double tensor with E_X tensor_A N; on pure tensors it sends
e tensor (b tensor n) to eb tensor n, without requiring flatness of N.
6. Take a finite presentation of N. By
lem-sfb-constant-finite-free-presentation-extension, constant sheafification and
extension identify its cokernel with that of the same matrix over E_X. Row and
column reduction over E gives a free cokernel E^d; constant invertible matrices
stay invertible over E_X. This proves the model formula and finite freeness,
including N=0 and torsion N, whose rational rank is zero.
7. The tensor functor and its derived extension are A-linear by
lem-cbc-exact-linear-derived-functor. Set J(QK)=F(K) and
J(f/varpi^n)=varpi^(-n) F(f). A common denominator and a further power annihilating
the difference prove independence of representatives, functoriality and additivity.
lem-weil-l-adic-integers-localization-uniformizer identifies A[1/varpi] with E
and proves E-linearity of that formula.
8. The integral characterization gives closure under shifts and cones.
lem-weil-linear-abelian-derived-category gives linear shifts, so
lem-weil-linear-scalar-localization-triangulated applies. The shift comparison
is natural on fractions by linearity. Every rational distinguished triangle is
isomorphic to the rationalization of an integral distinguished triangle, whose
image under F is distinguished. Thus J is triangulated. -/
theorem rationalModuleRealizationFunctor (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] :
    Nonempty (RationalModuleRealization l E X) := by
  sorry

end AlgebraicGeometry.Scheme
