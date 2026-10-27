/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q104
-/
module

public import Sheaf.Paper.EtaleDerivedScalarTensor
public import Sheaf.SecSmoothPurity.SupportedEtaleTensorOrigin
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.Paper.ComparisonPullbackExact
public import Sheaf.CategoryTheory.ConstantCoefficientScalarExtensionPresentations
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations
public import Sheaf.Paper.WitnessCompatibility
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
import Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Paper.RingedTopoiDerivedPullbackIndependent
import Sheaf.Paper.KFlatScalarComparisonNormalization
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.SiteOneSidedTensorNormalization

/-! # The bounded-flat coefficient/site square

Source: Stacks Project, Tags 06YQ, 0G7E, 06YY, 07A4, 08G1 and 03EL
(blueprint: lem-sp-bounded-flat-coefficient-site-square).

The fixed-scalar module-sheaf presentation retains the target-ring action. Every
comparison below is the published adjunction comparison, including its chain model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.ProEtale
namespace BoundedFlatCoefficientSiteSquare

/-- Bundle flatness, strict support and K-flatness, without choosing a
resolution. Source: Stacks 06YQ and 08G1
(blueprint: lem-sp-bounded-flat-coefficient-site-square). -/
def modelProperties {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) (A : Type (u + 1)) [CommRing A] (a b : ℤ)
    (P : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℤ) : Prop :=
  (∀ q : ℤ, exactFunctor _ _ (tensorRight (P.X q))) ∧
    (∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q)) ∧
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P

/-- The etale model, using the recorded etale universal Tor test itself.
Source: Stacks 08G1 (blueprint: lem-sp-bounded-flat-coefficient-site-square). -/
def etaleModelProperties (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (a b : ℤ) (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    Prop :=
  modelProperties X.smallEtaleTopology A a b P ∧
    Etale.DerivedCategory.hasTorAmplitudeIn A X a b
      (_root_.DerivedCategory.Q.{u + 1, u + 1, u + 2}.obj P)

/-- The pro-etale model, using the recorded fixed-coefficient Tor specialization itself.
Source: Stacks 08G1 (blueprint: lem-sp-bounded-flat-coefficient-site-square). -/
def proEtaleModelProperties (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (a b : ℤ)
    (P : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ℤ) : Prop :=
  @modelProperties.{u} X.ProEt inferInstance
      (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X) A inferInstance a b P ∧
    Scheme.HasFixedCoefficientProEtaleTorAmplitude X A
      (_root_.DerivedCategory.Q.{u + 1, u + 1, u + 2}.obj P) a b

/-- The actual chain comparison, obtained by applying the ordinary adjunction
comparison in each degree. Source: Stacks 03EL
(blueprint: lem-sp-bounded-flat-coefficient-site-square). -/
def chainComparison {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) :=
  (Functor.mapHomologicalComplexCompIso
    (Iso.refl (etaleSheafExtendScalars φ X ⋙ comparisonUpperStar.{u + 2, u} (ModuleCat.{u + 1} B)
        X))
      (.up ℤ)).symm ≪≫
    NatIso.mapHomologicalComplex (etaleSheafExtendScalarsCompComparisonUpperStarIso φ X)
      (.up ℤ) ≪≫
    Functor.mapHomologicalComplexCompIso
      (Iso.refl (comparisonUpperStar.{u + 2, u} (ModuleCat.{u + 1} A) X ⋙ sheafExtendScalars φ X))
        (.up ℤ)

/-- Bounded flat representatives simultaneously compute change of coefficients and
exact etale/pro-etale inverse image, including the canonical B-linear derived square.

Source: Stacks 06YQ, 0G7E, 06YY, 07A4, 08G1 and 03EL
(blueprint: lem-sp-bounded-flat-coefficient-site-square).

Proof:
1. lem-sf-comparison-pullback-exact identifies inverse-image constant coefficients
and gives exactness. The exact-functor localization factor gives Q(N_A P) = N_A Q(P).
2. lem-weil-pbc-ringed-topos-flat-module-pullback preserves flat terms for both scalar
extensions and both site inverse images. Additivity preserves zero terms, so all
five complexes remain supported in [a,b].
3. lem-weil-pbc-independent-bounded-flat-kflat gives K-flatness of every complex,
against arbitrary acyclic complexes. No boundedness is imposed on a test complex.
4. lem-weil-pbc-ringed-topoi-derived-pullback computes scalar extension on P and
N_A P. Its counits, transposed through the scalar adjunction, are precisely the
representative arrows below. They are invertible and natural in chain maps.
5. lem-sfb-kflat-scalar-comparison-normalization gives the canonical ordinary
comparison of 03EL, with its target B-action. Applying it in every degree gives
chainComparison. The natural isomorphism already contains naturality in all
chain maps. Its normalization identifies the localized comparison with the
inverse of pbcComparisonReduction, the scalar-adjunction mate recorded in
def-weil-pbc-witness-compatibility.
6. To identify this mate with the canonical tensor/site comparison of
lem-weil-pbc-ringed-topoi-derived-tensor-pullback, resolve B[0] using
lem-pc-kflat-resolution. Apply lem-trf-site-one-sided-tensor-normalization to
P and N_A P. Naturality in the coefficient resolution gives a commuting tensor
square whose vertical maps are isomorphisms. Cancellation identifies its bottom
map with the localized ordinary comparison, including the target-ring action.
7. For each of the five representatives C and every module sheaf M in degree
zero, the same one-sided tensor normalization computes QC tensor M by C tensor
M[0]. Its q-th term is C^q tensor M, zero outside [a,b]. Its cohomology vanishes
there, proving the universal Tor test. Neither flatness nor finite projective
dimension of B over A, constructibility of P, nor Noetherianity of X is used. -/
theorem boundedFlatCoefficientSiteSquare
    (X : Scheme.{u}) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (a b : ℤ) (_hab : a ≤ b)
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (_hflat : ∀ q : ℤ, exactFunctor _ _ (tensorRight (P.X q)))
    (_hbounded : ∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q)) :
    etaleModelProperties.{u} X A a b P ∧
    etaleModelProperties.{u} X B a b
      (((etaleSheafExtendScalars φ X).mapHomologicalComplex (.up ℤ)).obj P) ∧
    proEtaleModelProperties.{u} X A a b
      (((comparisonUpperStar.{u + 2, u} (ModuleCat.{u + 1} A) X).mapHomologicalComplex (.up ℤ)).obj
        P) ∧
    proEtaleModelProperties.{u} X B a b
      (((sheafExtendScalars φ X).mapHomologicalComplex (.up ℤ)).obj
        (((comparisonUpperStar.{u + 2, u} (ModuleCat.{u + 1} A) X).mapHomologicalComplex (.up
        ℤ)).obj P)) ∧
    proEtaleModelProperties.{u} X B a b
      (((comparisonUpperStar.{u + 2, u} (ModuleCat.{u + 1} B) X).mapHomologicalComplex (.up ℤ)).obj
        (((etaleSheafExtendScalars φ X).mapHomologicalComplex (.up ℤ)).obj P)) ∧
    IsIso (Etale.scalarExtensionRepresentative.{u} φ X P) ∧
    IsIso (SupportedEtaleTensorOrigin.proScalarExtensionRepresentative.{u} φ X
      (((comparisonUpperStar.{u + 2, u} (ModuleCat.{u + 1} A) X).mapHomologicalComplex (.up ℤ)).obj
        P)) ∧
    ((comparisonUpperStar.{u + 2, u} (ModuleCat.{u + 1} B) X).mapDerivedCategory.map
        (Etale.scalarExtensionRepresentative.{u} φ X P) ≫
      (comparisonUpperStar.{u + 2, u} (ModuleCat.{u + 1} B) X).mapDerivedCategoryFactors.hom.app
        (((etaleSheafExtendScalars φ X).mapHomologicalComplex (.up ℤ)).obj P) ≫
      _root_.DerivedCategory.Q.{u + 1, u + 1, u + 2}.map ((chainComparison.{u} φ X).hom.app P) =
    (pbcComparisonReduction.{u} X φ).inv.app (_root_.DerivedCategory.Q.{u + 1, u + 1, u + 2}.obj P)
        ≫
      (SheafOfModules.constantCoefficientProEtaleScalarExtension.{u} φ X).map
        ((comparisonUpperStar.{u + 2, u} (ModuleCat.{u + 1} A) X).mapDerivedCategoryFactors.hom.app
        P) ≫
      SupportedEtaleTensorOrigin.proScalarExtensionRepresentative.{u} φ X
        (((comparisonUpperStar.{u + 2, u} (ModuleCat.{u + 1} A) X).mapHomologicalComplex (.up
        ℤ)).obj P)) := by
  sorry

end BoundedFlatCoefficientSiteSquare
end AlgebraicGeometry.ProEtale
