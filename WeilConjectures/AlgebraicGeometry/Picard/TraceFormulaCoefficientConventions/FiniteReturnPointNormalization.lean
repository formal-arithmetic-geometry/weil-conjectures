/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.TraceFormulaCoefficientConventions.SelectedSchemeGaloisComparison
public import WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructible
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.TraceFormulaCoefficientConventions.TraceFormulaCoefficientConventions
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPoint
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.SchemeFrobenius
public import WeilConjectures.ZetaWeil.FrobeniusPointTransport
public import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExact
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Limits.Types.ColimitType
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.AlgebraicGeometry.SixFunctors.FrobeniusTrivializationPullback
public import WeilConjectures.DeligneLaumon.LocalFrobeniusTrace
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatRingedToposPullback

/-! # Point-section normalization of finite return Frobenius -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.TraceFormulaCoefficientConventions

/-- The normalized absolute-Frobenius point map is the specified restriction followed
by distinguished insertion, for arbitrary sheaves, and on complexes it is exactly the
successive point transport with the canonical compositors.

Source: current blueprint, lem-trf-absolute-frobenius-site.proof.md,
finite-return specialization, original argument Steps 2--6; Stacks Tag 0F6W
(blueprint: lem-trf-finite-return-point-normalization).

Proof: for an automorphism h of s, the graph object (U,hu) is initial in the inverse-image
comma category, so its insertion gives the sectionwise inverse-image identification.
The constant-coefficient tensor map sends x tensor a to ax, with inverse x to x tensor 1.
The canonical compositor sends the graph of a composite to the two successive graph
insertions and x tensor a to (x tensor 1) tensor a; its adjunction-unit characterization
identifies it with the recorded intrinsic compositor. For r = h inverse, evaluate the
unit equation defining the absolute-Frobenius trivialization at (s,r). The relative
Frobenius there is r, so the equation says that the trivialization is inverse restriction
along r. Applied to h*N, this becomes restriction along h followed by the graph insertion.
The one-step finite point transport uses exactly this restriction, insertion, and tensor
unit. Induct on m: the zero case is the canonical identity pullback, and presheaf
functoriality composes successive restrictions into restriction along h^m, while the
canonical compositors compose the same graph insertions and tensor units. Apply this
natural sheaf identity degreewise; its naturality ensures compatibility with differentials.
This gives the asserted chain identity without flatness or constructibility assumptions. -/
theorem finiteReturn_point_normalization
    (T : TraceFormulaCoefficientConventions.{u}) (m : ℕ)
    (wRH : T.returnAbsolute
        (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))) m ≫
      T.returnBasePower m = 𝟙 (Spec (.of T.datum.k))) :
    (∀ (N : proEtaleRingModules (Spec (.of T.datum.k))
        (proEtaleConstantRing (Spec (.of T.datum.k)) T.coefficientRing))
      (x : N.val.obj (op (ProEt.mk (𝟙 (Spec (.of T.datum.k)))))),
      ((T.returnPointAbsolute m wRH).app N).val.app
          (op (ProEt.mk (𝟙 (Spec (.of T.datum.k))))) x =
        T.returnSectionInsertion m N (N.val.map (T.returnRestriction m).op x)) ∧
    (∀ N : CochainComplex
        (proEtaleRingModules (Spec (.of T.datum.k))
          (proEtaleConstantRing (Spec (.of T.datum.k)) T.coefficientRing)) ℤ,
      ((pointFiniteSections T.datum.k T.coefficientRing).mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex (T.returnPointAbsolute m wRH) (.up ℤ)).app N) =
        T.returnPointChainPower m N) := by
  sorry

end WeilConjectures.TraceFormulaCoefficientConventions
