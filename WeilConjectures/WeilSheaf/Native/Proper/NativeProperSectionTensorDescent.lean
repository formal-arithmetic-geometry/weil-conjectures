/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Proper.NativeProperProjectionComparisons
public import WeilConjectures.WeilSheaf.Native.NativeTwoSidedKFlatSections

/-! # Tensor comparison for normalized native section adjunctions

Source: Stacks 07A4, 0G7E; native proper-projection model proof, step 4.
No realization data or direct-image comparison is constructed by this lemma.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison
  WeilConjectures.AdicQbarRealization.ordinary
  WeilConjectures.commonStageDerivedPullback WeilConjectures.commonStageDerivedTensor
  AlgebraicGeometry.Scheme.ContinuousRational.modulePull
  AlgebraicGeometry.Scheme.ContinuousRational.derivedPull

universe u v u' v' w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeilConjectures Opposite
open WeilConjectures.AdicQbarRealization
open AlgebraicGeometry.Scheme
open scoped TensorProduct AlgebraicGeometry.ProEtaleWeilSheaf

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

variable (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  (R : LocallyFiniteAdicRealization.Realization l
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  [∀ x : (X ↘ Spec (CommRingCat.of k₀)).geometricFiber,
    Invertible (l : (X ↘ Spec (CommRingCat.of k₀)).geometricFiber.residueField x)]
  (A : At l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber R)

/-- Normalized tensor descent for the section functor of one scheme.
Source: Stacks 07A4, 06YN and BS 6.8.14--6.8.15.
(blueprint: lem-sf-native-proper-section-tensor-descent).

Proof: construct and descend the normalized single-scheme comparison as follows.

1. Use AdicModuleTensorComparisonCore. Identify comparisonRing with the actual
   sectionRingSheaf by the identity map on locally finite functions. The product
   equation is ScalarForgetting.sectionRing_mul followed by the coefficient
   multiplication equation. Identify the two module actions by
   ScalarForgetting.sectionAction_forget. Restriction of scalars along this ring
   isomorphism preserves the balanced tensor and its sheafification generator;
   the inverse uses the inverse ring isomorphism. Thus the comparison is natural,
   invertible and fixes actual pure tensors, rather than an unspecified scalar
   multiple of them. Compose with native Frobenius forgetting.
2. Apply these comparisons on each (i,j) summand. The exact section functor
   preserves the countable coproducts by R.sectionsColimits. The two differential
   squares follow from sheaf-level naturality, with the same sign (-1)^i in both.
   The inverse is assembled from inverse component maps. The universal property
   of each total coproduct proves the required insertion and generator equation.
3. Use native_two_sided_kflat_sections for the two section complexes. On
   each two-sided K-flat pair compose the specified nativeOpenTensorModel,
   properSectionFactors, localized cochain comparison and A.models.iso. Their
   chain-map naturalities give the required comparison on K-flat representatives.
4. Descend through the K-flat HOMOTOPY subcategory. The existing restriction
   localization lemma in SiteDerivedTensorDescentIndependentCoefficients applies
   after supplying K-flat quasi-isomorphic replacements, as in
   RingedEquivalenceResolvingTensorDescent.model_localization. Refine the vertices
   of homotopy roofs by such replacements; naturality on chain maps gives
   naturality on homotopy classes and inverses of quasi-isomorphisms. This gives
   a natural isomorphism on all derived objects. Its restriction to every K-flat
   pair is the original composite, which is precisely the representative equation.
   No strict calculus of fractions on the category of complexes is assumed.

The empty site, zero complexes and identity section equivalences use the same
pure-tensor and coproduct maps; no nonempty-site hypothesis is needed. -/
theorem native_proper_section_tensor_descent
    (hR : (sectionFunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber R).IsEquivalence) :
    ∃ (cochain : ∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ,
    (properSectionCochain k₀ l X R).obj
      (((nativeTensorTotal k₀ l X).obj P).obj Q) ≅
    (coefficientTotalTensor.{u + 1, u + 1, u}
      (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (ring l _ R)).obj
        ((properSectionCochain k₀ l X R).obj P,
          (properSectionCochain k₀ l X R).obj Q))
      (tensor : nativeDerivedTensor k₀ l X ⋙ properSectionDerived k₀ l X R ≅
    (properSectionDerived k₀ l X R).prod (properSectionDerived k₀ l X R) ⋙ A.closed.tensor),
    (∀ P Q (i j n : ℤ) (h : i + j = n) V x y,
    ((cochain P Q).hom.f n).val.app V
      (properNativeTotalGenerator k₀ l X R P Q i j n h V x y) =
    coefficientTensorGenerator.{u + 1, u + 1, u}
      (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (ring l _ R)
      ((properSectionCochain k₀ l X R).obj P)
      ((properSectionCochain k₀ l X R).obj Q) i j n h V x y) ∧
    (∀ P Q (hP : NativeIsKFlat k₀ l X P) (hQ : NativeIsKFlat k₀ l X Q),
    (properSectionDerived k₀ l X R).map (nativeOpenTensorModel k₀ l X P Q hP hQ).hom ≫
      (properSectionFactors k₀ l X R).hom.app
        (((nativeTensorTotal k₀ l X).obj P).obj Q) ≫
      DerivedCategory.Q.map (cochain P Q).hom ≫
      (A.models.iso _ _ _ _ _
        (native_two_sided_kflat_sections k₀ l X R P hP)
        (native_two_sided_kflat_sections k₀ l X R Q hQ)).hom =
    tensor.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      A.closed.tensor.map (Prod.mkHom
        ((properSectionFactors k₀ l X R).hom.app P)
        ((properSectionFactors k₀ l X R).hom.app Q))) := by sorry

end AlgebraicGeometry.ProEtaleWeilSheaf
