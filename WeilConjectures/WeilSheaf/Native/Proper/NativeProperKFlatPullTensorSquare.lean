/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Proper.NativeProperSectionAdjunctionModels
public import WeilConjectures.WeilSheaf.Native.NativeTwoSidedKFlatSections

/-! # Pullback tensor square on native K-flat representatives

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

variable {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (p : Z ⟶ Y) [p.IsOver (Spec (CommRingCat.of k₀))]

variable
  (R : LocallyFiniteAdicRealization.Realization l
    (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  (S : LocallyFiniteAdicRealization.Realization l
    (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  [∀ x : (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber,
    Invertible (l : (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber.residueField x)]
  [∀ y : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber,
    Invertible (l : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber.residueField y)]
  (O : Proper.Operations l (NativeBaseChange.geometricMap k₀ p) R S)

variable
  (A : At l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber R)
  (B : At l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber S)
  (C : Proper.TensorComparison l (NativeBaseChange.geometricMap k₀ p) R S O A B)
  (J : NativeProperSectionAdjunctionModels k₀ l p R S O)

/-- The normalized pullback tensor square on two-sided K-flat representatives.
Source: Stacks 07A4, 0G7E, 0DEN, 0DEP and BS 6.8.14--6.8.15; proper-projection model,
step 4 (blueprint: lem-sf-native-proper-kflat-pull-tensor-square).

Proof: Use the given natural sheaf comparison rho and its ordinary normalization.
Its invertible Frobenius-algebra components already give equivariance.

1. Totalize rho in every bidegree. Preserve every insertion and signed differential.
   Use lemma-pullback-K-flat-points for arbitrary K-flat complexes: the pro-etale
   site has enough points, source stalks are K-flat, ring base change preserves
   that test, and the reverse stalk criterion detects K-flatness on the target.
   Translate through the ordinary normalized section comparison and use
   native_two_sided_kflat_forget. Exact conservative Frobenius forgetting and
   the two tensor-cone comparisons establish both native quasi-isomorphism tests.
   The flat-term pullback theorem alone would not justify this assertion.
2. Form the comparison on K-flat pairs using the specified native tensor model
   maps and exact inverse-image localization factors. Descend via homotopy roofs
   refined by K-flat replacements. Naturality and inverse identities are inherited
   from the totalized sheaf maps. Record the presentation, all compatibility
   identifications and ordinary sheaf normalization, obtaining balanced.
3. Compute J.pull on these models. J.pushSections fixes the sheaf push comparison
   by its identity on actual sections. J.pushRepresentative fixes the derived push
   comparison on K-injective complexes, which represent all derived objects.
   J.counit makes J.pull its left adjoint mate. Uniqueness of the mate therefore
   identifies it with the localized balanced sheaf inverse-image comparison.
4. Rewrite the desired square using C.representative, TZ.representative,
   TY.representative and the presentation equation of balanced. The two composites
   on each pure tensor apply the same coefficient precomposition and send
   b tensor (x tensor y) to (b tensor x) tensor (1 tensor y). The inverse multiplies
   the two coefficients. Balancing and Frobenius compatibility hold by the
   coefficient equation. Sheaf tensor extensionality and total coproduct
   extensionality give the chain equality, and localization gives the square at
   Q(P), Q(Q).

This assumes the two section tensor structures and a normalized sheaf-level
comparison; it constructs neither structure and asserts the square only on
K-flat representatives. Empty schemes, zero inputs and identity pullback have
the same balanced formulas. -/
theorem native_proper_kflat_pull_tensor_square
    (hR : (sectionFunctor l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber R).IsEquivalence)
    (hS : (sectionFunctor l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber S).IsEquivalence)
    (rho : nativeOpenSheafTensor k₀ l Y ⋙ upperStar k₀ l p ≅
      (upperStar k₀ l p).prod (upperStar k₀ l p) ⋙ nativeOpenSheafTensor k₀ l Z)
    (hrho : ∀ M N, HEq ((rho.hom.app (M, N)).hom.f)
      ((ProEtale.adicUpperStarTensorLeftIso l
        (Scheme.Hom.geometricFiberMap p (comp_over p _)) N.carrier).hom.app M.carrier))
    (TZ : ProperSectionTensor k₀ l Z R A)
      (TY : ProperSectionTensor k₀ l Y S B) :
    ∃ balanced : NativeProjectionTensorComparison k₀ l p,
      ∀ (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ),
      NativeIsKFlat k₀ l Y P → NativeIsKFlat k₀ l Y Q →
      (properSectionDerived k₀ l Z R).map
          (balanced.mu.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        TZ.tensor.hom.app
          ((nativeOpenPull k₀ l p).obj (DerivedCategory.Q.obj P),
            (nativeOpenPull k₀ l p).obj (DerivedCategory.Q.obj Q)) ≫
        A.closed.tensor.map (Prod.mkHom
          (J.pull.hom.app (DerivedCategory.Q.obj P))
          (J.pull.hom.app (DerivedCategory.Q.obj Q))) =
      J.pull.hom.app ((nativeDerivedTensor k₀ l Y).obj
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        (ContinuousRational.derivedPull
          (NativeBaseChange.geometricMap k₀ p) O.coefficient).map
            (TY.tensor.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        C.tensor.hom.app
          ((properSectionDerived k₀ l Y S).obj (DerivedCategory.Q.obj P),
            (properSectionDerived k₀ l Y S).obj (DerivedCategory.Q.obj Q)) := by sorry

theorem native_proper_section_tensor_descent_legacy
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
