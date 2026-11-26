/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportData
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCoefficientInverseImage
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeAdicForgetAbEquivalence
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeDirectImageSections
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.EquivalenceAdjunctionComparisonSupplement
import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetMonoidalAdjunction
import WeilConjectures.SixFunctors.ProEtale.Adic.Hom
import WeilConjectures.CategoryTheory.Sites.SheafComposeBraided

/-! # Native locally finite coefficient transport

The native section presentation of locally finite adic coefficients respects pullback,
direct image and open extension.

## Implementation details

The construction forgets the constant algebraic-closure vector-space action on a native
internal module (an exact additive equivalence) and then uses the section-module
equivalence. Both direct images evaluate the same module on the same base-changed test
object, so the direct-image comparison is the identity on sections; pullback and open
extension are obtained by conjugating the native adjunctions through the section
equivalences. No finite-type or separatedness hypothesis is used.

## References

* [Bhatt--Scholze, Section 6.8]
* [Stacks, Tags 03D6, 03D7 and 03DI]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option linter.style.haveILetI false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]

private theorem native_commutative (T : Scheme.{u}) : IsCommMonObj (abRing l T) := by
  haveI : IsCommMonObj (ProEtale.adicConstantSheaf l T) :=
    ProEtale.adicConstantSheaf.isCommMonObj T
  let _ : (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1}).LaxBraided :=
    ModuleCat.laxBraidedForget₂Ab _
  letI : (ProEtale.weilCoefficientsForgetAb l T).LaxBraided :=
    CategoryTheory.sheafComposeLaxBraided _ _
  exact Functor.isCommMonObj_obj (F := ProEtale.weilCoefficientsForgetAb l T)

/-- The native section presentation respects pullback, direct image and open extension:
there is a `NativeGeometry` structure. -/
theorem native_compact_support_geometry : Nonempty (NativeGeometry.{u} l) := by
  classical
  let commutative : ∀ T : Scheme.{u}, IsCommMonObj (abRing l T) :=
    native_commutative l
  let pull {U V : Scheme.{u}} (g : U ⟶ V) :=
    (native_coefficient_inverse_image l g).choose
  let N : NativeRings.{u} l :=
    { commutative := commutative
      pull := pull
      pull_normalized := fun g ↦ (native_coefficient_inverse_image l g).choose_spec.1 }
  have equivalence (T : Scheme.{u}) : (sections l T).IsEquivalence := by
    have := native_adic_forgetAb_isEquivalence l T
    unfold sections
    infer_instance
  have additive (T : Scheme.{u}) : (sections l T).Additive :=
    Functor.additive_of_preserves_binary_products (sections l T)
  let lower {U V : Scheme.{u}} (g : U ⟶ V) :=
    (native_direct_image_sections l g).choose
  let upperExists {U V : Scheme.{u}} (g : U ⟶ V) :=
    exists_equivalenceAdjunctionComparison
      (sections l V).asEquivalence (sections l U).asEquivalence
      (ProEtale.adicUpperStarLowerStarAdjunction l g)
      (proEtaleRingModuleAdjunction g (ringSheaf l V) (ringSheaf l U) (N.pull g))
      (lower g)
  let upper {U V : Scheme.{u}} (g : U ⟶ V) := (upperExists g).choose
  let extensionExists {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :=
    exists_equivalenceAdjunctionComparison
      (sections l U).asEquivalence (sections l V).asEquivalence
      (ProEtale.adicOpenImmersionLowerShriekAdjunction l j)
      (PurCompactSupport.openAdjunction (nativeCoefficients l) j) (upper j)
  let extension {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :=
    (extensionExists j).choose
  exact ⟨{
    toNativeRings := N
    additive := additive
    limits := fun T ↦ inferInstance
    colimits := fun T ↦ inferInstance
    equivalence := equivalence
    lower := lower
    lower_normalized := fun g ↦ (native_direct_image_sections l g).choose_spec.1
    upper := upper
    upper_normalized := fun g ↦ (upperExists g).choose_spec.1
    extension := extension
    extension_normalized := fun j ↦ (extensionExists j).choose_spec.1 }⟩

end WeilConjectures.LocallyFiniteAdicCompactSupport
