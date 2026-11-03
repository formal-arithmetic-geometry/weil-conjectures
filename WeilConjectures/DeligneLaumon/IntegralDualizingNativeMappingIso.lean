/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import WeilConjectures.SixFunctors.Coefficient.CoefficientDuality
import WeilConjectures.DeligneLaumon.IntegralDualizingNativeMappingAction
import WeilConjectures.DeligneLaumon.IntegralDualizingNativeHomEquiv
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Detecting invertibility of the native exceptional mapping action
Source: current blueprint prop-coef-integral-dualizing.proof.md, paragraph 2.
(blueprint: lem-coef-integral-dualizing-native-mapping-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace WeilConjectures

set_option maxHeartbeats 2000000 in
-- Elaborating the fixed dependent scalar and adjunction interfaces needs this budget.
/-- Normalization of the action and the ordinary exceptional adjunction imply that
the natural morphism of full derived mapping complexes is invertible.

Source: current blueprint prop-coef-integral-dualizing.proof.md, paragraph 2
(blueprint: lem-coef-integral-dualizing-native-mapping-iso).

Proof: take the canonical constructible shift from exceptional exactness. For every
K and i the normalization square identifies H^i of the action, through two bijections,
with the counit adjunction map for K[-i]. That map is bijective by the ordinary Hom
adjunction. Hence each cohomology map is an isomorphism of scalar modules. Derived
cohomology detects isomorphisms in the unbounded derived category. The existing
natural transformation therefore defines a natural isomorphism. No completeness,
uniform bound, or finite-level reduction is needed for this detection step.
-/
theorem integralDualizing_native_mapping_iso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] [IsAlgClosed k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (hR : IsNativeExceptionalCoefficient l (DerivedNakayama.integerRing l E)) :
    let R := DerivedNakayama.integerRing l E
    let s := Spec (.of k)
    letI : LocallyOfFiniteType (Over.mk (𝟙 s)).hom :=
      inferInstanceAs (LocallyOfFiniteType (𝟙 s))
    letI : QuasiCompact (Over.mk (𝟙 s)).hom := inferInstanceAs (QuasiCompact (𝟙 s))
    letI : IsSeparated (Over.mk (𝟙 s)).hom := inferInstanceAs (IsSeparated (𝟙 s))
    let f : X ⟶ Over.mk (𝟙 s) := Over.homMk X.hom
    let F := nativeConstructibleLowerShriek R l k
      (exceptionalCurrentFieldCD l k (Or.inr inferInstance)) f hR
    let ω := (currentExceptionalInverseImage R l k (Or.inr inferInstance) f hR).obj
      (IntegralDualizingNative.unit R s)
    Nonempty ((constantModelBoundedConstructible R X.left).ι.op ⋙
      (derivedHom R X.left).flip.obj ω.obj ⋙ CohomologyTransport.Γ R X.left ≅
      F.op ⋙ (constantModelBoundedConstructible R s).ι.op ⋙
        (CohomologyTransport.Γ R s).op ⋙ coefficientDerivedDual (condensedScalarRing R)) := by
  dsimp only
  let R := DerivedNakayama.integerRing l E
  let s := Spec (.of k)
  let : LocallyOfFiniteType (Over.mk (𝟙 s)).hom :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 s))
  let : QuasiCompact (Over.mk (𝟙 s)).hom := inferInstanceAs (QuasiCompact (𝟙 s))
  let : IsSeparated (Over.mk (𝟙 s)).hom := inferInstanceAs (IsSeparated (𝟙 s))
  let f : X ⟶ Over.mk (𝟙 s) := Over.homMk X.hom
  obtain ⟨hX, _, _⟩ :=
    (currentExceptionalInverseImage_properties R l k (Or.inr inferInstance) f hR).2.2.1
  let := hX
  obtain ⟨η, hη⟩ := integralDualizing_native_mapping_action l E k X hR
  have hηiso : ∀ K, IsIso (η.app K) := by
    intro K
    apply (DerivedCategory.isIso_iff _ _).mpr
    intro i
    obtain ⟨eS, eT, hn⟩ := hη K.unop i
    have hb := integralDualizing_native_counit_bijective R l k (Or.inr inferInstance) f hR
      (K.unop⟦-i⟧) (IntegralDualizingNative.unit R s)
    have hc := hb.comp eS.bijective
    have hcomp : Function.Bijective
        (eT ∘ (DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (condensedScalarRing R)) i).map (η.app K)) := by
      convert hc using 1
      funext x
      exact hn x
    exact (ConcreteCategory.isIso_iff_bijective _).mpr
      (Function.Bijective.of_comp_left hcomp eT.injective)
  have : IsIso η := (NatTrans.isIso_iff_isIso_app η).mpr hηiso
  exact ⟨asIso η⟩
end WeilConjectures
