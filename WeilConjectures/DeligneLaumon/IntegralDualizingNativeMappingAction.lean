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
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.K.KInjectiveTotalDerivedLinear
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom
import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Ulift
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedMappingAction.Step.DerivedMappingSingleStepConstruction
import WeilConjectures.CategoryTheory.DerivedMappingAction.DerivedMappingOrdinaryAction
import WeilConjectures.CategoryTheory.DerivedMappingModel.DerivedMappingDerivedHom
import WeilConjectures.CategoryTheory.DerivedMappingAction.Step.MappingArrow.DerivedMappingSingleStepAlgebra
import WeilConjectures.CategoryTheory.DerivedMappingAction.Step.MappingArrow.DerivedMappingRepresentativeShiftCohomology

/-! # The normalized action on integral global mapping complexes

Source: current blueprint prop-coef-integral-dualizing.proof.md, paragraph 2,
the direct counit map and its cohomological normalization.
(blueprint: lem-coef-integral-dualizing-native-mapping-action).
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
/-- The actual compact-support action followed by the actual counit, together with
its degreewise normalization. Invertibility is not part of this assertion.

Source: current blueprint prop-coef-integral-dualizing.proof.md, paragraph 2
(blueprint: lem-coef-integral-dualizing-native-mapping-action).

Proof: resolve internal module complexes by the K-injective models defining derived
Hom and terminal scalar sections. Apply the linear compact-support mapping action
separately to exact open extension and proper direct image, then use the universal
comparison from their composite to the fixed compactification functor. Postcompose
with its specified exceptional counit. On the algebraically closed point the exact
scalar-section functor takes the actual coefficient unit to the regular scalar module;
the perfect-point comparison therefore identifies the result with coefficient duality.
The ordinary Hom-complex normalization identifies degree i with maps from K[-i].
Naturality of all resolution comparisons gives the functor morphism below. The
mapping action's normalization and counit postcomposition give the displayed square,
with precisely the fixed compactification, not an arbitrary comparison. This also
covers zero complexes, empty schemes and negative i.
-/
theorem integralDualizing_native_mapping_action
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] [IsAlgClosed k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (hR : IsNativeExceptionalCoefficient l (DerivedNakayama.integerRing l E))
    [(constantModelBoundedConstructible
      (DerivedNakayama.integerRing l E) X.left).IsTriangulated] :
    let R := DerivedNakayama.integerRing l E
    let s := Spec (.of k)
    letI : LocallyOfFiniteType (Over.mk (𝟙 s)).hom :=
      inferInstanceAs (LocallyOfFiniteType (𝟙 s))
    letI : QuasiCompact (Over.mk (𝟙 s)).hom := inferInstanceAs (QuasiCompact (𝟙 s))
    letI : IsSeparated (Over.mk (𝟙 s)).hom := inferInstanceAs (IsSeparated (𝟙 s))
    let f : X ⟶ Over.mk (𝟙 s) := Over.homMk X.hom
    let F := nativeConstructibleLowerShriek R l k
      (exceptionalCurrentFieldCD l k (Or.inr inferInstance)) f hR
    let adj := currentExceptionalAdjunction R l k (Or.inr inferInstance) f hR
    let U := IntegralDualizingNative.unit R s
    let ω := (currentExceptionalInverseImage R l k (Or.inr inferInstance) f hR).obj U
    let S := (constantModelBoundedConstructible R X.left).ι.op ⋙
      (derivedHom R X.left).flip.obj ω.obj ⋙ CohomologyTransport.Γ R X.left
    let T := F.op ⋙ (constantModelBoundedConstructible R s).ι.op ⋙
      (CohomologyTransport.Γ R s).op ⋙ coefficientDerivedDual (condensedScalarRing R)
    ∃ η : S ⟶ T, ∀ (K : ConstantModelBoundedConstructible R X.left) (i : ℤ),
      let H := DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (condensedScalarRing R)) i
      ∃ (eS : H.obj (S.obj (op K)) ≃ ((K⟦-i⟧).obj ⟶ ω.obj))
        (eT : H.obj (T.obj (op K)) ≃
          ((rightDerivedLowerShriekOfCompactification R (compactificationOverField f)).obj
            (K⟦-i⟧).obj ⟶ U.obj)),
        ∀ x, eT (H.map (η.app (op K)) x) =
          (rightDerivedLowerShriekOfCompactification R (compactificationOverField f)).map
            (eS x) ≫ (adj.counit.app U).hom := by
  sorry

end WeilConjectures
