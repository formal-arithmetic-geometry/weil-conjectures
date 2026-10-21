/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.PadicIntegersInvertEll
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.SectionDerivedPushpullNormalization
import Sheaf.Paper.SectionDerivedTensorNormalization
import Sheaf.CategoryTheory.InternalSectionScalarAdjunction
import Sheaf.Paper.CondensedQcqsPushforwardContinuity
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.CategoryTheory.ScalarLocalizationTelescopeCore
import Sheaf.CategoryTheory.ScalarLocalizationModuleColimit
import Sheaf.CategoryTheory.ScalarLocalizationSheafExact
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Paper.CartesianCoefficients

/-!
# Localization of coefficients and bounded-below direct image

Source: Hemo--Richarz--Scholbach, Lemmas 5.3(1) and 5.6; Bhatt--Scholze,
Remark 6.8.15 (blueprint: lem-sfb-localized-direct-image-comparison).

The map is the published coefficient-change mate on the ambient module categories.
Its flatness argument is supplied by the existing localization theorem, rather than
assumed of the complex or of the scheme morphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option synthInstance.maxHeartbeats 80000 in
-- Elaborate the two scalar derived functors and their geometric adjunction mate.
/-- The canonical coefficient-change/direct-image arrow. The inclusion is pulled back
from the point. The published `derivedPushHom` is the mate of the canonical restriction
comparison; equivalently it is adjoint to scalar extension of the geometric counit,
after the canonical pullback/tensor identification. Its required scalar exactness is
the last assertion of `padicIntegers_invertEll`, not an additional hypothesis.
Source: HRS Lemma 5.3(1), natural comparison (5.4), and Stacks 07A6, 07A4
(blueprint: lem-sfb-localized-direct-image-comparison). -/
def localizedDirectImageComparison (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) :
    (Mod.extendScalars (padicIntegersToPadicSubfield Y ℓ E)).leftDerivedFunctor.obj
        ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj ℓ E.1) f).obj C) ⟶
      (moduleObjectDerivedPushforward (Profinite.continuousMapRingObj E.1) f).obj
        ((Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).leftDerivedFunctor.obj C) :=
  letI : ∀ Z : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E) Z)) :=
    fun Z ↦ (padicIntegers_invertEll Z ℓ E).choose_spec.2.choose_spec.2.2.choose_spec.2.2.2
  (derivedPushHom (padicIntegersRingObjToContinuousMapRingObj ℓ E) f).app C

set_option synthInstance.maxHeartbeats 80000 in
-- The ambient derived category retains the full module tensor-resolution structure.
/-- Localization of coefficients commutes with ordinary ambient derived direct image
for every bounded-below complex; completeness, constructibility and finite Tor
amplitude are not required.
Source: HRS Lemmas 5.3(1), 5.6; Bhatt--Scholze Remark 6.8.15
(blueprint: lem-sfb-localized-direct-image-comparison).

Proof:
1. Use `lem-pd-section-derived-pushpull-normalization`,
`lem-sfb-internal-section-scalar-adjunction` and
`lem-pd-section-derived-tensor-normalization` to pass to section-ring modules,
preserving the specified units, counits and tensor comparison.
2. By `det-prop-sfb-qlbar-colimit-x-invert-ell`, E_Z is A_Z[1/ℓ]. Scalar extension
is exact by `lem-weil-pbc-scalar-localization-sheaf-exact` and agrees with its
termwise derived functor by `lem-weil-pbc-exact-functor-derived-functor`.
Cartesian coefficients and `lem-weil-pbc-ring-sheaf-change-adjunction` give the
adjunction-compatible restriction/direct-image isomorphism d.
3. Good-truncate a representative of C below a cohomological lower bound a.
By `lem-weil-pbc-scalar-localization-complex-colimit`, its scalar telescope has
colimit U_X L_X C with nth leg ℓ⁻ⁿ times the scalar unit. All terms vanish below a.
4. Apply `lem-weil-pbc-condensed-qcqs-pushforward-continuity` to this sequence.
In each degree q it identifies the telescope colimit with H^q(Rf_* U_X L_X C).
Exactness and `lem-weil-pbc-scalar-localization-module-colimit` identify the same
colimit with H^q(U_Y L_Y Rf_* C), with the prescribed fraction-unit legs.
5. For the stated mate β put t = U_Y β followed by d. Adjunction compatibility,
the definition of the mate, and the canonical pullback/tensor unit normalization
of `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` give
η followed by t = Rf_*(η). On K-flat representatives both maps insert 1 in E.
6. Naturality and E-linearity extend that equality to every ℓ⁻ⁿ-unit leg.
The colimit universal property therefore makes H^q(t) the composite of the two
colimit isomorphisms in step 4, hence an isomorphism for all integers q.
7. By `lem-weil-pbc-unbounded-derived-iso-cohomology`, t is invertible. Since d
is invertible and scalar restriction is conservative, β is invertible.
The normalized equivalences in step 1 recover exactly the original ambient map. -/
theorem localizedDirectImageComparison_isIso (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))
    (hC : DerivedCategory.TStructure.t.plus C) :
    IsIso (localizedDirectImageComparison ℓ E f C) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
