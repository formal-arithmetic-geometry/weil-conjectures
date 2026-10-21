/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuityDirectImage
import Sheaf.CategoryTheory.InternalSectionTensorComparison
import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import Sheaf.Paper.QlbarTailModuleColimit
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.Paper.ProjectionMateExact
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Paper.CartesianCoefficients

/-!
# Algebraic-closure coefficient change and bounded-below direct image

Source: Hemo--Richarz--Scholbach, Lemmas 5.3(1) and 5.6; Bhatt--Scholze,
Remark 6.8.15 (blueprint: lem-sfb-qlbar-direct-image-comparison).

The comparison is the existing coefficient-change mate `derivedPushHom` in the
ordinary ambient derived category of internal module objects. Its algebraic-closure
coefficient ring uses continuous functions with values in one finite subextension.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Algebraic-closure extension commutes with qcqs direct image on every bounded-below
ambient module complex, without constructibility or finite Tor amplitude.
Source: Hemo--Richarz--Scholbach, Lemmas 5.3(1), 5.6; Bhatt--Scholze, Remark 6.8.15
(blueprint: lem-sfb-qlbar-direct-image-comparison).

Proof plan:
1. Transport internal modules to section-ring module sheaves using
   lem-pe-internal-section-tensor-comparison and lem-sfb-internal-module-operations-transport.
   Exact equivalences preserve injective resolutions and the null-homotopy test for
   K-injectivity (lem-weil-pbc-equivalence-injective-resolutions), so this also preserves
   the derived adjunction and its counit (sk-def-sfb-derived-categories).
2. The finite intermediate fields containing E form a nonempty directed tail. Their
   actual inclusion legs exhibit the algebraic-closure coefficient module as a colimit
   (lem-sfb-qlbar-tail-module-colimit). Cartesian coefficients identify their pullbacks
   and inclusion maps (sk-prop-sfb-cartesian-coefficients, sk-def-sfb-coefficient-change).
   Finite coefficients are finite free; closure coefficients are flat
   (lem-sfb-subfield-flat, lem-sfb-qlbar-flat).
3. Represent C by a complex vanishing below one integer a, using
   def-sbc-standard-tstructure-derived-category. Exact scalar extension preserves this
   common bound. Tensor preserves the coefficient colimit termwise
   (lem-weil-pbc-independent-sheaf-tensor-colimits). Filtered module colimits are exact
   (lem-weil-pbc-module-sheaves-colimits-forgetful,
   lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact), hence commute with cohomology
   (lem-weil-pbc-exact-functor-complex-cohomology).
4. The symmetric projection mate at a finite coefficient field is the finite-biproduct
   comparison: naturality and the tensor-unit normalization identify it on every summand
   (lem-weil-pbc-ringed-projection-mate-exact). It is therefore invertible.
5. Apply det-pe-bounded-continuity-direct-image to the actual finite-field diagram with
   its common bound a. Naturality gives the cocone equation for the projection mates.
   Thus the closure projection mate induces, on every cohomology sheaf, the colimit of
   the finite-field isomorphisms followed by the continuity isomorphism. Cohomology
   detects invertibility (lem-weil-pbc-unbounded-derived-iso-cohomology).
6. Restrict the specified coefficient-change map to E. The conservative restriction
   and its adjunction-compatible pushforward comparison
   (lem-weil-pbc-ring-sheaf-change-adjunction) identify it with the closure projection
   mate: both adjuncts are the canonical pullback/tensor identification followed by
   scalar extension of the E-coefficient counit
   (lem-weil-pbc-ringed-topoi-derived-tensor-pullback). The pulled-back inclusion is the
   same by sk-def-sfb-coefficient-change. Restriction reflects isomorphisms, so the
   specified map is invertible. Transport back to internal modules as in step 1.

Here `derivedPushHom` is the mate of `derivedComapLowerStarIso` under derived scalar
extension/restriction. Equivalently, under the derived geometric adjunction its adjunct
is `(derivedPullIso a f).inv.app (Rf_* C)` followed by extension of the geometric counit,
where a is the actual finite-subfield inclusion. This fixes the canonical map itself. -/
theorem isIso_derivedPushHom_padicAlgCl_of_boundedBelow
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (C : DerivedCategory.Plus
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E))) :
    IsIso ((derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f).app C.obj) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
