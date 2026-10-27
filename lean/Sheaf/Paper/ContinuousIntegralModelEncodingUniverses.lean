/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.Paper.ContinuousModuleEncodingUniverses
public import Sheaf.Paper.IntegralStratifiedPerfectModels
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def

/-! # Finite integral models under section-action reconstruction

Source: Bhatt--Scholze, Definition 6.8.10; Stacks Project, Tags 00YV and 03EK.
(blueprint: lem-weil-pbc-continuous-integral-model-encoding-universes)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
attribute [local instance] Profinite.continuousMapRingObjOfUniverseMonObj
open CategoryTheory
open scoped CategoryTheory.Obj
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
namespace AlgebraicGeometry.Scheme

/-- Finite completed constant models give finite internal presentations in degree zero.
The coefficient isomorphism may be arbitrary: restriction along any ring isomorphism
preserves the regular module and its finite presentations.
Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3); Stacks 00YV, 03EK.
(blueprint: lem-weil-pbc-continuous-integral-model-encoding-universes).

Proof: choose the finite stratification and the covering sieve in the hypothesis.
The section-action equivalence identifies the regular internal module with the unit
module sheaf. It is exact, and therefore identifies cokernels of maps between finite
free modules. Constant module realization and scalar extension take a finite scalar
presentation to such a presentation over the completed ring. Actual-ring inverse image
and restriction to the slice are exact and preserve the regular module, so the same
holds for each model on the covering sieve. Section-action reconstruction commutes
with actual-ring inverse image: both functors are left adjoint to the same module
direct image, whose sectionwise action is scalar restriction. Localizing at an object
is restriction to its slice site. Transport each model isomorphism back through these
comparisons. The sieve generates a pro-etale covering family, and its finite
presentations give exactly the archived local-finite-presentation condition on each
stratum. Restriction along c and its inverse preserves all these presentations.
The argument includes zero ranks, torsion scalar modules, and the empty scheme. -/
theorem continuousIntegralModelEncodingUniverses (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) [IsNoetherian T]
    (c : pbcAdicCompletion T (pbcIntegralDatum l E) ≅
      latticeCoefficientSheaf T (Padic.coefficientExtensionIntegers l E))
    (M : pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E)))
    (hM : IsIntegralStratifiedFinitelyPresented T (pbcIntegralDatum l E) M) :
    IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousCoefficientRingObj
        (Padic.coefficientExtensionIntegers l E)) T)
      ((completedContinuousModuleEquivalence l E T c).inverse.obj M) := by sorry

end AlgebraicGeometry.Scheme
