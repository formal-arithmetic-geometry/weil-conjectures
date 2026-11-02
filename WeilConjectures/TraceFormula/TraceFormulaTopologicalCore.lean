/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.TraceFormulaCoefficientConventions.TraceFormulaCoefficientConventions
import WeilConjectures.AlgebraicGeometry.UniversallyHomeomorphIntegral
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.TopInvariance
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Ambient derived topological invariance

Source: blueprint i-topology, exact module equivalence and derived descent paragraphs.
(blueprint: trace-formula-topological-core).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The ambient derived equivalence, before any constructibility restriction.
Source: blueprint i-topology, paragraphs 1--3; Stacks Tags 09AB and 04DF.
(blueprint: trace-formula-topological-core).

Proof: topological invariance gives an equivalence of set-valued pro-etale sheaves.
Lift it to finite coefficient modules, using the canonical constant-ring realization.
The inverse-image functor and its inverse are exact, so their termwise functors
preserve quasi-isomorphisms and descend to the derived localizations. The unit and
counit descend too, with their triangle identities. The exact inverse image is the
recorded finite derived pullback. Since the inverse is exact and preserves
K-injectives, its derived functor agrees with the canonical derived direct image.
No finite-Tor or constructibility condition is used in this assertion. -/
theorem finiteUniversalHomeomorphism_traceFormula_core
    (T : TraceFormulaCoefficientConventions.{u})
    {X Y : Scheme.{u}} (r : X ⟶ Y) [IsFinite r]
    (hr : (topologically IsHomeomorph).universally r) :
    ∃ e : proEtaleDerivedCategory Y T.coefficientRing ≌
        proEtaleDerivedCategory X T.coefficientRing,
      Nonempty (e.functor ≅ T.derivedPullback r) ∧
      Nonempty (e.inverse ≅ proEtaleConstantDerivedDirectImage r T.coefficientRing) := by
  let : Finite T.coefficientRing := Padic.finite_coefficientExtensionRing
    T.coefficients.l T.coefficientField T.level T.level_pos
  let : IsUniversalHomeomorphism r :=
    isUniversalHomeomorphism_of_universally_isHomeomorph r hr
  let : (AlgebraicGeometry.ProEtale.upperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} T.coefficientRing)) r).IsEquivalence :=
    AlgebraicGeometry.ProEtale.isEquivalence_upperStar_of_isUniversalHomeomorphism _ r
  let : (sfIntrinsicPullback T.coefficientRing r).IsEquivalence := by
    unfold sfIntrinsicPullback sfIntrinsicTransport
    infer_instance
  let e := (sfIntrinsicDerivedPullback T.coefficientRing r).asEquivalence
  have hp : sfIntrinsicDerivedPullback T.coefficientRing r ≅ T.derivedPullback r := by
    rcases T with ⟨D, C, E, n, hn, X₀, hf, hq, hs⟩
    cases n with
    | zero => omega
    | succ n => exact Iso.refl _
  refine ⟨e, ⟨hp⟩, ⟨?_⟩⟩
  exact e.toAdjunction.rightAdjointUniq
    (Adjunction.mapDerivedCategoryRightDerivedAdjunction
      (sfIntrinsicConstantModuleAdjunction r T.coefficientRing))

end WeilConjectures
