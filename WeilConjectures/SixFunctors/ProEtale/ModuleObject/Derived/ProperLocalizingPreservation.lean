/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperImageLocalizingProper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicProperConstructibleCohomology
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarCoproducts

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
/-- Characteristic-free proper-image preservation and coproduct interface.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-thm-purity-transport/sk-thm-purity-transport.proof.md, General-field localizing tools,
Steps 2--4. The proof requires a uniform characteristic-free proper-heart bound and the
finite-truncation coproduct dévissage for native condensed coefficients. The intended proof is:
(1) apply the characteristic-free proper-heart finiteness theorem to every finite
constant-model generator and obtain a uniform lower and upper cohomological bound (the
existing raw finite-extension and algebraic-closure bounds must first be transported to
the native condensed coefficient `Λ` supplied by `hΛ`);
(2) use finite truncations and the triangulated right-derived pushforward to extend the
generator statement to the whole bounded constructible finite-Tor class;
(3) form the inverse-image localizing subcategory of objects whose pushforward is in the
target closure and use closure minimality to obtain preservation of the source closure;
(4) apply the heart coproduct criterion to finite constant models, compare the ambient
coproduct with the pushforward coproduct, and use the same minimality argument to obtain
all Type (u+1)-indexed coproducts. The generic proper restriction is stated one universe
higher, so its coproduct conclusion also needs a universe-lowering transport. The empty
family is handled by the zero object.
(blueprint: lem-dla1-general-field-proper-preservation). -/
theorem properLocalizingPreservation (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [PerfectField k] [Fact (ringChar k ≠ ℓ)]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    {T S : Scheme.{u}} [T.Over (Spec (CommRingCat.of k))]
    [S.Over (Spec (CommRingCat.of k))]
    [IsSeparated (T ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (T ↘ Spec (CommRingCat.of k))]
    [IsSeparated (S ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (S ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (S ↘ Spec (CommRingCat.of k))]
    (p : T ⟶ S) [p.IsOver (Spec (CommRingCat.of k))] [IsProper p] :
    (∀ K, localizingClosureProEtale Λ T K → localizingClosureProEtale Λ S
      ((moduleObjectDerivedPushforward Λ p).obj K)) ∧
    (∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
      ((localizingClosureProEtale Λ T).ι ⋙ moduleObjectDerivedPushforward Λ p)) := by
  sorry
end AlgebraicGeometry.ProEtale.CondensedRing
