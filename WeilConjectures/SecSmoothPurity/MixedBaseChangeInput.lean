/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.MixedBaseChangeOperations

/-! Constructible inputs and invertible compact-support exchange. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

/-- Pullback preserves the intrinsic bounded constructible finite-Tor inputs, and the
specified compact-support exchange is invertible on them.
Source: blueprint det-sp-mixed-base-change, Step 4; finite proper base change and
constructible pullback, det-thm-sf-ctf-stability-direct-images clause (1)
(blueprint: lem-sp-mixed-base-change-input).

Proof: finite-type schemes over a field are Noetherian. Pullback of a finite locally
constant stratification is constructible. Exact inverse image preserves cohomological
bounds, and its canonical tensor comparison preserves the same Tor interval. Thus
pullback sends each intrinsic Dctf object to Dctf. For compact-support exchange, choose
its bounded etale antecedent by finite-ring constructible derived origin. Extend this
antecedent by zero along cpt.i, using the exact open-extension comparison. Proper
base change makes the proper exchange at this open extension invertible. The normalized
counit-mate transport identifies that exchange with directImageConstantExchange. The
open factor mixedOpenBaseChangeIso is already an isomorphism by construction. Their
composite is exactly mixedCompactSupportExchange, hence is invertible. This argument
also covers empty schemes and zero coefficient rings, and requires no flatness of a
coefficient change. -/
theorem mixedBaseChange_input
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {X Y X' : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [X'.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of k))]
    [QuasiCompact (X' ↘ Spec (.of k))] [IsSeparated (X' ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (cpt : Compactification f) [cpt.Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (cpt.Z ↘ Spec (.of k))]
    [QuasiCompact (cpt.Z ↘ Spec (.of k))] [IsSeparated (cpt.Z ↘ Spec (.of k))]
    [cpt.i.IsOver (Spec (.of k))] [cpt.g.IsOver (Spec (.of k))]
    {Y' : Scheme.{u}} [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))]
    [QuasiCompact (Y' ↘ Spec (.of k))] [IsSeparated (Y' ↘ Spec (.of k))]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [g'.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of k))]
    [g.IsOver (Spec (.of k))]
    (sq : ChosenCartesianSquare g' f' f g)
    (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (M : proEtaleDerivedCategory X A) (hM : spFiniteConstructibleTor X A M) :
    spFiniteConstructibleTor X' A
        ((proEtaleConstantRingDerivedPullback A g').obj M) ∧
      IsIso ((mixedCompactSupportExchange A sq cpt).app M) := by sorry

end AlgebraicGeometry.ProEtale
