/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrdinaryCompactificationCoherence
public import WeilConjectures.AlgebraicGeometry.MixedBaseChangeInput
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
import WeilConjectures.AlgebraicGeometry.MixedBaseChangeOperations

/-!
# Scalar extension and chosen compact-support exchange

Source: latest blueprint, thm-pur-finite-reduction-of-purity.proof.md, Step 4,
base-change coherence; det-sp-reduction-compatibilities.proof.md, (3), compatibility
with b (blueprint: lem-pur-compact-scalar-base-change).

All operations use ordinary uncompleted constant-ring module derived categories on
small pro-etale sites. Both compactifications are independent of coefficients.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

section Geometry

variable (ℓ pchar : ℕ) [Fact ℓ.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
  (k : Type u) [Field k] [CharP k pchar]
  {X Y X' Y' : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))]
  [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))]
  [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))]
  [QuasiCompact (X' ↘ Spec (.of k))] [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))]
  [QuasiCompact (Y' ↘ Spec (.of k))] [IsSeparated (Y' ↘ Spec (.of k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
  (c : Compactification f) [c.Z.Over (Spec (.of k))]
  [LocallyOfFiniteType (c.Z ↘ Spec (.of k))]
  [QuasiCompact (c.Z ↘ Spec (.of k))] [IsSeparated (c.Z ↘ Spec (.of k))]
  [c.i.IsOver (Spec (.of k))] [c.g.IsOver (Spec (.of k))]
  (h : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
  [h.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  (sq : ChosenCartesianSquare h f' f g)

/-- Exact inverse image on these Dctf inputs, with its automatic membership certificate.
The existing input theorem imposes no smoothness condition on f.
Source: latest blueprint, finite reduction Step 4
(blueprint: lem-pur-compact-scalar-base-change). -/
def compactExchangePullObject (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (M : spFiniteConstructibleTorCategory X A) : spFiniteConstructibleTorCategory X' A :=
  ⟨(proEtaleConstantRingDerivedPullback A h).obj M.obj,
    (mixedBaseChange_input ℓ pchar hp hℓ k f c h f' g sq A hA M.obj M.property).1⟩

/-- The specified proper/open exchange followed by the normalized comparison to the
independently chosen primed compactification. Source: latest blueprint finite reduction
Step 4 (blueprint: lem-pur-compact-scalar-base-change). -/
def compactChosenExchange (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (d : Compactification f') (M : spFiniteConstructibleTorCategory X A) :
    (proEtaleConstantRingDerivedPullback A g).obj
        ((reductionCompactSupport A c.i c.g).obj M.obj) ⟶
      (reductionCompactSupport A d.i d.g).obj
        ((proEtaleConstantRingDerivedPullback A h).obj M.obj) := by
  letI : IsNoetherian X' := isNoetherian_of_locallyOfFiniteType (X' ↘ Spec (.of k))
  letI : IsNoetherian Y' := isNoetherian_of_locallyOfFiniteType (Y' ↘ Spec (.of k))
  letI : QuasiCompact f' := inferInstance
  exact (mixedCompactSupportExchange A sq c).app M.obj ≫
    (ordinaryCompactificationComparison A (mixedPullbackCompactification sq c) d).hom.app
      (compactExchangePullObject ℓ pchar hp hℓ k f c h f' g sq A hA M)

end Geometry

end AlgebraicGeometry.ProEtale
