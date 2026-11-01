/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.SitePerfectComplex
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-! # Internal Hom through the coefficient dual

Source: current Weil conjectures blueprint, `sec-six-functors/sk-prop-sf-dualizable-biduality/`
`prop-sf-dualizable-hom.md`, order 3499 (blueprint: prop-sf-dualizable-hom).

The declarations state the pro-étale condensed-coefficient assertion and its finite
coefficient small-étale realization.  The displayed map is the existing canonical
`ihomUnitTensorToIhom`: its source is the coefficient dual tensored with the target,
and its target is the derived internal Hom.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-! The pulled-back coefficient ring uses the canonical ring-object structure induced by
`p_X^*`; the local instance below keeps the derived module category notation independent
of any local Brown-hypothesis bundle. -/

section

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  (X : Scheme.{u})

local instance condensedRingObj_monObj : MonObj (condensedRingObj Λ X) :=
  Functor.monObjObj (F := upperStarFromPoint X) Λ

/-! The hypotheses `hK` and `hM` render membership in the bounded constructible
finite-Tor subcategory `D^b_ctf(X, Λ)`; `hPerfect` renders the local bounded
finite-projective hypothesis. -/

/-- In the current condensed coefficient-site interpretation, a locally bounded
finite-projective object is dualizable: for every bounded constructible finite-Tor
target, coefficient dual tensor target maps isomorphically to derived internal Hom.

Source: current Weil conjectures blueprint,
`sec-six-functors/sk-prop-sf-dualizable-biduality/prop-sf-dualizable-hom.md`,
statement and proof steps 1--5 (blueprint: prop-sf-dualizable-hom).

Proof (node proof, Stacks 08JJ).
1. The internal Hom `H = RHom_R` is the right adjoint of the same K-flat derived tensor, by
   uniqueness of adjoints; the displayed map is the evaluation
   `e : M ⊗ᴸ H(K, R) ⟶ H(K, M)` after symmetry. On each chart of the cover choose a bounded
   representative `P` of `K` whose terms are retracts of finite free modules.
2. On a chart put `D = Hom^•(P, R[0])`. The terms of `P` have exact Hom functors and finite
   free retract duals, so `D` represents `H(K, R)` and `Hom^•(P, F)` represents `H(K, M)`
   for a K-flat flat-term representative `F` of `M`; `D` is bounded flat, hence K-flat.
3. Termwise all-target evaluation `B ⊗ (P^i)^∨ ≅ Hom(P^i, B)`, assembled with signs, gives
   a chain isomorphism `Tot(F ⊗ D) ≅ Hom^•(P, F)`, `y ⊗ φ ↦ (x ↦ y φ(x))`.
4. The representative normalization of the ringed-site duality maps identifies this chain
   isomorphism with `e` on the chart, compatibly with restriction to the chart.
5. Restriction is exact, so the cohomology sheaves of the cone of `e` vanish on a cover and
   hence vanish; `e` and therefore the displayed map are isomorphisms. -/
theorem sitePerfect_dualizable_hom
    [IsCommMonObj Λ]
    (K M : DerivedCategory
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)))
    (hK : constantModelBoundedConstructible Λ X K ∧
      DerivedCategory.finiteTorAmplitude _ K)
    (hM : constantModelBoundedConstructible Λ X M ∧
      DerivedCategory.finiteTorAmplitude _ M)
    (hPerfect : IsPerfectOnCoefficientSite Λ X K) :
    IsIso (MonoidalClosed.ihomUnitTensorToIhom K M) := by
  sorry

end

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.Etale.DerivedCategory

/-! For a finite coefficient ring the same assertion is stated on the small étale site,
using the recorded bounded-constructible predicate `isBoundedConstructible`
(def-weil-pbc-constructible-complexes) and the finite-Tor predicate `hasTorAmplitudeIn`
(def-kun-tor-amplitude). -/

variable {A : Type (u + 1)} [CommRing A] [Finite A] {X : Scheme.{u}}

/-- The finite-coefficient small-étale realization of
`prop-sf-dualizable-hom`.  Its hypotheses spell out the bounded constructible
finite-Tor subcategory, and `IsSitePerfect` is the local bounded
finite-projective condition on the coefficient site.

Source: current Weil conjectures blueprint,
`sec-six-functors/sk-prop-sf-dualizable-biduality/prop-sf-dualizable-hom.md`,
finite-coefficient small-étale clause (blueprint: prop-sf-dualizable-hom).

Proof (node proof, step 5): steps 1--5 of `sitePerfect_dualizable_hom` use only statements
about an arbitrary small ringed site with commutative coefficient sheaf; run on the small
étale site with the constant coefficient sheaf of `A`, they give this assertion: local
finite-free-retract representatives, their K-flat termwise duals, the signed termwise
evaluation chain isomorphism, its identification with the canonical map on each chart,
and local detection of the acyclic cone. -/
theorem sitePerfect_dualizable_hom_etale
    (K M : DerivedCategoryModule A X)
    (hK : DerivedCategory.isBoundedConstructible A X K ∧
      ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A X a b K)
    (hM : DerivedCategory.isBoundedConstructible A X M ∧
      ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A X a b M)
    (hPerfect : IsSitePerfect K) :
    IsIso (MonoidalClosed.ihomUnitTensorToIhom K M) := by
  sorry

end AlgebraicGeometry.Etale.DerivedCategory
