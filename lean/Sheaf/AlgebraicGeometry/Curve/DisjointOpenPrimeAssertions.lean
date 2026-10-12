/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-! # Decomposition of extension by zero on disjoint opens -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry.Etale

namespace AlgebraicGeometry.IsCurve

/-- Assertions for extension from a finite union of disjoint opens are componentwise.
Source: Stacks Project, Theorem 03SC, proof, fourth paragraph, and Lemma 0A5C
(blueprint: lem-pbc-q1-disjoint-open-prime-assertions).

Proof: Put W = ⋃ a, U_a and let i_a : U_a → W denote the inclusions. Their counits, followed
by extension by zero to X, define the canonical map from the finite direct sum of the
j_a! (F|U_a) to j_! (F|W). On each geometric stalk this is the identity of F at the unique
open containing the point, or the identity of zero if the point is outside W. Geometric
stalks are conservative, so this map is an isomorphism. Every summand is constructible,
by the open-closed stratification, and killed by r. The cohomology functors and inverse image
are additive, so cohomology of the finite sum is the finite sum of cohomologies, and each
pullback or restriction map is the direct sum of the summand maps. Such a sum is zero or
finite exactly when every summand is, and is bijective or surjective exactly when all
summand maps are. These statements prove C1-C8 separately. The affine and proper hypotheses
concern the same X. For the torsion hypotheses, if r is different from char k all summands
have invertible torsion, and if r equals char k all are primary; in the exceptional cases
the summands to which a different-primary or invertible-torsion condition applies are zero,
so their assertions are automatic. This proves both implications for the conditional
assertions. When n = 0, extension from the empty open is zero and the right side is vacuous. -/
theorem assertions_iff_disjoint_open_prime (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (r : ℕ) [Fact r.Prime] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsConstructibleSheaf F] (hF : r • 𝟙 F = 0)
    (n : ℕ) (U : Fin n → X.Opens)
    (hU : Pairwise (fun a b ↦ Disjoint (U a : Set X) (U b))) :
    IsCurve.Assertions Λ f
      (((⨆ a, U a).ι)_!open[ModuleCat.{u + 1} Λ].obj
        (((⨆ a, U a).ι)^*[ModuleCat.{u + 1} Λ].obj F)) ↔
      ∀ a, IsCurve.Assertions Λ f
        (((U a).ι)_!open[ModuleCat.{u + 1} Λ].obj
          (((U a).ι)^*[ModuleCat.{u + 1} Λ].obj F)) := by sorry

end AlgebraicGeometry.IsCurve
