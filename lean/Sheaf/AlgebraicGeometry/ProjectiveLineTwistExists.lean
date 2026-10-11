/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-!
# Existence and uniqueness of twists on the projective line

Source: Weil conjectures blueprint, `sec-picard-framework`, `sk-thm-picard-coherence`,
node `lem-sc-p1-twist-exists`, order 636 (blueprint: lem-sc-p1-twist-exists).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveLine

/-- The twist O(d) exists, is invertible, and is unique up to unique isomorphism preserving
its two standard generators.
Source: Weil conjectures blueprint, `lem-sc-p1-twist-exists`, order 636.
Proof: take free rank-one modules on the two standard opens. On their overlap send the
first generator to t^(-d) times the second; this is an isomorphism since t is a unit
(def-sc-p1-standard). Set the self-transition maps to identities. The cocycle identities
reduce to t^d * t^(-d) = 1 and t^(-d) * t^d = 1. Glue the modules and their trivializations
using clause (2) of lem-weil-pbc-glue-sheaves-of-modules. Quasi-coherence is local and each
chart is free of rank one, so the glued module is invertible (def-sc-invertible-module).
For another twist, the generator-preserving local maps agree on the overlap. Clause (1)
of lem-weil-pbc-glue-sheaves-of-modules glues them uniquely. Glue the inverse local maps
as well to obtain a unique compatible isomorphism.
(blueprint: lem-sc-p1-twist-exists). -/
theorem exists_twistData_unique_iso (k : Type u) [Field k] (d : ℤ) :
    ∃ (L : (ProjectiveLine (Spec (.of k))).Modules)
      (T : TwistData (Spec (.of k)) d L),
      Scheme.Modules.IsInvertible L ∧
        ∀ (L' : (ProjectiveLine (Spec (.of k))).Modules)
          (T' : TwistData (Spec (.of k)) d L'),
          ∃! e : L ≅ L',
            e.hom.app (ProjectiveSpace.standardOpen _ (Spec (.of k)) ⟨0⟩) T.g₀ = T'.g₀ ∧
            e.hom.app (ProjectiveSpace.standardOpen _ (Spec (.of k)) ⟨1⟩) T.g₁ = T'.g₁ := sorry

end AlgebraicGeometry.ProjectiveLine
