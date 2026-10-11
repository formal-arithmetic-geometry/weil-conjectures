/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.CategoryTheory.Subobject.Basic

/-! # Ascending chains of quasi-coherent submodules

Source: Stacks Project, Cohomology of Schemes, Lemma 30.10.1 (Tag 01Y8), and the
maximal-element form used in Tags 088C and 088E
(blueprint: lem-weil-pbc-noetherian-acc-quasi-coherent).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- On a Noetherian scheme, ascending sequences of quasi-coherent submodules of a coherent
module stabilize. Every nonempty set of these submodules, or of quasi-coherent ideal
sheaves (`X.IdealSheafData`), has a maximal element under inclusion.

Source: Stacks Project, Tag 01Y8; maximal-element form as used in Tags 088C and 088E
(blueprint: lem-weil-pbc-noetherian-acc-quasi-coherent).

Proof:
1. Local Noetherianness and quasi-compactness give a finite affine cover with Noetherian
   section rings [pqf-def-locnoeth, def-weil-pbc-noetherian-ring, def-pc-scheme].
2. Coherence gives finite presentation locally, hence quasi-coherence and finite generation
   of sections on each affine in the cover [pqf-def-coherent,
   lem-weil-pbc-quasi-coherent-finite-type-affine, def-weil-finitely-generated-module].
   For the structure sheaf, the section ring is generated over itself by one.
3. Comparable quasi-coherent submodules agreeing on the cover agree everywhere: restriction
   preserves quasi-coherence, the affine tilde-global-sections counits identify their
   restrictions, and the sheaf gluing axiom gives global equality
   [lem-weil-pbc-module-restriction-open-immersion-colimits,
   lem-weil-pbc-affine-tilde-gamma-adjunction, def-weil-sheaf-of-modules-category].
4. The sections of an ascending chain stabilize on each affine by Noetherianness of the
   finite ambient module [lem-weil-pbc-noetherian-finite-module-acc]. Take the maximum of
   the finitely many stabilization indices and apply step 3.
5. For a nonempty set, successively retain the submodules whose sections are a chosen
   maximal element on each affine [lem-weil-pbc-noetherian-finite-module-acc]. Each retained
   set is nonempty. A member of the final set is maximal: any larger member of the original
   set agrees on the cover by successive maximality, then agrees globally by step 3.
   The same argument applies to quasi-coherent ideal sheaves, whose ideals on the affines
   of the cover determine them, using the last sentence of step 2. -/
theorem noetherian_quasicoherent_submodules (X : Scheme.{u}) [IsNoetherian X]
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hF : RingedSpace.IsCoherent X.toRingedSpace F) :
    (∀ (G : ℕ → Subobject F), Monotone G →
      (∀ n, (G n : SheafOfModules.{u} (moduleRings X.toRingedSpace)).IsQuasicoherent) →
      ∃ n, ∀ m, n ≤ m → G m = G n) ∧
    (∀ S : Set (Subobject F), S.Nonempty →
      (∀ G ∈ S, (G : SheafOfModules.{u} (moduleRings X.toRingedSpace)).IsQuasicoherent) →
      ∃ G ∈ S, ∀ H ∈ S, G ≤ H → H = G) ∧
    (∀ S : Set X.IdealSheafData, S.Nonempty →
      ∃ I ∈ S, ∀ J ∈ S, I ≤ J → J = I) := by
  sorry

end AlgebraicGeometry
