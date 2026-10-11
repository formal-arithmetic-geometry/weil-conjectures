/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import WeilConjectures.AlgebraicGeometry.Picard.Group
import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-!
# The Picard group of a field

Source: the blueprint of the Weil conjectures, chapter `sec-picard-framework`, unit
`sk-def-picard-pic`, node 802 (blueprint: lem-pc-pic-of-field).
-/

universe u

namespace AlgebraicGeometry.Scheme

/-- (blueprint: lem-pc-pic-of-field) The Picard group of the spectrum of a field is trivial:
every invertible module is isomorphic to the structure sheaf. An invertible module is locally
free of rank one. Since the spectrum has just one point, a local rank-one trivialization is
global. Equivalently, its sections form a one-dimensional vector space over the field;
choosing a nonzero vector identifies them with the field and the sheaf with the structure
sheaf. Thus every Picard class is the identity. Source: the blueprint, node 802, proof. -/
theorem pic_of_field (k : Type u) [Field k] :
    Subsingleton (Spec (.of k)).Pic ∧
      ∀ (L : (Spec (.of k)).Modules) [L.IsInvertible],
        Nonempty (L ≅ SheafOfModules.unit (Spec (.of k)).ringCatSheaf) := by
  sorry

end AlgebraicGeometry.Scheme
