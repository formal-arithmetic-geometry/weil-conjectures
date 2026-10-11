/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Admissible subalgebras in the Popescu construction

Source: Stacks Project, proof of Tag 07FH
(blueprint: def-weil-pbc-popescu-admissible-subalgebra).
-/

universe uA vA

namespace Subalgebra

/-- An admissible subalgebra is Artinian local, essentially of finite type over the base,
flatly included in the ambient ring, with its maximal ideal generating the specified ambient
ideal. Source: Stacks Project, proof of Tag 07FH
(blueprint: def-weil-pbc-popescu-admissible-subalgebra). -/
def IsPopescuAdmissible {k : Type uA} {B : Type vA} [Field k] [CommRing B] [Algebra k B]
    (A : Subalgebra k B) (m : Ideal B) : Prop :=
  IsArtinianRing A ∧ Algebra.EssFiniteType k A ∧
    ∃ (_ : IsLocalRing A),
      A.val.toRingHom.Flat ∧ (IsLocalRing.maximalIdeal A).map A.val.toRingHom = m

end Subalgebra
