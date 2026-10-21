/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.Paper.FiniteDiscreteOrdinaryEncoding

/-! # Finite discrete coefficient comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- Tensor products and Tor intervals under the normalized section-action encoding.
Source: blueprint coefficient-identification proof, steps 5--7; Stacks Tags 08BJ and 08FZ.
(blueprint: lem-sf-finite-discrete-encoding-tensor-tor).

Proof: section-action identifies relative tensor products by the universal property of
balanced bilinear maps. Scalar restriction along the normalized coefficient isomorphism
and restriction to constant sections preserve these balancing relations and the unit.
The pure-tensor maps respect associativity and both unitors. Termwise extension preserves
coproducts, so the same maps identify direct-sum total tensors and their signed
differentials. An additive equivalence preserves and reflects acyclicity; transporting
the tensor tests therefore preserves and reflects K-flatness. Apply the exact monoidal
derived-equivalence theorem to obtain the monoidal structure on the actual termwise
extension. For intrinsic module sheaves compute derived tensor on any K-flat resolution;
the comparison identifies it with the generic derived tensor. All degree-zero test
modules correspond under either equivalence. The homology comparison consequently
identifies vanishing in every ordered interval. Finite Tor amplitude follows by enlarging
any witnessing interval to an ordered one and applying the same argument to the inverse.
This includes the zero ring and the zero object. -/
theorem encoding_tensor_tor [Finite A] [DiscreteTopology A]
    (T : Scheme.{u}) (e : Encoding A T) :
    Nonempty (e.fixedDerived.functor.Monoidal) ∧
    (∀ (K : DerivedCategory (Internal A T)) (a b : ℤ), a ≤ b →
      (DerivedCategory.torAmplitudeIn _ a b K ↔
        Scheme.HasProEtaleTorAmplitude T A (e.ordinaryDerived.functor.obj K) a b)) ∧
    (∀ (K : DerivedCategory (Internal A T)) (a b : ℤ), a ≤ b →
      (DerivedCategory.torAmplitudeIn _ a b K ↔ DerivedCategory.torAmplitudeIn _ a b
        (e.fixedDerived.functor.obj K))) := by sorry

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
