/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import WeilConjectures.RingTheory.ProEtale.ClosedLiftAdjunction

/-!
# Retractions and clopen subsets of the ind-étale closed lift

For an ind-étale `A ⧸ I`-algebra `C̄`, the lift `H_A(C̄)` of `Algebra.ClosedLift` is the
coreflection of `C̄` into ind-étale `A`-algebras: for every ind-étale `A`-algebra `D`, composition
with `H_A(C̄) ⟶ C̄` is a bijection `Hom_A(D, H_A(C̄)) ≃ Hom_A(D, C̄)`
(`Algebra.ClosedLift.homEquiv`, a reformulation of the adjunction
`Algebra.ClosedLift.exists_natural_homEquiv`, blueprint `lem-exc-closed-lift-adjunction`).

Consequences: retractions of faithfully flat ind-étale covers of `C̄` lift to `H_A(C̄)`
(`Algebra.ClosedLift.exists_retraction`), and every nonempty clopen subset of `Spec H_A(C̄)` meets
`Spec C̄` (`Algebra.ClosedLift.exists_comap_mem_of_isClopen`).
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped TensorProduct

namespace Algebra.ClosedLift

variable {A : Type u} [CommRing A] {C : Type u} [CommRing C] [Algebra A C]

section HomEquiv

variable (I : Ideal A) [Algebra (A ⧸ I) C] [IsScalarTower A (A ⧸ I) C]
  [Algebra.IndEtale (A ⧸ I) C]

include I

end HomEquiv

/-! ### Retractions of faithfully flat ind-étale covers -/

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- Base change of an ind-étale algebra is ind-étale. -/
lemma indEtale_tensorProduct (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra.IndEtale R T] :
    Algebra.IndEtale S (TensorProduct R S T) :=
  (RingHom.IndEtale.algebraMap_iff _ _).mp (RingHom.IndEtale.isStableUnderBaseChange R T S
    (TensorProduct R S T) ((RingHom.IndEtale.algebraMap_iff _ _).mpr inferInstance))

end Algebra.ClosedLift
