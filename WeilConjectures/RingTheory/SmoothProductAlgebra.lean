/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.Algebra.Algebra.Prod

import Mathlib.RingTheory.Smooth.Pi
import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
import Mathlib.Algebra.Ring.Fin

/-!
# A product of two smooth algebras over one base is smooth

## References

* [Stacks, Tag 0GIF]
-/

@[expose] public section

universe u v w

namespace Algebra.Smooth

/-- A binary product of smooth `R`-algebras, equipped with `Prod.algebra`, is smooth over `R`. -/
theorem prod (R : Type u) (S' : Type v) (S'' : Type w)
    [CommRing R] [CommRing S'] [CommRing S''] [Algebra R S'] [Algebra R S'']
    [Smooth R S'] [Smooth R S''] : Smooth R (S' × S'') := by
  let A : Fin 2 → Type (max v w)
    | ⟨0, _⟩ => ULift.{w} S'
    | ⟨1, _⟩ => ULift.{v} S''
  let : (i : Fin 2) → CommRing (A i)
    | ⟨0, _⟩ => inferInstance
    | ⟨1, _⟩ => inferInstance
  let : (i : Fin 2) → Algebra R (A i)
    | ⟨0, _⟩ => inferInstance
    | ⟨1, _⟩ => inferInstance
  have : (i : Fin 2) → Smooth R (A i)
    | ⟨0, _⟩ => Smooth.of_equiv (ULift.algEquiv (R := R)).symm
    | ⟨1, _⟩ => Smooth.of_equiv (ULift.algEquiv (R := R)).symm
  have : Smooth R ((i : Fin 2) → A i) := {}
  let e : ((i : Fin 2) → A i) ≃ₐ[R] A 0 × A 1 :=
    { RingEquiv.piFinTwo A with commutes' := fun _ ↦ rfl }
  have : Smooth R (ULift.{w} S' × ULift.{v} S'') := Smooth.of_equiv e
  exact Smooth.of_equiv (AlgEquiv.prodCongr
    (ULift.algEquiv (R := R)) (ULift.algEquiv (R := R)))

end Algebra.Smooth
