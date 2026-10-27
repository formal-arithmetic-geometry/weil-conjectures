/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q124
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.GroupTheory.Index
public import Sheaf.FieldTheory.FieldTower
import Mathlib.FieldTheory.Fixed
import Mathlib.LinearAlgebra.Dimension.Free
import WeilConjectures.FieldTheory.PurelyInseparablePthRootTower

/-!
# Constants fixed by a Sylow subgroup

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose X, 2.3 Step 2,
printed p.151, diagram (2.c); Stacks Project, Fields, Tags 09I3, 09I1, 09G9, 09HI.
(blueprint: lem-sfb-sylow-constants-field-degree)

The action need not be faithful. Equality of the sets of underlying functions identifies the
full automorphism group over the subgroup's fixed field with the actual image of the subgroup.
-/

@[expose] public section

universe u v w

namespace FieldExtension

/-- The subgroup's fixed field has finite degree prime to `ℓ` over the base, and the upper
extension is finite Galois with automorphism group exactly the image of the subgroup.
Source: ILO, Expose X, 2.3 Step 2, printed p.151, diagram (2.c).
(blueprint: lem-sfb-sylow-constants-field-degree)

Proof plan:
1. Put `H = ρ.range` and `J = L.map ρ`. The fixed-element equations identify their fixed
   fields with `E = K^G` and `F = K^L`. Both are intermediate fields of the finite extension
   `K/e`, hence finite over `e`; also `F/E` is finite.
2. Apply lem-wf-finite-field-action-fixed-degree to the faithful image groups `H` and `J`.
   Thus `K/E` and `K/F` are finite Galois of degrees `|H|` and `|J|`. By
   lem-weil-pbc-finite-galois-fixed-field, `Aut_F(K)` has `|J|` elements. The injection
   from `J` into that group, preserving underlying functions, is therefore surjective.
   Conversely each element of `J` fixes `F` by the definition of the fixed field. This
   proves the equality of the two sets of functions in the conclusion.
3. The tower law lem-weil-pbc-field-degree-multiplicativity gives
   `|H| = |J| [F:E]`. Apply lem-sfb-surjective-subgroup-image-index to the surjection
   `G → H`: `|H| = |J| [H:J]` and `[H:J]` divides `[G:L]`. Since `|J|` is positive,
   cancellation gives `[F:E] = [H:J]`, which is prime to `ℓ`.
4. In characteristic zero, pure inseparability gives `E = e`, of degree one. In positive
   characteristic `p`, lem-weil-pbc-purely-inseparable-pth-root-tower and repeated tower
   laws give `[E:e] = p^n`, including the empty tower. Since `p` and `ℓ` are distinct
   primes, `ℓ` does not divide `[E:e]`.
5. The tower law gives `[F:e] = [F:E] [E:e]`. Neither factor is divisible by the prime
   `ℓ`, so neither is the product. Finiteness and the Galois-group assertion were obtained
   in steps 1 and 2. The power-order hypothesis on `L` is retained as in the source;
   the degree calculation itself uses only its prime-to-`ℓ` index.
-/
theorem sylow_fixedField_degree
    (e : Type u) (K : Type v) [Field e] [Field K] [Algebra e K]
    [FiniteDimensional e K] (ℓ : ℕ) (hℓ : Nat.Prime ℓ) (hchar : ℓ ≠ ringChar e)
    (G : Type w) [Group G] [Finite G] (ρ : G →* (K ≃ₐ[e] K))
    (hinsep : IsPurelyInseparable e (IntermediateField.fixedField ρ.range))
    (L : Subgroup G) (hpower : ∃ n : ℕ, Nat.card L = ℓ ^ n) (hindex : ¬ ℓ ∣ L.index) :
    Module.Finite e (IntermediateField.fixedField (L.map ρ)) ∧
      (¬ ℓ ∣ Module.finrank e (IntermediateField.fixedField (L.map ρ))) ∧
      Module.Finite (IntermediateField.fixedField (L.map ρ)) K ∧
      IsGalois (IntermediateField.fixedField (L.map ρ)) K ∧
      Set.range (fun σ : K ≃ₐ[IntermediateField.fixedField (L.map ρ)] K ↦ (σ : K → K)) =
        Set.range (fun g : L ↦ (ρ g : K → K)) := by
  sorry

end FieldExtension
