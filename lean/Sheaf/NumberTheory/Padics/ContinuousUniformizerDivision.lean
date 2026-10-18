/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NI
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Topology.Algebra.Order.Field

/-!
# Continuous division by a uniformizer power

Source: Hemo–Richarz–Scholbach, proof of Theorem 6.12(2), finite `E` case,
pp. 18–19 (blueprint: lem-sfb-continuous-uniformizer-division).

The statement records the continuous integral division and the local unit
inversion used in the continuous Smith elimination argument. The valuation topology
of `E` is the metric topology of the recorded absolute value
`Padic.coefficientExtensionAbsoluteValue` (through `AbsoluteValue.toNormedField`,
as in the project's `coefficientExtensionNormedField`); the integer ring and the
range `π^e A` carry the subspace topologies.
-/

@[expose] public section

universe u v

namespace Padic

/-- Multiplication by a power of the chosen uniformizer is a homeomorphism onto
its image, and divisible continuous functions admit a unique continuous quotient.
If the value at a point is a unit multiple of that power, the quotient is locally
unit-valued and its inverse is continuous there.

Source: Hemo–Richarz–Scholbach, proof of Theorem 6.12(2), finite `E` case,
pp. 18–19 (blueprint: lem-sfb-continuous-uniformizer-division).

The quotient is unique among all continuous `q'` with `π^e q' = f`, independently
of the local unit clause.

Proof: multiplication by a nonzero uniformizer power is a homeomorphism of the
ambient valued field, and restriction to the valuation ring gives the first
clause. Compose a continuous divisible function with the inverse restriction to
obtain the unique quotient. Cancellation proves the value at the chosen point.
The unit locus is open in the valuation topology, and inversion is continuous on
the ambient field's nonzero locus, giving the final local assertion.
-/
theorem continuous_uniformizer_division
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (e : ℕ) :
    (∃ h : @Homeomorph (Padic.coefficientExtensionIntegers l E)
        {x : E // x ∈ Set.range
          (fun a : Padic.coefficientExtensionIntegers l E =>
            (Padic.coefficientExtensionUniformizer l E : E) ^ e * (a : E))}
        (TopologicalSpace.induced
          (fun x : Padic.coefficientExtensionIntegers l E => (x : E))
          (@UniformSpace.toTopologicalSpace E
            (coefficientExtensionAbsoluteValue l E).toNormedField.toUniformSpace))
        (TopologicalSpace.induced Subtype.val
          (@UniformSpace.toTopologicalSpace E
            (coefficientExtensionAbsoluteValue l E).toNormedField.toUniformSpace)),
      ∀ a : Padic.coefficientExtensionIntegers l E,
        h a = ⟨(Padic.coefficientExtensionUniformizer l E : E) ^ e * (a : E),
          ⟨a, rfl⟩⟩) ∧
    ∀ {T : Type v} [TopologicalSpace T]
      (f : T → Padic.coefficientExtensionIntegers l E),
      @Continuous T (Padic.coefficientExtensionIntegers l E) _
        (TopologicalSpace.induced
          (fun x : Padic.coefficientExtensionIntegers l E => (x : E))
          (@UniformSpace.toTopologicalSpace E
            (coefficientExtensionAbsoluteValue l E).toNormedField.toUniformSpace))
        f →
        (∀ t : T, (f t : E) ∈ Set.range
          (fun a : Padic.coefficientExtensionIntegers l E =>
            (Padic.coefficientExtensionUniformizer l E : E) ^ e * (a : E))) →
        ∃ q : T → Padic.coefficientExtensionIntegers l E,
          @Continuous T (Padic.coefficientExtensionIntegers l E) _
            (TopologicalSpace.induced
              (fun x : Padic.coefficientExtensionIntegers l E => (x : E))
              (@UniformSpace.toTopologicalSpace E
                (coefficientExtensionAbsoluteValue l E).toNormedField.toUniformSpace))
            q ∧
            (∀ t : T,
              (Padic.coefficientExtensionUniformizer l E : E) ^ e * (q t : E) =
                (f t : E)) ∧
            (∀ (t₀ : T),
              (f t₀ : E) ∈ Set.range
                (fun z : (Padic.coefficientExtensionIntegers l E)ˣ =>
                  (Padic.coefficientExtensionUniformizer l E : E) ^ e *
                    ((z : Padic.coefficientExtensionIntegers l E) : E)) →
              ∃ U : Set T, IsOpen U ∧ t₀ ∈ U ∧
                (∀ t : T, t ∈ U → IsUnit (q t)) ∧
                @ContinuousOn T E _
                  (@UniformSpace.toTopologicalSpace E
                    (coefficientExtensionAbsoluteValue l E).toNormedField.toUniformSpace)
                  (fun t : T => ((q t : E)⁻¹)) U) ∧
            ∀ q' : T → Padic.coefficientExtensionIntegers l E,
              @Continuous T (Padic.coefficientExtensionIntegers l E) _
                (TopologicalSpace.induced
                  (fun x : Padic.coefficientExtensionIntegers l E => (x : E))
                  (@UniformSpace.toTopologicalSpace E
                    (coefficientExtensionAbsoluteValue l E).toNormedField.toUniformSpace))
                q' →
              (∀ t : T,
                (Padic.coefficientExtensionUniformizer l E : E) ^ e * (q' t : E) =
                  (f t : E)) →
              q' = q
 := by
  sorry

end Padic
