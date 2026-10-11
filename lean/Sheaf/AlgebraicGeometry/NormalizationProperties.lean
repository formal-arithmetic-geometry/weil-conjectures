import Mathlib.AlgebraicGeometry.Birational.Birational
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import WeilConjectures.AlgebraicGeometry.Regular

/-!
# Properties of the normalization

Source: blueprint sec-curve-estimates/sk-thm-br/lem-sc-normalization-properties.md,
node lem-sc-normalization-properties, order 919.
-/

universe u

open CategoryTheory Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Properties of the normalization of an integral finite type scheme over a field.

Part (a) is supplied by `lem-sc-normalization-exists`, part (b) by
`lem-sc-normalization-over-normal-locus`, and part (c) by
`lem-sc-normalized-curve-smooth`.

The proof combines the finiteness, surjectivity, birationality, properness,
and dimension assertions from `lem-sc-normalization-exists`, the restriction
isomorphism from `lem-sc-normalization-over-normal-locus`, and the smoothness
assertion from `lem-sc-normalized-curve-smooth`.
(blueprint: lem-sc-normalization-properties)
-/
theorem normalization_properties {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] (q : X ⟶ Spec (.of k)) [LocallyOfFiniteType q] [QuasiCompact q] :
    IsFinite X.fromNormalization ∧
      Surjective X.fromNormalization ∧
      Birational X.normalization X ∧
      (IsProper q → IsProper (X.fromNormalization ≫ q)) ∧
      topologicalKrullDim X.normalization = topologicalKrullDim X ∧
      (∀ (U : X.Opens),
        (∀ x ∈ U, IsIntegrallyClosed (X.presheaf.stalk x)) →
          IsIso (X.fromNormalization ∣_ U)) ∧
      (PerfectField k → topologicalKrullDim X = 1 →
        Smooth (X.fromNormalization ≫ q)) := by
  sorry

end AlgebraicGeometry.Scheme
