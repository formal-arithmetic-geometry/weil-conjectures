import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Product of geometrically irreducible schemes over a field

Source: literature/stacks-project/varieties.tex, Tag 038F
(blueprint: lem-sc-irreducible-product-over-field).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The fibre product over a field of two geometrically irreducible schemes is irreducible.

Source: Stacks Project, Tag 038F (blueprint: lem-sc-irreducible-product-over-field).
The proof applies the component bijection, uses geometric irreducibility of the second factor,
and uses the component-cover lemma to conclude that the unique component is the whole product. -/
theorem irreducibleSpace_pullback_of_geometricallyIrreducible
    (K : Type u) [Field K] (U V : Scheme.{u})
    [U.Over (Spec (.of K))] [V.Over (Spec (.of K))]
    [GeometricallyIrreducible (U ↘ Spec (.of K))]
    [GeometricallyIrreducible (V ↘ Spec (.of K))] :
    IrreducibleSpace (pullback (C := Scheme) (U ↘ Spec (.of K)) (V ↘ Spec (.of K))) := by
  sorry

end AlgebraicGeometry
