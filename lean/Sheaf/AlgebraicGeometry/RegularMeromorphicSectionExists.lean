import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import Sheaf.AlgebraicGeometry.MeromorphicModule
import Sheaf.AlgebraicGeometry.NoEmbeddedPoints

universe v

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-!
# Existence of a regular meromorphic section

Source: Stacks Project, Divisors, Tag 02OZ (Lemma 31.5.10, case (3));
(blueprint: lem-sc-regular-meromorphic-section-exists).
-/

/-- For a proper locally Noetherian finite-dimensional scheme without embedded points, every
invertible module has a regular meromorphic section. The canonical map is represented by
`meromorphicSectionMap`, and regularity means that this map is a monomorphism.
Source: Stacks Project, Divisors, Tag 02OZ (Lemma 31.5.10, case (3));
(blueprint: lem-sc-regular-meromorphic-section-exists).
Proof: choose generators at generic points using Tag 0EMH and check injectivity componentwise;
these are the two proof steps recorded in the DAG, using
lem-sc-meromorphic-sheaf-generic-product and def-sc-invertible-module. -/
theorem exists_regularMeromorphicSection
    {k : Type v} [Field k] (X : Scheme.{v})
    [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    [IsLocallyNoetherian X]
    [NoEmbeddedPoints X]
    (hfinite : topologicalKrullDim X ≠ ⊤)
    (L : X.Modules) [L.IsInvertible] :
    ∃ s : unit X ⟶ meromorphicModule X L,
      Mono (meromorphicSectionMap X L s) := by
  sorry

end AlgebraicGeometry
