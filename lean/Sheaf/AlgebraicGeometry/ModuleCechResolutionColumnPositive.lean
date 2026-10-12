module

public import Sheaf.AlgebraicGeometry.ModuleCechComparison

public import Sheaf.Topology.OpenModuleCohomology

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- Vanishing open cohomology in degree p makes the corresponding column homology zero.
Source: Stacks Project, Tag 01ET, proof using the columns of the double complex of 01EQ.
(blueprint: lem-sc-module-cech-resolution-column-positive)

Proof: for each tuple y, apply the resolution-computation isomorphism for the right
derived functor of sections on the intersection of U(y(l)). By the hypothesis its
degree-p homology is zero, so every degree-p cocycle is the differential of a degree
p-1 element. The Cech column consists of products of these section modules, with
coordinatewise resolution differential. Choose a preimage for each coordinate of a
product cocycle. Their tuple is a preimage in the column, proving exactness in degree p.
Restriction of scalars to the global section ring preserves this underlying exactness.
Exactness in degree p is equivalent to the homology object being zero. For an empty
tuple-indexing type the product is zero, so the same argument applies. -/
theorem moduleCech_resolution_column_positive {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (F : X.Modules) (I : InjectiveResolution F) (n p : ℕ)
    (hp : 0 < p)
    (hvan : ∀ y : Fin (n + 1) → ι,
      Subsingleton ((RingedSpace.openModuleCohomology X.toRingedSpace p
        (⨅ l, U (y l))).obj F)) :
    IsZero (((moduleCechDouble U I).flip.X n).homology p) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
