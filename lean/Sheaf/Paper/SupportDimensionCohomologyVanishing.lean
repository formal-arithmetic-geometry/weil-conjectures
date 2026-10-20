module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sheaves.Sheaf
import Sheaf.Topology.ClosedImmersionPushforwardCohomology
import Sheaf.Topology.NoetherianTopologicalCohomologyVanishing

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Cohomology of an abelian sheaf vanishes above the dimension of a closed support.
(blueprint: lem-sc-support-dimension-cohomology-vanishing)

The support locus is written inline as the set of points whose abelian-group
stalk is not subsingleton, using Mathlib's presheaf stalk. -/
theorem support_dimension_cohomology_vanishing
    (X : Scheme.{u}) [CompactSpace X] [IsLocallyNoetherian X]
    (F : Sheaf (Opens.grothendieckTopology (X : Type u)) AddCommGrpCat.{u})
    [HasSheafify (Opens.grothendieckTopology (X : Type u)) AddCommGrpCat.{u}]
    [HasExt (Sheaf (Opens.grothendieckTopology (X : Type u)) AddCommGrpCat.{u})]
    (Z : Set X)
    (hSupp : {x : (X : Type u) |
      ¬ Subsingleton (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (X := TopCat.of (X : Type u)) F.obj x)} ⊆ Z)
    (hZ : IsClosed Z)
    (r p : ℕ) (hdim : topologicalKrullDim Z ≤ (r : WithBot ℕ∞)) (hp : r < p) :
    Subsingleton (CategoryTheory.Sheaf.H' F p (⊤ : TopologicalSpace.Opens (X : Type u))) := by
  sorry

end AlgebraicGeometry
