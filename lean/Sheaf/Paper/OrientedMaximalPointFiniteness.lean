module

public import Sheaf.Paper.OrientedNearbyCycles
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Sheaf.AlgebraicGeometry.EtaleToposPointsGeometric
public import Sheaf.AlgebraicGeometry.GeometricSpecializationStrictLocalLift
public import Sheaf.AlgebraicGeometry.NormalizedBaseChangeNoetherianTopology
public import Sheaf.CategoryTheory.Sites.OrientedProductLargeSites
public import Sheaf.TraceFormula.OrientedPointNormalizedStratum

@[expose] public section

universe u v w

namespace AlgebraicGeometry.OrientedNearbyCycles

open CategoryTheory

/--
Finitely many maximal isomorphism classes of points of the vanishing topos.

Source: Orgogozo, *Modifications et cycles proches sur une base générale*,
Lemma 8.3.2 and the point-order definition immediately preceding it (author
draft, p. 18).  The proof is the source's finite-type argument: represent a
point by an oriented triple, lift its second support to a generic point of a
Noetherian component, identify each fixed-support stratum with the normalized
fibre, and apply Noetherian finiteness of irreducible components.  A finite
poset argument then gives the maximal representatives.  The theorem is stated
with `sorry` at stage 2; no assertion is weakened by the finite-family
formulation.  The empty vanishing topos is included by allowing an empty
finite index type.

(blueprint: lem-trf-oriented-maximal-point-finiteness)
-/
theorem oriented_maximal_point_finiteness
    {S X : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [CompactSpace S]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] :
    ∃ (ι : Type w), Finite ι ∧
      ∃ (m : ι → GeometricMorphism (Type 0) (VanishingTopos.{u, v} f)),
        (∀ i : ι,
          ∀ q : GeometricMorphism (Type 0) (VanishingTopos.{u, v} f),
            Nonempty (q.direct ⟶ (m i).direct) →
              Nonempty (q.direct ≅ (m i).direct)) ∧
        (∀ p : GeometricMorphism (Type 0) (VanishingTopos.{u, v} f),
          ∃ i : ι, Nonempty ((m i).direct ⟶ p.direct)) := by
  sorry


end AlgebraicGeometry.OrientedNearbyCycles
