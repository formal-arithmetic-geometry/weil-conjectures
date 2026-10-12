module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Coherence of a formal module is invariant under isomorphism of inverse systems.
Source: Stacks Project, Lemma 087X, transport of the three defining conditions
(blueprint: lem-weil-pbc-coherent-formal-iso-invariant).

Proof: transport coherence and zero-product conditions along each component isomorphism;
transport the quotient-transition isomorphisms by the naturality squares of the given
natural isomorphism. -/
theorem coherentFormalModules_of_iso
    (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData)
    {F G : ℕᵒᵖ ⥤ X.Modules} (e : F ≅ G)
    (hF : IsCoherentFormalModule I F) :
    IsCoherentFormalModule I G := by
  sorry

end AlgebraicGeometry
