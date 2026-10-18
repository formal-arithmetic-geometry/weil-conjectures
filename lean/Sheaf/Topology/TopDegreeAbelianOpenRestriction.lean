module

public import Sheaf.Topology.TopDegreeAbelianNeighborhoodZero
public import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
public import Mathlib.Topology.Sheaves.MayerVietoris

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology Opposite
namespace TopCat
/-- Top-degree cohomology restricts surjectively to every open of a Noetherian
spectral space. Source: Stacks Project, Tag 0A3G (2).
(blueprint: lem-weil-pbc-top-degree-abelian-open-restriction).

Proof: A given class vanishes on the intersection with a neighborhood of the
complement by the punctured-neighborhood argument above. The open and that
neighborhood cover the space. Their Mayer--Vietoris sequence lifts the pair
consisting of the given class and zero to a global class. -/
theorem top_degree_abelian_open_restriction_surjective
    {T : Type u} [TopologicalSpace T] [NoetherianSpace T] [SpectralSpace T]
    (d : ℕ) (hdim : topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})
    (U : Opens T) :
    Function.Surjective
      ((A.cohomologyPresheaf d).map (homOfLE (le_top : U ≤ ⊤)).op) := by
  sorry


end TopCat
