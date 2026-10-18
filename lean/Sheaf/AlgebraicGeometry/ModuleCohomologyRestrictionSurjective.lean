module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.Topology.KrullDimension
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import Sheaf.Topology.TopDegreeAbelianOpenRestriction
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
/-- The underlying additive restriction on top-degree module cohomology is surjective.
Source: Stacks Project, Cohomology, Tag 0A3G (2); compare the underlying abelian
Mayer--Vietoris argument and the canonical module/abelian resolution comparison.
(blueprint: lem-weil-pbc-top-degree-module-restriction-surjective).
Proof: choose an injective module resolution and forget scalars termwise. The
resulting section complexes compute both module and abelian cohomology and commute
with restriction. Apply top-degree abelian open restriction surjectivity and
transport through these canonical resolution comparisons. -/
theorem module_cohomology_restriction_surjective
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (d : ℕ) (hdim : topologicalKrullDim X = (d : WithBot ℕ∞))
    (V : Scheme.{u}) (j : V ⟶ X) [IsOpenImmersion j] [CompactSpace V]
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    Function.Surjective
      (moduleCohomologyFMap j ((restrictAdjunction j).unit.app F) d) := by
  sorry
end AlgebraicGeometry.Scheme.Modules
