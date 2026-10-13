module

public import Sheaf.RingTheory.IsStrictHenselization
import Sheaf.RingTheory.StrictHenselizationTriples
public import Mathlib.CategoryTheory.Filtered.Basic

@[expose] public section
universe u
open CategoryTheory
namespace Algebra

/-- Filteredness follows from identity, tensor-product successors, and the iterated
 tensor equalizer construction of Stacks Tag 04GW.
Source: Stacks Project, Algebra, Tag 04GW.
(blueprint: lem-sc-pointed-etale-filtered). -/
theorem pointedEtale_filtered
    (R K : Type u) [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [IsSepClosure (IsLocalRing.ResidueField R) K] [Algebra R K]
    [IsScalarTower R (IsLocalRing.ResidueField R) K] :
    let P : ObjectProperty (Over (CommAlgCat.of R K)) := fun X ↦ Etale R X.left
    IsFiltered P.FullSubcategory := by sorry
end Algebra
