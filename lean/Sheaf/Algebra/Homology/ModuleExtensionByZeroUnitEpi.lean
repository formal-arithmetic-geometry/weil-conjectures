module
public import Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact
@[expose] public section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
noncomputable section
namespace AlgebraicGeometry
/-- The extension-by-zero/restriction unit is epic.
Source: Stacks Project, Sheaves Lemma 00A7 (4).
Proof: identify sections on opens contained in W with the unique direct-sum summand;
every section of the restricted sheaf is represented by such a summand, and sheafification
preserves the resulting surjection.
(blueprint: lem-sc-module-extension-by-zero-unit-epi) -/
theorem moduleExtensionByZero_unit_epi (X : RingedSpace.{u}) (W : Opens X)
    (G : SheafOfModules.{u} ((moduleRings X).over W)) :
    Epi ((Classical.choice (open_restriction_adjunction_exact X W).2.2.2.2).unit.app G) := by sorry
end AlgebraicGeometry
