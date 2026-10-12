module
public import Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact
import Sheaf.CategoryTheory.ExtensionByZeroPresheaf
@[expose] public section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
noncomputable section
namespace AlgebraicGeometry
/-- The extension-by-zero/restriction unit is monic.
Source: Stacks Project, Sheaves Lemma 00A7 (4).
Proof: identify sections on opens contained in W with the unique direct-sum summand;
the resulting restriction map is injective, and sheafification preserves this comparison.
(blueprint: lem-sc-module-extension-by-zero-unit-mono) -/
theorem moduleExtensionByZero_unit_mono (X : RingedSpace.{u}) (W : Opens X)
    (G : SheafOfModules.{u} ((moduleRings X).over W)) :
    Mono ((Classical.choice (open_restriction_adjunction_exact X W).2.2.2.2).unit.app G) := by sorry
end AlgebraicGeometry
