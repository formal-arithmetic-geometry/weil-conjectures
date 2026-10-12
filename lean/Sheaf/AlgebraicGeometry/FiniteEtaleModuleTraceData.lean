module
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.CategoryTheory.Linear.FunctorCategory
import Sheaf.AlgebraicGeometry.EtaleSheaves
import Sheaf.Paper.DirectImageSplitCoverProduct
import Sheaf.Paper.FiniteEtaleEtaleLocalSplit
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.FiniteEtaleTraceExists
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale
/-- Intermediate coefficient-linear trace data from the finite étale local splitting and sheaf
gluing construction of Stacks 03SH and 04HN.
(blueprint: lem-weil-pbc-finite-etale-module-trace-data) -/
theorem finiteEtaleModuleTraceData
    {X Y : Scheme.{u}} (R : Type (u + 1)) [CommRing R]
    (f : Y ⟶ X) [IsFinite f] [Etale f]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) (d : ℕ)
    (hdeg : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      Nat.card (f.GeometricFiber s) = d) :
    (∃ t : (f)_*[ModuleCat.{u + 1} R].obj ((f)^*[ModuleCat.{u + 1} R].obj G) ⟶ G,
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).unit.app G ≫ t =
        (d : R) • 𝟙 G) ∧ Nonempty PUnit.{0} := by
  sorry
end AlgebraicGeometry.Etale
