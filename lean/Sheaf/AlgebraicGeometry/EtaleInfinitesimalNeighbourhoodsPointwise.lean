module
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.BaseChangeConventions
import Sheaf.AlgebraicGeometry.EtaleOpenOfSmoothZeroFibreDimension
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import Sheaf.AlgebraicGeometry.FormallySmooth
import Sheaf.AlgebraicGeometry.SmoothArtinianLiftingAtPoint
import Sheaf.AlgebraicGeometry.Thickening
import WeilConjectures.Mathlib.Topology.KrullDimension
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
/-! Pointwise étale neighbourhood extracted from infinitesimal étaleness.

The proof follows the pointwise part of Stacks Lemma 0A43: the Artinian lifting
criterion gives smoothness, the zeroth neighbourhood gives fibre dimension zero,
and shrinking yields an étale neighbourhood. (blueprint: lem-weil-pbc-etale-infinitesimal-pointwise)
-/
/-- Every point over the closed subscheme has an etale neighbourhood. The proof uses
smoothness from the Artinian lifting criterion, zero fibre dimension from the etale
zeroth neighbourhood, and the etale shrinking lemma.
(blueprint: lem-weil-pbc-etale-infinitesimal-pointwise) -/
theorem etale_infinitesimal_pointwise
    {X S Z : Scheme.{u}} (g : X ⟶ S) (i : Z ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsClosedImmersion i] (J : S.IdealSheafData) (hJ : J = i.ker)
    (h_etale : ∀ n : ℕ,
      Etale (pullback.snd g ((J ^ (n + 1)).subschemeι)))
    (x : X) (hx : (g : X → S) x ∈ Set.range (i : Z → S)) :
    ∃ W : X.Opens, x ∈ W ∧ Etale (W.ι ≫ g) := by
  sorry
end AlgebraicGeometry
