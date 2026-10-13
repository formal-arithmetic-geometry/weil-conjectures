module
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Algebra.Module.Torsion.Free
import Sheaf.AlgebraicGeometry.Morphisms.NormalizationStalkBaseChange
@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme
/-- Injectivity of the normalization stalk map in the punctured DVR situation.
(blueprint: lem-sbc-punctured-dvr-normalization-stalk-torsion-free-injective)
-/
theorem punctured_dvr_normalization_stalkMap_injective
    {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens)
    {P : Scheme.{u}} (p : P ⟶ U.toScheme) [IsFinite p] (hetale : Etale p)
    (x : (p ≫ U.ι).normalization)
    (hs : (p ≫ U.ι).fromNormalization x ∉ U)
    [IsDomain (X.presheaf.stalk ((p ≫ U.ι).fromNormalization x))]
    [IsDiscreteValuationRing (X.presheaf.stalk ((p ≫ U.ι).fromNormalization x))] :
    Function.Injective ((p ≫ U.ι).fromNormalization.stalkMap x).hom := by
  sorry
end AlgebraicGeometry.Scheme
