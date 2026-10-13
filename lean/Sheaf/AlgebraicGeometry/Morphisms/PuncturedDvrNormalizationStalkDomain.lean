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
/-- The normalization stalk in the punctured DVR situation is a domain.
(blueprint: lem-sbc-punctured-dvr-normalization-stalk-domain)
-/
theorem punctured_dvr_normalization_stalk_isDomain
    {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens)
    {P : Scheme.{u}} (p : P ⟶ U.toScheme) [IsFinite p] (hetale : Etale p)
    (x : (p ≫ U.ι).normalization)
    (hs : (p ≫ U.ι).fromNormalization x ∉ U)
    [IsDomain (X.presheaf.stalk ((p ≫ U.ι).fromNormalization x))]
    [IsDiscreteValuationRing (X.presheaf.stalk ((p ≫ U.ι).fromNormalization x))] :
    IsDomain ((p ≫ U.ι).normalization.presheaf.stalk x) := by
  sorry
end AlgebraicGeometry.Scheme
