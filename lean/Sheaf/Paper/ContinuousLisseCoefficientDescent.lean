module

public import Sheaf.Paper.ContinuousIntegralCoefficients
import all Sheaf.Paper.ContinuousLissePullbackSystem
import all Sheaf.Paper.ContinuousLisseStratumDescent
import Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem continuousLisse_coefficient_lattice_on_stratum
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (D : PullbackSystem.{u} ℓ E)
    {X U V W : Scheme.{u}} [TopologicalSpace.NoetherianSpace W]
    (p : U ⟶ X) (j : W ⟶ X) (r : V ⟶ U) (q : V ⟶ W)
    [IsFinite q] [Etale q] [Surjective q] (w : r ≫ p = q ≫ j)
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hP : LocallyFree (condensedRingObj (Profinite.continuousMapRingObj E) X) P)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) U))
    (hM : LocallyFree (condensedRingObj (integralCoeff ℓ E) U) M)
    (e : (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) U)).obj M ≅
      (CondensedRing.upperStar (Profinite.continuousMapRingObj E) p).obj P) :
    ∃ N : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) W),
      ProEtale.IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) W) N ∧
      Nonempty ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) W)).obj N ≅
        (CondensedRing.upperStar (Profinite.continuousMapRingObj E) j).obj P) := by
  exact @continuousLisse_lattice_on_stratum
    (integralCoeff ℓ E) (Profinite.continuousMapRingObj E) _ _ _ _
    (integralScalarMap ℓ E) _ D X U V W _ p j r q _ _ _ w P hP M hM e
    (fun P' hP' M' hM' e' ↦
      continuousLisse_finiteEtale_lattice ℓ E W P' hP' q M' hM' e')

end AlgebraicGeometry.ProEtale.CondensedRing
