/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!

# The comparison of the two finite-coefficient models commutes with pullback

Let `T` be a finite discrete commutative ring and `f : X ⟶ Y` a morphism of schemes. The
equivalence `ProEtale.finiteCoefficientModEquivalence` between module objects over the condensed
coefficient ring `T̲_X = p_X^* C(-, T)` and pro-étale sheaves of `T`-modules commutes with the
pushforwards (`ProEtale.lowerStarFiniteCoefficientModEquivalenceIso`): both pushforwards have
underlying abelian sheaf `f_* M`, and the actions of `t ∈ T` agree, being the actions of the
constant global section `t` (`ProEtale.finiteCoefficientModEquivalence_smul`). By uniqueness of
left adjoints it commutes with the pullbacks
(`ProEtale.upperStarFiniteCoefficientModEquivalenceIso`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (T : Type) [TopologicalSpace T] [CommRing T]
  [IsTopologicalRing T] [DiscreteTopology T] [Finite T]

/-- **The comparison of the two finite-coefficient models commutes with pushforward**:
`f_* ⋙ Φ_Y ≅ Φ_X ⋙ f_*`, where `Φ` is `finiteCoefficientModEquivalence`. Both sides have
underlying abelian sheaf `f_* M`, and the actions of `t ∈ T` on sections agree, being the actions
of the constant global section `t` (`finiteCoefficientModEquivalence_smul`). -/
noncomputable def lowerStarFiniteCoefficientModEquivalenceIso :
    CondensedRing.lowerStar (Profinite.continuousMapRingObj T) f ⋙
        (finiteCoefficientModEquivalence Y T).functor ≅
      (finiteCoefficientModEquivalence X T).functor ⋙
        ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} T)) f :=
  sorry

/-- **The comparison of the two finite-coefficient models commutes with pullback**:
`f^* ⋙ Φ_X ≅ Φ_Y ⋙ f^*`, the conjugate of `lowerStarFiniteCoefficientModEquivalenceIso`. -/
noncomputable def upperStarFiniteCoefficientModEquivalenceIso :
    CondensedRing.upperStar (Profinite.continuousMapRingObj T) f ⋙
        (finiteCoefficientModEquivalence X T).functor ≅
      (finiteCoefficientModEquivalence Y T).functor ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} T)) f :=
  sorry

end AlgebraicGeometry.ProEtale
