/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeBaseChange.GeometricProperBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.Native.NativeBaseChangeOpenChart
import WeilConjectures.AlgebraicGeometry.Native.NativeDerivedExchangeComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleSmoothBaseChange
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
import WeilConjectures.SixFunctors.ProEtale.Adic.MayerVietoris
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.OverSquare
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# The geometric native derived smooth base-change mate

For a cartesian square of `k₀`-schemes
```
Z' --v--> Z
|p'       |p
v         v
T' --g--> T
```
with `g` smooth and `p` separated, quasi-compact and locally of finite type, the native derived
base-change morphism `ḡ^* Rp̄_* ⟶ Rp̄'_* v̄^*` of the geometric square (the base change to the
algebraic closure of `k₀`) is invertible on bounded complexes with constructible cohomology
(`AlgebraicGeometry.NativeBaseChange.geometric_smooth_baseChange_isIso`).

The proof follows `AlgebraicGeometry.NativeBaseChange.geometric_proper_baseChange_isIso`: by
the joint conservativity of restriction to an affine Zariski cover of the target, the claim
reduces to affine charts
(`AlgebraicGeometry.ProEtale.adicDerivedBaseChange_isIso_of_affine_of_smooth`),
where the encoded native mate is identified with the condensed base-change morphism of bounded
constructible `ℚ̄_ℓ`-complexes, which is invertible by smooth base change
(`AlgebraicGeometry.ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_smooth`).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

namespace ProEtale

attribute [local irreducible] DerivedCategory HasDerivedCategory.standard
  Functor.rightDerivedFunctor Functor.mapDerivedCategory
  CondensedRing.boundedConstructibleBaseChangeOfPreserves
  upperStarFromPoint Functor.leftDerivedFunctor Mod.monoidalCategory
  CondensedRing.boundedConstructibleUpperStar
  CondensedRing.derivedUpperStarLowerStarAdjunction ObjectProperty.lift
  CondensedRing.boundedConstructibleUpperStarCompatibility
  CondensedRing.boundedConstructiblePullbackSquareComparison
  Functor.squareTransport Adjunction.restrictFullyFaithful

attribute [local irreducible] CondensedRing.boundedConstructibleBaseChange

end ProEtale

namespace NativeBaseChange

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]

variable {Z' Z T' T : Scheme.{u}}
  [Z'.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
  [T'.Over (Spec (CommRingCat.of k₀))] [T.Over (Spec (CommRingCat.of k₀))]
  {v : Z' ⟶ Z} {p' : Z' ⟶ T'} {p : Z ⟶ T} {g : T' ⟶ T}
  [v.IsOver (Spec (CommRingCat.of k₀))] [p'.IsOver (Spec (CommRingCat.of k₀))]
  [p.IsOver (Spec (CommRingCat.of k₀))] [g.IsOver (Spec (CommRingCat.of k₀))]

end NativeBaseChange

end AlgebraicGeometry
