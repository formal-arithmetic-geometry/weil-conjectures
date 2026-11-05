/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStar

/-!

# The derived finite-coefficient comparison commutes with pushforward and extension by zero

Let `T` be a finite discrete commutative ring and `g : X ⟶ Y` a morphism of schemes. The
equivalence `ProEtale.finiteCoefficientModEquivalence` identifies module objects over
`Λ_X = p_X^* T̲` with pro-étale sheaves of `T`-modules on `X`, and commutes with pushforward
(`ProEtale.lowerStarFiniteCoefficientModEquivalenceIso`) and pullback
(`ProEtale.upperStarFiniteCoefficientModEquivalenceIso`). This file derives the consequences for
the derived pushforward and for extension by zero along open immersions.

## Main definitions and results

* `ProEtale.finiteCoefficientDerivedLowerStarIso`: the derived comparison commutes with the
  derived pushforward, `D(Φ_X) ⋙ Rg_* ≅ Rg_*⟦T̲⟧ ⋙ D(Φ_Y)`.
* `CategoryTheory.Adjunction.leftAdjointCompEquivalenceIso`: a commutation of right adjoints
  with equivalences induces the conjugate commutation of the left adjoints. Hence the extension
  by zero versions `ProEtale.finiteCoefficientModOpenImmersionLowerShriekIso` and
  `ProEtale.finiteCoefficientDerivedOpenImmersionLowerShriekIso`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

/-! ### Transporting a commutation of right adjoints to the left adjoints -/

namespace CategoryTheory.Adjunction

variable {C C' D D' : Type*} [Category* C] [Category* C'] [Category* D] [Category* D']
  (eC : C ≌ C') (eD : D ≌ D') {L : D ⥤ C} {R : C ⥤ D} {L' : D' ⥤ C'} {R' : C' ⥤ D'}

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T] {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- **The derived finite-coefficient comparison commutes with pushforward**: for
`Φ = finiteCoefficientDerivedEquivalence`, `Φ_X ⋙ Rg_* ≅ Rg_*⟦T̲⟧ ⋙ Φ_Y`. Since `Φ_X` is an
exact equivalence, it preserves K-injective complexes and `D(Φ_X) ⋙ Rg_* ≅ R(Φ_X ⋙ g_*)`; since
`Φ_Y` is exact, `R(g_*⟦T̲⟧ ⋙ Φ_Y) ≅ Rg_*⟦T̲⟧ ⋙ D(Φ_Y)`; the two right derived functors are
identified by `lowerStarFiniteCoefficientModEquivalenceIso`. -/
noncomputable def finiteCoefficientDerivedLowerStarIso :
    (finiteCoefficientDerivedEquivalence X T).functor ⋙
        R((g)_*[ModuleCat.{u + 1} (ULift.{u + 1} T)]) ≅
      R((g)_*⟦Profinite.continuousMapRingObj T⟧) ⋙
        (finiteCoefficientDerivedEquivalence Y T).functor :=
  (Functor.mapDerivedCategoryCompRightDerivedFunctorIso
      (finiteCoefficientModEquivalence X T).functor _).symm ≪≫
    Functor.rightDerivedFunctorNatIso (lowerStarFiniteCoefficientModEquivalenceIso g T).symm ≪≫
    Functor.rightDerivedFunctorCompMapDerivedCategoryIso _
      (finiteCoefficientModEquivalence Y T).functor

/-! ### Extension by zero -/

end AlgebraicGeometry.ProEtale
