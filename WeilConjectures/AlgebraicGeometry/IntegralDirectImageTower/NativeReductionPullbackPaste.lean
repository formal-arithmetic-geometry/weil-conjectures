/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralDirectImageTowerData
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # Pasting the normalized scalar and geometric pullback comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Paste the ordinary comparisons using the specified ordinary compositors.
Source: normalized scalar/pullback construction, paragraphs (2)--(3).
(blueprint: def-dla1-native-reduction-pullback-paste). -/
def nativeReductionOrdinaryPaste (s : Presentation l E) (q : ReductionGeometry l E s)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    CondensedRing.upperStar (spIntegralCondensed l E) (f ≫ g) ⋙
        ordinaryReduction l E s X ≅
      ordinaryReduction l E s Z ⋙ (s.operations.geometry (f ≫ g)).pull :=
  Functor.isoWhiskerRight (CondensedRing.upperStarComp (spIntegralCondensed l E) f g)
      (ordinaryReduction l E s X) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (q.pullback f).ordinary ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (q.pullback g).ordinary _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (s.operations.ordinaryComp f g)

/-- Paste the derived comparisons using the specified derived compositors.
Source: normalized scalar/pullback construction, paragraphs (2)--(3).
(blueprint: def-dla1-native-reduction-pullback-paste). -/
def nativeReductionDerivedPaste (s : Presentation l E) (q : ReductionGeometry l E s)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pull l E (f ≫ g) ⋙ derivedReduction l E s X ≅
      derivedReduction l E s Z ⋙
        SpTowerShriek.pull l E s.base (s.operations.geometry (f ≫ g)) :=
  Functor.isoWhiskerRight
      (CondensedRing.leftDerivedUpperStarComp (spIntegralCondensed l E) f g)
      (derivedReduction l E s X) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (q.pullback f).derived ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (q.pullback g).derived _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (s.operations.comp f g)

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower
