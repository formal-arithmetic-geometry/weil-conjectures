/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictCompactificationComparisonData
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! Finite adjunction coordinates for the strict compactification comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u c₁ c₂ c₃ c₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerShriek

private def coordinatesOfLeft
    {C₁ : Type c₁} {C₂ : Type c₂} {C₃ : Type c₃} {C₄ : Type c₄}
    [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
    (e : C₁ ⥤ C₃) (d : C₂ ⥤ C₄) [e.IsEquivalence] [d.IsEquivalence]
    {L : C₁ ⥤ C₂} {G : C₂ ⥤ C₁} (adj : L ⊣ G)
    {l : C₃ ⥤ C₄} {g : C₄ ⥤ C₃} (level : l ⊣ g)
    (s : L ⋙ d ≅ e ⋙ l) : ComparisonAdjunctionCoordinates e d adj level := by
  let a : TwoSquare e L l d := TwoSquare.mk _ _ _ _ s.inv
  have : IsIso a.natTrans := by dsimp [a]; infer_instance
  have := isIso_mateEquiv_of_isEquivalence adj level a
  refine { left := s,
           right := asIso (mateEquiv adj level a).natTrans,
           unit := ?_,
           counit := ?_ }
  · intro K
    change e.map (adj.unit.app K) ≫ (mateEquiv adj level a).app (L.obj K) ≫
      g.map (s.hom.app K) = _
    rw [← Category.assoc, unit_mateEquiv adj level a]
    simp [a, ← Functor.map_comp]
  · intro K
    exact mateEquiv_counit adj level a K

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The fixed scalar realization admits the right-adjoint coordinates determined by
its pullback square and the two adjunction equations.
Source: blueprint operations proof (2), transposes of the finite pullback square.
(blueprint: new-lem-sp-strict-finite-coordinates-existence).

Proof: for each finite level, localize the ordinary identity-section realization
and use the canonical adjunction between upper-star and lower-star.  Conjugating
its right adjoint by the realization equivalence gives the right comparison; the
adjunction unit and counit identities are preserved by the equivalence.  The
left comparison is definitionally the fixed comparisonFinitePull.  Taking these
coordinates for every morphism and level yields StrictFiniteCoordinates. -/
theorem strictFiniteCoordinatesExistence (b : Base l E) :
    Nonempty (StrictFiniteCoordinates l E b) := by
  refine ⟨⟨fun f n ↦ coordinatesOfLeft _ _
    (derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) f)
    (Adjunction.mapDerivedCategoryRightDerivedAdjunction
      (proEtaleConstantRingAdjunction (R l E n) f))
    (comparisonFinitePull l E b f n), fun f n ↦ rfl⟩⟩

end AlgebraicGeometry.ProEtale.SpTowerShriek
