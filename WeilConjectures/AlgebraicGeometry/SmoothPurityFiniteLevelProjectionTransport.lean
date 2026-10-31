/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerShriekData
public import WeilConjectures.AlgebraicGeometry.SmoothPurityStrictCompactificationComparisonData

/-! # Finite-level projection: strict-word transport -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Transport finite projection invertibility through the strict comparison word.
This is purely categorical: there are no field or GoodLevel hypotheses.
Source: blueprint operations proof (2a), strict finite projection comparison word
(blueprint: lem-sp-finite-level-projection-transport).

Proof: unpack the tensor comparison and its word equality in `comparison`.
Specialize that equality to `wK.level.obj` and `wL.level.obj`. Its left side is
invertible: `hfixed` supplies its first factor and all other factors are components
of comparison isomorphisms or functor images of such components. On the right side,
the factors preceding comparisonLevelProjection are invertible. Cancel them to
obtain invertibility on the realized fixed-scalar origins. The proper counit,
tensor comparison, open tensor mate and pullback compositor defining the level
projection are natural in both inputs. For the open tensor factor this follows by
applying the adjunction Hom bijection to its mate equation: both composites become
the same tensor of the natural unit and tensor-pullback comparison. Compose these
naturality equations, then use `wK.realization` and `wL.realization` to conjugate the
projection to the evaluated objects. Cancel the two endpoint isomorphisms. The
argument works for zero objects and empty schemes without any arithmetic condition.
-/
theorem finite_level_projection_transport_isIso (b : Base l E) (o : Operations l E b)
    (levels : ComparisonLevels l E b o) (coordinates : StrictFiniteCoordinates l E b)
    (comparison : StrictFiniteProjectionComparisons l E b o levels coordinates)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (n : ℕ) (K : D l E X) (L : D l E Y)
    (wK : Origin l E b X n K) (wL : Origin l E b Y n L)
    (hfixed : IsIso ((comparisonFiniteRealization l E b Y n).map
      (comparisonFiniteProjection l E b c n wK.level.obj wL.level.obj))) :
    IsIso (comparisonLevelProjection l E b o levels c n
      ((Ev l E X n).obj K) ((Ev l E Y n).obj L)) := by sorry

end AlgebraicGeometry.ProEtale.SpTowerShriek
