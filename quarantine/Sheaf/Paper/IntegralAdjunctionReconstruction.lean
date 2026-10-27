/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S6
-/
module

public import Sheaf.Paper.IntegralReconstructionComparisonData
import Sheaf.Paper.IntegralReconstructionComparisons

/-! # Interface comparisons for the integral adjunction

Source: latest blueprint, integral-adjunction-bijection, Normalization and Purity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpIntegralAdjunction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Assemble the normalized reconstruction comparisons for the given presentations.
Source: latest blueprint, integral-adjunction-bijection, Normalization and Bijections;
lem-sp-integral-reconstruction-comparisons
(blueprint: lem-sp-integral-adjunction-reconstruction-package).

Proof: finite type over the field makes X and Y Noetherian. Restrict each specified
normalized equivalence to the integral and normalized constructible subcategories.
Its actual unit and counit give the reconstruction isomorphisms, full faithfulness,
and reconstruction identity by naturality and cancellation of the unit. The tower
purity theorem gives preservation of normalization by both adjoints; hence the
specified total-limit right functor lands in integral constructible objects.
Choose the quotient-normalized compactification limit presentations and scalar
comparisons from complete_compactification_limit_realization. Its canonical image
comparison, followed by towerWord, gives imageComparison with image_normalization.
Reduce it and compose with NY's actual counit to get leftComparison. Use NX's
actual counit for rightComparison. Their naturality is inherited from these maps.
The image comparison also proves support_closed. These are exactly the fields of
Reconstruction; none asserts the transported integral adjunction or its purity. -/
theorem integralAdjunctionReconstruction
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    {X Z Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    [(j ≫ p).IsOver (Spec (.of D.k))]
    (d : ℕ) [SmoothOfRelativeDimension d (j ≫ p)]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : SpTowerCalculus.Coordinates l E b) (w : SpChartAdmissibility.Twists l E X)
    (RX : SpReductionTower l E X (q.abelian X))
    (NX : SpNormalizedEquivalence l E X (q.abelian X) RX)
    (RY : SpReductionTower l E Y (q.abelian Y))
    (NY : SpNormalizedEquivalence l E Y (q.abelian Y) RY)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q (SpTowerGamma.factorization j p)).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (a : SpTowerGluing.support l E b o q (SpTowerGamma.factorization j p) hF ⊣ G)
    (lv : SpTowerGluing.Levels l E b o q (SpTowerGamma.factorization j p) hF G a) :
    Nonempty (reconstructionResult l E D j p b o q RX NX RY NY hF G a) := by
  sorry

end AlgebraicGeometry.ProEtale.SpIntegralAdjunction
