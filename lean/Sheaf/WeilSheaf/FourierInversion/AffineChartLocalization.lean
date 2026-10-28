/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.WeilSheaf.FourierInversion.ProjectiveLineRestriction
public import WeilConjectures.WeilSheaf.LowerShriek

/-! # The affine chart of the relative projective line -/

@[expose] public section

universe u
open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry.WeilComplex

/-- The compact-support localization triangle for the affine chart of the projective line
(blueprint: lem-pur-b3-weil-affine-localization).

Source: blueprint `sk-prop-an` (integration; recorded unit Step 5), the open-closed
triangle followed by proper direct
image), and `prop-sf-open-closed-triangle-all-stages`. Identify Y with the affine line over X
using the given cartesian square. Its standard compactification is the projective line over
X, with complementary closed section infinity. Apply the open-closed localization triangle
to q^*K. Proper direct image along q preserves distinguished triangles. The composition
comparison identifies its first term with Rπ_!π^*K and its last term with K, since infinity
is a section. The middle term is Rq_*q^*K by properness of q. Under these comparisons the
second arrow is restriction to infinity: use the counit description of restriction and the
adjunction identities. The first arrow is natural in K since it is the open counit followed
by proper direct image, and all comparison maps are natural. No calculation of projective
or affine cohomology is required for this localization statement. -/
theorem exists_affineChart_localization
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
    [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))]
    (π : Y ⟶ X) (s : Y ⟶ affineLine k₀)
    [π.IsOver (Spec (CommRingCat.of k₀))]
    (hπ : IsPullback π s (X ↘ Spec (CommRingCat.of k₀))
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] :
    ∃ α : upperStar π ⋙ derivedLowerShriek k₀ l π ⟶
        projectiveLineCohomology (k₀ := k₀) (l := l) X,
      ∀ K, ∃ w, Triangle.mk (α.app K) ((projectiveLineRestriction X).app K) w ∈
        distTriang (WeilComplex k₀ l X) := by sorry

end AlgebraicGeometry.WeilComplex
