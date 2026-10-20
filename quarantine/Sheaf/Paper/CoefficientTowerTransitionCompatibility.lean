/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K6
-/
module

public import Sheaf.Paper.CoefficientTowerShriekInterfaces
import Sheaf.Paper.SmoothPurityCoefficientTowersAbelian
import Sheaf.Paper.SemilinearDerivedSections
import Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction
import Sheaf.SecSmoothPurity.RestrictionTransitionTranspose

/-! # Compatibility of actual tower transitions

Source: blueprint Local pairs and Levels, coefficient tower shriek calculus.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerCalculus

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The actual compact-support transition and its scalar-adjunction transpose.
Source: blueprint Levels, step 7; Stacks 07A6, 0D6D and 0D6E.
Proof: write each strict transition as a map to restriction of scalars. The
semilinear direct-image transition formula and the compact-support restriction
comparison express the output transition as F(t) followed by that comparison.
The scalar coordinate unit equation identifies its transpose with the recorded
reduction map. Apply the restriction-transition transpose identity to obtain the
displayed equality. This assertion is about the actual transitions, not only their
sources and targets or their evaluations. No flatness of the quotient is used.
Identity, composition and naturality of input reduction are separate formal laws.
(blueprint: lem-sp-tower-transition-compatibility). -/
theorem reduction_transition_compatibility
    (pchar : ℕ) (hp : 0 < pchar) (hne : pchar ≠ l)
    (k : Type u) [Field k] [CharP k pchar]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (z : FiniteCoordinates l E)
    (finiteData : FiniteNormalization l E k b o q z) :
    (∀ {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (K : C l E b q X) {m n : ℕ} (v : m ≤ n),
    (scalarExtensionFunctor (quotient l E v) Y).map
        ((finiteData.evaluation c n).comparison.hom.app K.obj) ≫
      (reductionDirectImageComparison (quotient l E v) c.i c.g).app
        ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj K.obj) ≫
      (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).map
        (reduction l E X (q.abelian X) v (q.scalar X v) K.obj) =
    reduction l E Y (q.abelian Y) v (q.scalar Y v) ((F l E b o q c).obj K.obj) ≫
      (finiteData.evaluation c m).comparison.hom.app K.obj) := by
  sorry


end AlgebraicGeometry.ProEtale.SpTowerCalculus

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
