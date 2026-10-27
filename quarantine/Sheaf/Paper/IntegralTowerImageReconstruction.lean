/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B8
-/
module

public import Sheaf.Paper.IntegralDirectImageTowerData

import Sheaf.Paper.SmoothPurityReductionTowerNormalized
import Sheaf.Paper.SmoothPurityTowerShriekLevels
import Sheaf.Paper.CompactSupportUniformTorBound
import Sheaf.Paper.ShriekNormalizedTransitionComparison
import Sheaf.SecSmoothPurity.ReductionDirectImage
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.Paper.CompleteCompactificationLimitRealization
import Sheaf.Paper.SmoothPurityTowerReconstruction
import Sheaf.Paper.SmoothPurityNormalizedEquivalence
import Sheaf.Paper.IntegralModels
import Sheaf.Paper.CompletedCondensedCoefficients

/-! # Components of the integral direct-image tower argument -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Normalized compact-support towers, their Tor bounds, and canonical integral reconstruction.
Source: blueprint latest direct-image.proof.md paragraphs (1) and (2).
Proof: reduce M using the normalized reduction theorem. Tower shriek levels and the uniform
bound theorem give finite constructibility and widen each Tor interval by 2d. Each transition
is the finite coefficient direct-image comparison composed with direct image of the input
transition, hence invertible. Complete compactification/limit realization commutes the two
separately derived factors with the scalar-restricted strict inverse limit: the proper factor
is a right adjoint and quasi-compact open extension is exact and preserves products. The
input is complete by the integral-model criterion. Tower reconstruction gives integral
constructibility of the limit. The normalized equivalence identifies its reduction with
the original normalized strict tower. The actual ordinary and derived adjunction
normalizations identify this isomorphism with the constructed proper/open mate, rather than
only its evaluations. Its inverse limit after the completion unit is reconstruction, hence
invertible. Transport constructibility across that isomorphism. The empty-source image and
the zero input are zero, so all assertions and arbitrary Tor-interval bounds remain valid.
(blueprint: lem-sp-integral-tower-image-reconstruction). -/
theorem image_reconstruction (s : Presentation l E)
    (q : ReductionGeometry l E s) (hq : OpenReductionIsIso l E s q)
    (L : ∀ T : Scheme.{u}, Limit l E s T) :
    ∀ (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
      (X Y : Scheme.{u}) [X.Over (Spec (.of k))]
      [Y.Over (Spec (.of k))]
      [LocallyOfFiniteType (X ↘ Spec (.of k))]
      [QuasiCompact (X ↘ Spec (.of k))]
      [IsSeparated (X ↘ Spec (.of k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of k))]
      [QuasiCompact (Y ↘ Spec (.of k))]
      [IsSeparated (Y ↘ Spec (.of k))]
      (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
      (d : ℕ) [SmoothOfRelativeDimension d f],
    ∀ c : Compactification f,
      Nonempty (CanonicalTowerComparison l E s q hq c) ∧
      ∀ M : Constructible l E X,
        spNormalizedConstructibleTorTowers l E Y (s.towers Y)
          (imageTower l E s c M.obj) ∧
        (∀ a b : ℤ,
          DerivedCategory.torAmplitudeIn _ a b M.obj → ∀ n : ℕ,
          Scheme.HasProEtaleTorAmplitude Y (SpTowerShriek.R l E n)
            (imageLevel l E s c M.obj n) a (b + 2 * d)) ∧
        constantModelBoundedConstructible (spIntegralCondensed l E) Y
          ((shriek l E c).obj M.obj) ∧
        constantModelBoundedConstructible (spIntegralCondensed l E) Y
          ((lim l E s Y (L Y)).obj
            (imageTower l E s c M.obj)) ∧
        IsIso (reconstruction l E s c (L Y) q hq M)
 := by sorry

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower
