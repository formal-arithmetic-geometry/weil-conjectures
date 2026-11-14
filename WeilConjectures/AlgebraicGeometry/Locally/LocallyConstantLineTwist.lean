/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.CategoryTheory.Monoidal.TensorInverse
public import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Line bundles raised to locally constant integer powers

Source: EGA II, Remark 4.2.7; Stacks Project, Sheaves, Tags 00AL and 00AM.

The product of direct images from disjoint open degree strata is a concrete model
of gluing: over any open its sections are the product of the sections on the strata.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical dual supplies the tensor inverse, with the evaluation isomorphism.
Source: Stacks, Tag 01CR; EGA II, Remark 4.2.7. -/
noncomputable def lineTensorInverse {X : Scheme.{u}} (A : X.Modules)
    (hA : A.IsInvertible) : TensorInverse A :=
  @TensorInverse.mk X.Modules _ _ A (dual A)
    (@asIso _ _ _ _ (dualEvaluation A) (@isIso_dualEvaluation X A hA))
    ((β_ (dual A) A) ≪≫
      @asIso _ _ _ _ (dualEvaluation A) (@isIso_dualEvaluation X A hA))

/-- The integer power uses the existing monoidal integer powers, with the dual for
negative exponents. Source: EGA II, Remark 4.2.7; Stacks, Tag 01CR. -/
noncomputable def integerLinePower {X : Scheme.{u}} (A : X.Modules)
    (hA : A.IsInvertible) (m : ℤ) : X.Modules :=
  (lineTensorInverse A hA).zpow m

/-- The open degree-m stratum, including empty strata.
Source: Stacks, Tags 00AL and 00AM. -/
def lineDegreeOpen {X : Scheme.{u}} (d : LocallyConstant X ℤ) (m : ℤ) : X.Opens :=
  ⟨{x | d x = m}, d.isLocallyConstant.isOpen_fiber m⟩

/-- Glue the integer powers across disjoint degree strata by their actual direct-image
product. No line bundle is chosen from an existence assertion.
Source: EGA II, Remark 4.2.7; Stacks, Tags 00AL and 00AM. -/
noncomputable def locallyConstantLineTwist {X : Scheme.{u}} (A : X.Modules)
    (hA : A.IsInvertible) (d : LocallyConstant X ℤ) : X.Modules :=
  ∏ᶜ fun m : ℤ ↦ (pushforward (lineDegreeOpen d m).ι).obj
    ((tensorPullback (lineDegreeOpen d m).ι).obj (integerLinePower A hA m))

end AlgebraicGeometry.Scheme.Modules
