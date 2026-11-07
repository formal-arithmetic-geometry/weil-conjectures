/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalizationDataSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleCompactSupportGraphSheafNormalization
public import Submission.WeilConjectures.SixFunctors.BaseChange.Etale
public import Submission.WeilConjectures.ConstructibleSheaf.EtaleMorphismDescent
import Submission.WeilConjectures.AlgebraicGeometry.EtaleCompactSupportFiniteGraphIso
import Submission.WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalizationDataSupplement
import Submission.WeilConjectures.AlgebraicGeometry.EtaleCompactSupportGraphSheafNormalization
import Submission.WeilConjectures.SixFunctors.BaseChange.Etale
import Submission.WeilConjectures.ConstructibleSheaf.EtaleMorphismDescent
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import Submission.WeilConjectures.AlgebraicGeometry.EtaleCompactSupportGraphGeometricBaseChange
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Submission.WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
import Submission.WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekBaseChange
import Submission.WeilConjectures.SixFunctors.Etale.Derived.BaseChangeCube
import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import Submission.WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Local
import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import Submission.WeilConjectures.SixFunctors.OpenClosed.Conservative
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleCompactSupportGraphDerivedIso

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Invertibility of the graph comparison on unbounded complexes

Source: SGA 4 XVII 5.2.2 and 6.2.11; Stacks Project Tags 03S6 and 0F0C
(blueprint: lem-asd-compact-support-graph-derived-isomorphism).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Core data from the specified graph map, with its forced inverse and termwise descent.
Source: SGA 4 XVII 6.2.11
(blueprint: lem-asd-compact-support-graph-derived-isomorphism). -/
noncomputable def canonicalEtaleCompactSupportCore
    (A : Type (u + 1)) [CommRing A] [Finite A] : EtaleCompactSupportCore A where
  comparison := fun f _ _ _ _ _ _ c ↦ canonicalEtaleCompactSupportComparison A f c
  sheafComparison := fun f _ _ _ _ _ _ c => etaleCompactificationGraphMap A f c
  sheaf_normalization := fun f _ _ _ _ _ _ c M =>
    compactSupportGraphSheafComparison_normalization A f c M
  derived_normalization := by
    intro U X f hf hs hU hUc hX hXc c K
    exact compactSupportDerivedComparison_app A f c (etaleCompactificationGraphMap A f c) K

end AlgebraicGeometry.Etale
