/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
module

public import Submission.WeilConjectures.Mathlib.Topology.JacobsonSpace
public import Submission.WeilConjectures.Mathlib.Topology.Spectral.Basic
public import Submission.WeilConjectures.Topology.SpectralSpace.WLocal.Basic
public import Submission.WeilConjectures.Topology.SpectralSpace.Constructible

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Closed Points of w-local spaces is profinite

-/

@[expose] public section

variable {X : Type*} [TopologicalSpace X]

namespace WLocalSpace

instance spectralSpace_closedPoints [WLocalSpace X] : SpectralSpace (closedPoints X) :=
  SpectralSpace.of_isClosed X

instance t1Space_closedPoints : T1Space (closedPoints X) where
  t1 := closedPoints.isClosed_singleton

instance CompactSpace_closedPoints [WLocalSpace X] :
    CompactSpace (closedPoints X) :=
  (IsClosed.isClosedEmbedding_subtypeVal inferInstance).compactSpace

end WLocalSpace
