/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral

/-!
# Compatibility import for the derived adjunction on ringed spaces

The adopted source library proves `AlgebraicGeometry.RingedSpace.derivedModulePullback_adjunction`
from concrete tensor pullback and its absolute left derived comparison. Re-export that
implementation to preserve the existing import path and the full derived adjunction.

Source: Stacks Project, Cohomology, Tags 06YJ and 079W.
(blueprint: lem-pc-ringed-spaces-derived-adjoint-general)
-/

@[expose] public section
