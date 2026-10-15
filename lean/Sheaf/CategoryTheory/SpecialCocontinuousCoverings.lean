/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings

/-!
# Special cocontinuous functors between sites

Source: Stacks Project, Definitions 00XJ and 03CG, Lemma 03A0, conditions (1)-(5)
(blueprint: def-weil-pbc-special-cocontinuous-functor).

Cocontinuity itself is `Functor.IsCocontinuous` for the generated topologies.
The remaining conditions use the actual covering presieves, not their saturation.
-/
