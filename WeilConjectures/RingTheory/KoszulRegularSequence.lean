/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulComplex

/-!
# Koszul-regular and H₁-regular sequences

Source: Stacks Project, More on Algebra, Definition 15.31.1, Tag 062E
(blueprint: def-weil-pbc-koszul-regular-sequence).

The Koszul complex is indexed by `ℕ`, with negative degrees zero by the extension
convention of def-weil-pbc-module-chain-complex-homology. Vanishing in all nonzero
integer degrees therefore means vanishing in all nonzero natural degrees.
The module-valued homology is Mathlib's kernel-modulo-image homology; `IsZero`
expresses that this module is zero, without requiring a chosen equality to a zero object.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace RingTheory.Sequence

end RingTheory.Sequence
