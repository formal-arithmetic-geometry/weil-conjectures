/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulRegularSequence
public import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import WeilConjectures.RingTheory.KoszulTensorConeCoordinates
import WeilConjectures.RingTheory.KoszulTensorZerothBoundarySaturation

/-!
# Regular sequences are Koszul-regular

Source: Stacks Project, More on Algebra, Lemma 15.31.2 (Tag 062F)
(blueprint: lem-weil-pbc-regular-sequence-koszul-regular).

Successive injectivity is Mathlib's `IsWeaklyRegular`; it does not require the final
quotient to be nonzero. `List.ofFn f` lists the given finite sequence in its original order.
The homology and Koszul complexes are those of the dependency modules, with negative
terms zero by their extension convention.
-/

@[expose] public section

universe u v

namespace RingTheory.Sequence

end RingTheory.Sequence
