/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.RingTheory.MPseudoCoherent
public import Sheaf.RingTheory.RingPseudoCoherent
import Sheaf.RingTheory.FiniteHomologyOfMPseudoCoherent
import Sheaf.RingTheory.PseudoCoherentDistinguishedTriangle

/-!
# Pseudo-coherence and degreewise pseudo-coherence

Source: Stacks Project, More on Algebra, Lemma 15.66.5, Tag 064U
(blueprint: lem-pc-ring-pseudo-coherent-iff-all-m).
-/

@[expose] public section

universe w v u

open CategoryTheory

namespace DerivedCategory

/-- Truncating a bounded-above finite-free model below `m` proves the forward implication.
Conversely, 0-pseudo-coherence gives an upper cohomology bound `b`. Start with the zero
complex in degree `b + 1` and descend. For a stage-`n` map `F → C`, its cone vanishes in
degrees at least `n`. The bounded finite-free stage complex is `n`-pseudo-coherent
via its identity, and `C` is `(n - 1)`-pseudo-coherent by hypothesis. The first clause
of the distinguished-triangle lemma, with `m = n - 1`, therefore makes the cone
`(n - 1)`-pseudo-coherent, and the finite-cohomology lemma makes its degree-`n - 1`
cohomology finite. Thus the kernel of `Hⁿ(F) → Hⁿ(C)` is finite. Add a finite free term
in degree `n - 1` mapping onto this kernel through cocycles of `Fⁿ`; lift its image in
`Cⁿ` to `Cⁿ⁻¹`. This makes the degree-`n` map an isomorphism. The new cone again has
finite degree-`n - 1` cohomology, so the cokernel of `Hⁿ⁻¹(F) → Hⁿ⁻¹(C)` is finite.
Choose cocycles generating this cokernel and adjoin `R^r` to `Fⁿ⁻¹`, mapping its basis
to those cocycles in `Cⁿ⁻¹` and to zero in `Fⁿ`. This gives surjectivity in degree
`n - 1`. Repeating produces a bounded-above finite-free model quasi-isomorphic to `C`.
Source: Stacks Project, More on Algebra, Lemma 15.66.5, Tag 064U; proof dependencies:
lem-pc-ring-pseudo-coherent-distinguished-triangle and lem-sc-finite-cohomology
(blueprint: lem-pc-ring-pseudo-coherent-iff-all-m). -/
theorem isPseudoCoherent_iff_forall_isMPseudoCoherent (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (C : CochainComplex (ModuleCat.{v} R) ℤ) :
    IsPseudoCoherent (Q.obj C) ↔ ∀ m : ℤ, IsMPseudoCoherent m (Q.obj C) := by
  sorry

end DerivedCategory
