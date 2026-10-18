/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Sheaf.Algebra.Homology.LocalCohomologicalDimension

/-! # Local cohomological dimension under change of rings

Source: Stacks Project, Local Cohomology, Tag 0DXA (lemma-cd-change-rings),
restricted to commutative Noetherian rings
(blueprint: lem-per-local-cohomology-change-rings).
-/

@[expose] public section

universe u v

namespace ModuleCat

/-- Local cohomological dimension does not increase under an arbitrary homomorphism
of commutative Noetherian rings. The extended ideal is `I.map f`. The dimension uses
right derived ideal-power torsion, and its bottom value represents `-1`.
Source: Stacks Project, Tag 0DXA; the restriction comparison is Tag 0BJB, and the
Noetherian derived-torsion Cech computation is Tag 0956
(blueprint: lem-per-local-cohomology-change-rings).

Proof: Choose a finite list `t₁, …, tᵣ` generating `I`, using Noetherianity
(def-weil-pbc-noetherian-ring). Its images generate `I.map f`, including the empty list.
For any `B`-module `N`, compute both its local cohomology over `B` and that of its
restriction over `A` by the extended alternating localization complexes
(lem-per-ideal-torsion-cech-computation). These finite complexes also show that the
least integers defining the two dimensions exist. For every nonempty ordered subset
of the generators, identify the localized restricted module with the restriction of
the localized `B`-module by sending `n/tˢ` to `n/f(t)ˢ`. The fraction equality test is
the same on both sides, even if `f(t) = 0`, so the reverse formula is an inverse.
These identifications commute with all face localization maps and their alternating
signs; together with the identity in degree zero they give a cochain isomorphism.
Restriction of scalars preserves the kernels, images, and quotient additive groups,
so it identifies the local cohomology groups. Thus every degree above `cd(A,I)`
vanishes for every `B`-module, and `cd(A,I)` is an admissible bound for `cd(B,IB)`.
The all-modules vanishing criterion of Tag 0DX7 is independent of the module size
universe (equivalently it can be tested on the coefficient ring itself), so the
small-module dimension encoding gives this same comparison for independent `u`, `v`.
The argument includes dimension `-1`, the empty generating list, and zero rings.
No tensoring of exact sequences or flatness assumption is used. -/
theorem localCohomologicalDimension_map_le
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (f : A →+* B) (I : Ideal A) :
    localCohomologicalDimension (I.map f) ≤ localCohomologicalDimension I := by
  sorry

end ModuleCat
