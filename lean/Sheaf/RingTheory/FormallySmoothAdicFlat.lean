/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Sheaf.RingTheory.FormallySmoothAdic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.RingHom.Flat

/-!
# Flatness of adically formally smooth local ring maps

Source: Stacks Project, More on Algebra, Lemma 15.41.3 (Tag 07NP), using
Definition 15.38.3 (Tag 07NI) (blueprint: lem-weil-pbc-fs-adic-local-flat).
-/

universe u v

namespace RingHom

/-- A local homomorphism of Noetherian local rings that is formally smooth for the
maximal-ideal-adic topology on its target is flat (Stacks Project, Tag 07NP).
The algebra structure in the hypothesis is the one induced by the given ring map.
(blueprint: lem-weil-pbc-fs-adic-local-flat)

Proof following the six steps of the node:
1. Pass to the maximal-ideal completions. They are Noetherian complete local rings by
`lem-weil-pbc-local-completion-local-ring`, `lem-weil-pbc-adic-completion-noetherian`, and
`lem-weil-pbc-adic-completion-mod-ideal`. Formal smoothness passes to the induced map by
`lem-weil-pbc-fs-adic-complete-source-target`.
2. In the complete case, use `lem-weil-pbc-complete-local-flat-presentation` to obtain
surjections `R → A` and `S → B` between complete Noetherian local rings, with `R → S` flat.
For `I = ker(R → A)`, the second surjection factors as `q : S/IS → B`.
3. By `lem-weil-pbc-tensor-quotient-base-change`, `S/IS` is `S ⊗[R] A`; it is flat over `A`
by `lem-weil-pbc-flat-module-base-change`.
4. Put `C = S/IS` and `J = ker q`. The ring `C` is complete local by
`lem-weil-pbc-complete-local-quotient`. Locality and surjectivity give `q(m_C) = m_B`, hence
`q⁻¹(m_B^n) = J + m_C^n`. Since `B` is separated, their intersection is `J`, so `J` is
closed and contained in `m_C`. The identity of `B = C/J` is continuous. Apply
`lem-weil-pbc-fs-adic-lift-into-complete` with ideal of definition `m_C` and `t = 1` to
obtain an `A`-algebra section of `q`.
5. Thus `B` is a retract of the flat `A`-module `C`, and is flat by
`lem-weil-pbc-flat-module-retract`.
6. For the original rings, `A → Â` is flat and `B → B̂` is faithfully flat by
`lem-weil-pbc-local-completion-faithfully-flat`. The composite `A → Â → B̂` is flat by
`lem-weil-pbc-flat-ring-map-comp`, so `lem-weil-pbc-flat-permanence` descends flatness
from `B̂` to `B`. -/
theorem flat_of_formallySmoothAdic {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B] (φ : A →+* B) [IsLocalHom φ]
    (h : letI : Algebra A B := φ.toAlgebra
      Algebra.FormallySmoothAdic A B (IsLocalRing.maximalIdeal B)) :
    φ.Flat := by
  sorry

end RingHom
