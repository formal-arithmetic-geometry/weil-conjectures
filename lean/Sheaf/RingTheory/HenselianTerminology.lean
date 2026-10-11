/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.IsSepClosed

/-!
# Henselian pairs, henselian and strictly henselian local rings

Source: Weil conjectures blueprint, proper base change, unit `sk-thm-iff`; Stacks Project,
Tags 09XE, 09XI (3) and 04GF (blueprint: def-weil-pbc-henselian-terminology).

The henselian pairs `(A, I)` of the node are Mathlib's `HenselianRing A I` (Stacks 09XE; the
node's idempotent-lifting wording is the equivalent condition 09XI (3)), and a henselian local
ring is Mathlib's `HenselianLocalRing A`, as the source module
`WeilConjectures.Mathlib.RingTheory.Henselian` fixes for this node. The one notion Mathlib
lacks is a strictly henselian local ring, defined here on Mathlib's class. For `T = Spec A`,
the closed subscheme `T₀ = Spec (A ⧸ I)` is `Spec (.of (A ⧸ I))`, with the closed immersion
`Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))`.

## Main definitions

* `IsStrictlyHenselianLocalRing`: a henselian local ring with separably closed residue field.
-/

universe u

/-- A local ring `A` is *strictly henselian* if it is henselian (Mathlib's
`HenselianLocalRing`) and its residue field is separably closed.
Source: Stacks Project, Algebra, Definition 10.153.1 (Tag 04GF)
(blueprint: def-weil-pbc-henselian-terminology). -/
def IsStrictlyHenselianLocalRing (A : Type u) [CommRing A] [IsLocalRing A] : Prop :=
  HenselianLocalRing A ∧ IsSepClosed (IsLocalRing.ResidueField A)
