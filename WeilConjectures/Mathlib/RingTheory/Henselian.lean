/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Henselian

/-!
# Strictly Henselian local rings

A local ring is *strictly Henselian* if it is Henselian and its residue field is separably
closed. The main example is the strict henselization of a scheme at a geometric point, see
`AlgebraicGeometry.Scheme.strictHenselization`.
-/

@[expose] public section

/-- A local ring is *strictly Henselian* if it is Henselian and its residue field is
separably closed. -/
class IsStrictlyHenselianLocalRing (R : Type*) [CommRing R] : Prop
    extends HenselianLocalRing R where
  isSepClosed_residueField : IsSepClosed (IsLocalRing.ResidueField R)

instance (R : Type*) [CommRing R] [IsStrictlyHenselianLocalRing R] :
    IsSepClosed (IsLocalRing.ResidueField R) :=
  IsStrictlyHenselianLocalRing.isSepClosed_residueField

/-- A local ring is strictly Henselian if and only if it is Henselian and its residue
field is separably closed. -/
theorem isStrictlyHenselianLocalRing_iff (R : Type*) [CommRing R] [IsLocalRing R] :
    IsStrictlyHenselianLocalRing R ↔
      HenselianLocalRing R ∧ IsSepClosed (IsLocalRing.ResidueField R) :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun h ↦ have := h.1; ⟨h.2⟩⟩
