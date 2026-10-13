/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # A generically nonempty closed subset has nonempty nearby fibres

Source: Stacks Project, Tag 055G, intersection-image argument.
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- A single closed subset meeting the generic fibre meets every nearby fibre.

Source: Stacks Project, Tag 055G, argument for the nonempty intersections;
Tags 052A and 01UA.
Proof: the generic-point hypothesis makes T irreducible. Replace it by its reduction,
which is integral, and pull back P and C. Give C its reduced closed subscheme
structure. Its map to the reduced base is finite type since a closed immersion is
finite type. Its generic fibre is nonempty. Generic flatness, Tag 052A, gives a
nonempty affine open on which this map is flat and of finite presentation. Its
image is open by Tag 01UA and contains the generic point. This image is an open
neighbourhood on which every fibre meets C. Transfer it back to T along the
reduction homeomorphism. Fibres over corresponding points have the same underlying
sets, so the resulting open has the stated property. C cannot be empty by the
hypothesis; P need not be reduced or separated, and no assumption of noetherianity
on T is needed.

(blueprint: lem-sbc-generic-closed-subset-fibre-nonempty) -/
theorem exists_open_closed_subset_fibre_nonempty {P T : Scheme.{u}} (h : P ⟶ T)
    [LocallyOfFiniteType h] [QuasiCompact h] (η : T)
    (hη : IsGenericPoint η Set.univ) (C : Set P) (hC : IsClosed C)
    (hne : (C ∩ h ⁻¹' {η}).Nonempty) :
    ∃ V : Set T, IsOpen V ∧ η ∈ V ∧
      ∀ t ∈ V, (C ∩ h ⁻¹' {t}).Nonempty := by sorry

end AlgebraicGeometry
