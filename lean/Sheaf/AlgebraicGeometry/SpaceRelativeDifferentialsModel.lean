/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Sheaf.CategoryTheory.Sites.InverseImageDifferentials

/-! # Relative differentials on the small étale site of an algebraic space

Source: Stacks Project, More on Morphisms of Spaces, Tag 04CT; Modules on Sites,
Tags 04BN, 04BQ and 08TP (blueprint: def-sfb-space-relative-differentials-model).

The record specifies the differential module by its full universal property in sheaves.
The derivation and structural ring map are the existing constructions, rather than
an unrelated linearization or an arbitrary comparison map.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- A relative differential sheaf with its universal derivation. The inverse-image
structural map is the canonical chart-normalized one. Universality is in module
SHEAVES, not in all presheaves, and determines this record up to the unique isomorphism
respecting the derivation. This is a presentation of Ω¹, not an additional finiteness
or smoothness condition.
Source: Stacks, Tags 04CT, 04BN and 04BQ
(blueprint: def-sfb-space-relative-differentials-model). -/
structure SpaceRelativeDifferentialsModel {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) where
  /-- The relative differential module on the existing small étale site. -/
  omega : X.Modules
  /-- The universal relative derivation for f⁻¹ O_Y → O_X. -/
  derivation : PresheafOfModules.Derivation' (R := X.etaleForget.op ⋙ Scheme.Γ)
    omega.val (cotangentFullRingMap f).hom
  /-- Composition with d is bijective for every module sheaf. -/
  universal (N : X.Modules) : Function.Bijective
    (fun h : omega ⟶ N ↦ derivation.postcomp h.val)

end AlgebraicGeometry.AlgebraicSpace
