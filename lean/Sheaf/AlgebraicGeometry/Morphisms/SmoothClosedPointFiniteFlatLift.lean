/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.RingHom.Etale

/-!
# Finite flat rationalization of a smooth closed-fibre point

Source: Stacks Project, Tag 0EYB, the residue extension base change; Tag 07NE.
(blueprint: lem-sbc-smooth-closed-point-finite-flat-lift)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- A finite flat local base change makes the prescribed closed-fibre point separable.

Source: Stacks Project, Tag 0EYB, the first base change; Tag 07NE.
(blueprint: lem-sbc-smooth-closed-point-finite-flat-lift)

Proof: The smooth fibre is locally of finite type over the residue field of A.
Closedness of x and the Nullstellensatz make its residue extension finite. Apply
07NE to this extension and the maximal ideal of A. Its finite free algebra A' has
prime extended maximal ideal and quotient the prescribed residue field. Integrality
puts every maximal ideal above the maximal ideal of A, so A' is local. The finite
module over the Noetherian ring A is Noetherian, and freeness gives flatness. The
identity on the chosen residue field gives a rational point y of the base-changed
fibre above x. Its residue field equals the base residue field, so the residue map
of the base-changed smooth morphism at y is an isomorphism and hence etale. The
finite free construction uses successive monic polynomial quotients, so stays in
Type u. Empty fibres have no x; no separability of the original extension is used.
This statement constructs no section and makes no etale-slice assertion. -/
theorem exists_smooth_closed_point_finite_flat_lift
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {L : Scheme.{u}} (q : L ⟶ Spec (.of A)) [Smooth q]
    (x : q.fiber (IsLocalRing.closedPoint A)) (hx : IsClosed ({x} : Set _)) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : IsLocalRing A') (_ : IsNoetherianRing A'),
      ∃ (α : A →+* A'), IsLocalHom α ∧ α.Flat ∧
        IsFinite (Spec.map (CommRingCat.ofHom α)) ∧
        ∃ y : (pullback q (Spec.map (CommRingCat.ofHom α)) : Scheme.{u}),
          pullback.fst q (Spec.map (CommRingCat.ofHom α)) y =
            q.fiberι (IsLocalRing.closedPoint A) x ∧
          pullback.snd q (Spec.map (CommRingCat.ofHom α)) y =
            IsLocalRing.closedPoint A' ∧
          ((pullback.snd q (Spec.map (CommRingCat.ofHom α))).residueFieldMap y).hom.Etale
    := by sorry

end AlgebraicGeometry.Scheme
