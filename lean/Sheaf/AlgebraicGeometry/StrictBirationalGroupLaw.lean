/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Monoidal.Grp

/-!
# Strict relative birational group laws

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, 5.1 Definition 1,
5.2 Definition 1, and 6.5 Corollary 2 (blueprint: def-sfb-strict-birational-group-law).

A strict law is represented by its common translation chart. Open immersions encode
isomorphisms onto open subschemes. All three images are dense in every fibre of both
projections. Associativity is equality of morphisms on the common domain, expressed
on arbitrary scheme-valued points, including nonreduced test schemes.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-- Fibrewise topological density of a subset, using scheme-theoretic fibres.
Source: BLR, 2.5 and 5.2 Definition 1 (blueprint: def-sfb-strict-birational-group-law). -/
def IsFibrewiseDense {Y S : Scheme.{u}} (f : Y ⟶ S) (A : Set Y) : Prop :=
  ∀ s : S, Dense ((f.fiberι s) ⁻¹' A)

/-- A representative of a strict relative birational group law on `X`.
Source: BLR, 5.1 Definition 1 and 5.2 Definition 1
(blueprint: def-sfb-strict-birational-group-law).

The domain is an open subscheme of `X ×_S X`. The two translation maps are open
immersions, so are isomorphisms onto their open images. The six density fields say
that the domain and both images are dense in every fibre of each projection.
The final field says `(xy)z = x(yz)` whenever all four products are defined.
This representative formulation quantifies over every possible strict chart;
no choice of a maximal domain or of a rational-map quotient is required. -/
structure StrictBirationalGroupLaw {S : Scheme.{u}} (X : Over S) where
  /-- The open domain as a scheme over the base. -/
  domain : Over S
  /-- Its inclusion in the relative square. -/
  inclusion : domain ⟶ X ⊗ X
  /-- The domain is an open subscheme. -/
  open_inclusion : IsOpenImmersion inclusion.left
  /-- The partially defined multiplication, over the base. -/
  mul : domain ⟶ X
  /-- The left translation chart `(x,y) ↦ (x,xy)` is an open immersion. -/
  open_left : IsOpenImmersion (lift (inclusion ≫ fst X X) mul).left
  /-- The right translation chart `(x,y) ↦ (xy,y)` is an open immersion. -/
  open_right : IsOpenImmersion (lift mul (inclusion ≫ snd X X)).left
  /-- The domain is dense in every fibre of the first projection. -/
  domain_dense_fst : IsFibrewiseDense (fst X X).left (Set.range inclusion.left)
  /-- The domain is dense in every fibre of the second projection. -/
  domain_dense_snd : IsFibrewiseDense (snd X X).left (Set.range inclusion.left)
  /-- The left chart image is dense in every fibre of the first projection. -/
  left_dense_fst : IsFibrewiseDense (fst X X).left
    (Set.range (lift (inclusion ≫ fst X X) mul).left)
  /-- The left chart image is dense in every fibre of the second projection. -/
  left_dense_snd : IsFibrewiseDense (snd X X).left
    (Set.range (lift (inclusion ≫ fst X X) mul).left)
  /-- The right chart image is dense in every fibre of the first projection. -/
  right_dense_fst : IsFibrewiseDense (fst X X).left
    (Set.range (lift mul (inclusion ≫ snd X X)).left)
  /-- The right chart image is dense in every fibre of the second projection. -/
  right_dense_snd : IsFibrewiseDense (snd X X).left
    (Set.range (lift mul (inclusion ≫ snd X X)).left)
  /-- Associativity on the common domain, as an equality of morphisms. -/
  assoc : ∀ (T : Over S) (a b c d : T ⟶ domain),
    a ≫ inclusion ≫ snd X X = b ≫ inclusion ≫ fst X X →
    c ≫ inclusion ≫ fst X X = a ≫ mul →
    c ≫ inclusion ≫ snd X X = b ≫ inclusion ≫ snd X X →
    d ≫ inclusion ≫ fst X X = a ≫ inclusion ≫ fst X X →
    d ≫ inclusion ≫ snd X X = b ≫ mul →
    c ≫ mul = d ≫ mul

/-- A smooth separated finite-type group realization of a strict-law representative.
Source: BLR, 5.2 Theorem 3 and 6.5 Corollary 2
(blueprint: def-sfb-strict-birational-group-law).
The group axioms are those of Mathlib's group object in `Over S`; compatibility
with the partial multiplication is an equality on its entire open domain. -/
def StrictBirationalGroupLaw.Realizes {S : Scheme.{u}} {X : Over S}
    (m : StrictBirationalGroupLaw X) (H : Grp (Over S)) (i : X ⟶ H.X) : Prop :=
  Smooth H.X.hom ∧ IsSeparated H.X.hom ∧ LocallyOfFiniteType H.X.hom ∧
    QuasiCompact H.X.hom ∧ IsOpenImmersion i.left ∧
    IsFibrewiseDense H.X.hom (Set.range i.left) ∧
    m.mul ≫ i = m.inclusion ≫ (i ⊗ₘ i) ≫ μ[H.X]

end AlgebraicGeometry
