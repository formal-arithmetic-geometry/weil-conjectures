/-
Copyright (c) 2026 Q89. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q89
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Fibrewise birational extensions

Source: BLR, Néron Models, 2.5 and 4.3 Proposition 4(iii)
(blueprint: def-sfb-fiberwise-birational-extension).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An open is dense in every scheme-theoretic fibre. Source: BLR 2.5
(blueprint: def-sfb-fiberwise-birational-extension). -/
def IsFiberwiseDenseOpen {S : Scheme.{u}} (X : Over S) (U : X.left.Opens) : Prop :=
  ∀ s : S, Dense ((X.hom.fiberι s) ⁻¹' (U : Set X.left))

/-- A map on the indicated generic base change extends to a fibrewise birational map
which is an open immersion on its full domain of definition. The first equality says
that the representative extends the specified map. Fibrewise density of its domain
and image makes the open immersion an isomorphism between base-dense opens.
The last clause says its domain contains every other domain on which that generic map
extends. This encodes the maximal domain, rather than only one birational representative.
Source: BLR 2.5, 4.3 Proposition 4(iii)
(blueprint: def-sfb-fiberwise-birational-extension). -/
def HasFiberwiseBirationalExtension {S T : Scheme.{u}} (q : T ⟶ S) (X : Over S)
    (t : (Over.pullback q).obj X ⟶ (Over.pullback q).obj X) : Prop :=
  ∃ (U : X.left.Opens) (f : Over.mk (U.ι ≫ X.hom) ⟶ X),
    (Over.pullback q).map f =
      (Over.pullback q).map (Over.homMk U.ι) ≫ t ∧
    IsFiberwiseDenseOpen X U ∧ IsOpenImmersion f.left ∧
    (∀ s : S, Dense ((X.hom.fiberι s) ⁻¹' Set.range f.left)) ∧
    ∀ (V : X.left.Opens) (h : Over.mk (V.ι ≫ X.hom) ⟶ X),
      (Over.pullback q).map h =
        (Over.pullback q).map (Over.homMk V.ι) ≫ t → V ≤ U

end AlgebraicGeometry
