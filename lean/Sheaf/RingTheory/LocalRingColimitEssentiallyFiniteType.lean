/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Local rings as directed colimits of essentially finite type rings

Source: Stacks Project, Tag 00QU, proof (construction of the base-ring system).
(blueprint: lem-weil-pbc-local-ring-colimit-essentially-finite-type-over-z)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat

/-- Every local ring is a directed colimit in commutative rings of local rings essentially
of finite type over `ℤ`, with local transition maps and local cocone maps.
Source: Stacks Project, Tag 00QU, proof, base-ring construction; also Tag 00QT.
(blueprint: lem-weil-pbc-local-ring-colimit-essentially-finite-type-over-z)

Proof: Index by finite subsets `A` of `R`, including the empty subset; union supplies common
upper bounds. Let `C_A = ℤ[A]` and contract the maximal ideal of `R` to a prime `q_A` of `C_A`.
Localize `C_A` at `q_A` (def-weil-pbc-localization-at-prime). The resulting local ring `R_A`
is essentially of finite type over `ℤ`, since `A` generates `C_A`
(def-weil-pbc-finite-type-algebra, def-weil-pbc-essentially-finite-type-algebra).
For `A ⊆ B`, the fraction map `a/s ↦ a/s` is well defined: any denominator and any witness
of equality outside `q_A` remain outside `q_B`. This map preserves ring operations and
sends the maximal ideal into the maximal ideal. Its formula gives identity and composition.
Every denominator outside `q_A` is a unit in `R`
(lem-weil-pbc-local-ring-unit-criterion), so `a/s ↦ a * s⁻¹` defines a local ring map to `R`.
The fraction equality criterion proves well-definedness and compatibility. These maps are
injective: equality of images implies `at - bs = 0` already in the subring `C_A`.
Every `x : R` occurs at the singleton subset `{x}`. For any compatible cocone into any
commutative ring `T`, send an element of `R` to its image from any stage representing it.
Two representations agree in the union stage by injectivity into `R`, so this rule is
independent of the representation. Using a common stage proves it preserves sums and
products; the empty stage supplies zero and one. It factors the cocone maps and is unique
by the singleton representations, proving the universal property
(def-weil-pbc-category-colimit). -/
theorem exists_local_essFiniteType_colimit (R : Type u) [CommRing R] [IsLocalRing R] :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : I ⥤ CommRingCat.{u}) (π : F ⟶ (Functor.const I).obj (CommRingCat.of R)),
      (∀ i : I, IsLocalRing (F.obj i)) ∧
      (∀ (i j : I) (f : i ⟶ j), IsLocalHom (F.map f).hom) ∧
      (∀ i : I, IsLocalHom (π.app i).hom) ∧
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of R) π)) ∧
      (∀ i : I, Algebra.EssFiniteType ℤ (F.obj i)) := by
  sorry

end CommRingCat
