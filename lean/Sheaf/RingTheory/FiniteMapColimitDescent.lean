/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Descent of finiteness of an algebra map along a directed ring colimit

Source: Stacks Project, Algebra, Lemma 10.168.3 (Tag 07RG)
(blueprint: lem-weil-pbc-colimit-finite-ring-map).
-/

@[expose] public section

universe u v t

open CategoryTheory CategoryTheory.Limits

namespace RingHom

/-- A finite type algebra map whose base change to a directed colimit is finite
is already finite after base change to some stage above the initial stage.
Source: Stacks Project, Algebra, Lemma 10.168.3 (Tag 07RG)
(blueprint: lem-weil-pbc-colimit-finite-ring-map).

Proof:
1. Choose finitely many generators of `C₀` over `B₀`. Their tensors with `1` generate
   every base change, and the tensor-product transition maps commute with the algebra maps.
2. Finiteness at the colimit implies integrality of these generators
   (`lem-weil-pbc-finite-algebra-is-integral`), giving monic annihilating polynomials.
3. Lift their finitely many coefficients to a common stage by
   `lem-weil-pbc-directed-colimit-base-change-elementwise`, part (1), and directedness.
4. Their evaluations vanish at the colimit, so part (2) of the same lemma makes them
   vanish at a common later stage. Thus all the base-changed generators are integral there.
5. Apply `lem-weil-pbc-finite-of-integral-generators`: a finite type algebra generated
   by integral elements is finite as a module. -/
theorem exists_finite_tensorProductMap_of_colimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F] (i₀ : I)
    (B₀ : Type v) (C₀ : Type t) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (φ₀ : B₀ →ₐ[F.obj i₀] C₀) (hft : φ₀.FiniteType) :
    letI : Algebra (F.obj i₀) (colimit F : CommRingCat.{u}) :=
      (CommRingCat.Hom.hom (colimit.ι F i₀)).toAlgebra
    (Algebra.TensorProduct.map
      (AlgHom.id (F.obj i₀) (colimit F : CommRingCat.{u})) φ₀).Finite →
      ∃ (i : I) (h : i₀ ≤ i),
        letI : Algebra (F.obj i₀) (F.obj i) :=
          (CommRingCat.Hom.hom (F.map (homOfLE h))).toAlgebra
        (Algebra.TensorProduct.map (AlgHom.id (F.obj i₀) (F.obj i)) φ₀).Finite :=
  sorry

end RingHom
