/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Order.Directed

/-!
# Elements in tensor products over directed ring colimits

Source: Stacks Project, Algebra, Tags 00D6, 00D7, 00DD, as used in Tag 07RI
(blueprint: lem-weil-pbc-directed-colimit-base-change-elementwise).
-/

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace TensorProduct

/-- Base change along a directed ring colimit: every element of `colimit F ⊗[F.obj i₀] M₀`
comes from a stage `F.obj i ⊗[F.obj i₀] M₀` with `i₀ ≤ i`, and an element of a stage whose
image is zero already vanishes at a later stage. Source: Stacks Project, Algebra, Tags 00D6,
00D7 and 00DD, used in Tag 07RI
(blueprint: lem-weil-pbc-directed-colimit-base-change-elementwise).

The `F.obj i₀`-algebra structures on `F.obj i` (`i₀ ≤ i`) and on `colimit F` are those of
`F.map (homOfLE _)` and `colimit.ι F i₀`; the maps `μ_i = α_i ⊗ id` and
`μ_{i'i} = α_{i'i} ⊗ id` are `LinearMap.rTensor M₀` of these ring maps viewed as
`F.obj i₀`-algebra maps.

Proof:
1. Restrict to the upper tail `{i | i₀ ≤ i}`. It contains `i₀` and is directed.
   The ring transition maps and coprojections are `F.obj i₀`-linear by functoriality
   and cocone naturality. Tensoring them with the identity gives the module system
   and cocone (Tag 00D4).
2. The ring colimit is also the colimit of the upper-tail rings as base-ring modules:
   `lem-weil-pbc-filtered-colimit-algebras-elementwise` over the integers represents
   each ring element at a stage; directedness moves it above `i₀`. By
   `lem-weil-pbc-filtered-colimit-rings-zero`, equality holds at a common later stage.
   Thus compatible linear maps descend uniquely; addition and scalar multiplication
   are checked at a common stage (Tag 00D6).
3. Apply `lem-weil-pbc-tensor-commutes-with-colimits` (Tag 00DD) to tensor this
   module colimit with `M₀`. The resulting cocone is the module colimit, giving the
   equivalent parenthetical formulation in the node.
4. Apply `lem-weil-pbc-filtered-colimit-modules-elementwise` to this directed module
   colimit. Tag 00D6 gives representatives, and Tag 00D7 gives eventual vanishing.
-/
theorem directedColimitBaseChangeElementwise
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{v}) [HasColimit F]
    (i₀ : I) (M₀ : Type w) [AddCommGroup M₀] [Module (F.obj i₀) M₀] :
    let S := F.obj i₀
    let R := colimit F
    letI : Algebra S R := (colimit.ι F i₀).hom.toAlgebra
    (∀ x : R ⊗[S] M₀, ∃ (i : I) (h : i₀ ≤ i),
      letI : Algebra S (F.obj i) := (F.map (homOfLE h)).hom.toAlgebra
      let αᵢ : F.obj i →ₐ[S] R :=
        { (colimit.ι F i).hom with
          commutes' := fun s ↦
            congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s) (colimit.w F (homOfLE h)) }
      ∃ t : F.obj i ⊗[S] M₀, αᵢ.toLinearMap.rTensor M₀ t = x) ∧
    (∀ (i : I) (h : i₀ ≤ i),
      letI : Algebra S (F.obj i) := (F.map (homOfLE h)).hom.toAlgebra
      let αᵢ : F.obj i →ₐ[S] R :=
        { (colimit.ι F i).hom with
          commutes' := fun s ↦
            congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s) (colimit.w F (homOfLE h)) }
      ∀ t : F.obj i ⊗[S] M₀, αᵢ.toLinearMap.rTensor M₀ t = 0 →
        ∃ (i' : I) (h' : i ≤ i'),
          letI : Algebra S (F.obj i') := (F.map (homOfLE (h.trans h'))).hom.toAlgebra
          let αᵢ'ᵢ : F.obj i →ₐ[S] F.obj i' :=
            { (F.map (homOfLE h')).hom with
              commutes' := fun s ↦
                congrArg (fun f : F.obj i₀ ⟶ F.obj i' ↦ f s)
                  (F.map_comp (homOfLE h) (homOfLE h')).symm }
          αᵢ'ᵢ.toLinearMap.rTensor M₀ t = 0) := by
  sorry

end TensorProduct
