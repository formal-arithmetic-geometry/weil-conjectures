/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Category.Ring.Colimits

/-! # Canonical P-linear maps from tensor stages to the limiting tensor ring

For a directed system of rings `F` with colimit, the canonical maps
`F(j) ⊗[F(i₀)] B₀ → colim F ⊗[F(i₀)] B₀` are `P`-algebra maps for `j ≥ i`, provided the map from
stage `i` and the transitions from stage `i` are.

## References

* [Stacks, Tag 02JO] (3)
* [Stacks, Tag 00DD]
-/
@[expose] public section
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits
universe v w y
namespace RingHom
/-- If the canonical map `μB` from stage `i` and the transitions `βs j` from stage `i` to stages
`j ≥ i` are `P`-algebra maps, then so are the canonical maps
`F(j) ⊗[F(i₀)] B₀ → colim F ⊗[F(i₀)] B₀` for all `j ≥ i`. -/
theorem exists_comparison_tensor_canonical_maps
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{v}) [HasColimit F]
    (i₀ : I) (B₀ : Type w) [CommRing B₀] [Algebra (F.obj i₀) B₀]
    (P : Type y) [CommRing P]
    (aP : letI := (colimit.ι F i₀).hom.toAlgebra
      Algebra P (↥(colimit F) ⊗[F.obj i₀] B₀))
    (i : I) (hi : i₀ ≤ i)
    (aPi : letI := (F.map (homOfLE hi)).hom.toAlgebra
      Algebra P (↥(F.obj i) ⊗[F.obj i₀] B₀))
    (μB : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := (F.map (homOfLE hi)).hom.toAlgebra
      letI := aPi
      letI := aP
      (↥(F.obj i) ⊗[F.obj i₀] B₀) →ₐ[P] (↥(colimit F) ⊗[F.obj i₀] B₀))
    (hμB : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := (F.map (homOfLE hi)).hom.toAlgebra
      let αi : F.obj i →ₐ[F.obj i₀] ↥(colimit F) :=
        { (colimit.ι F i).hom with
          commutes' := fun s ↦
            congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s) (colimit.w F (homOfLE hi)) }
      μB.toRingHom =
        (Algebra.TensorProduct.map αi (AlgHom.id (F.obj i₀) B₀)).toRingHom)
    (aPs : ∀ j : {j : I // i ≤ j},
          letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
          Algebra P (↥(F.obj j.val) ⊗[F.obj i₀] B₀))
    (βs : ∀ j : {j : I // i ≤ j},
                    letI := (F.map (homOfLE hi)).hom.toAlgebra
                    letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                    letI := aPi
                    letI := aPs j
                    (↥(F.obj i) ⊗[F.obj i₀] B₀) →ₐ[P]
                      (↥(F.obj j.val) ⊗[F.obj i₀] B₀))
    (hβs : (∀ j : {j : I // i ≤ j},
                    letI := (F.map (homOfLE hi)).hom.toAlgebra
                    letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                    let αij : F.obj i →ₐ[F.obj i₀] F.obj j.val :=
                      { (F.map (homOfLE j.property)).hom with
                        commutes' := fun s ↦
                          congrArg (fun f : F.obj i₀ ⟶ F.obj j.val ↦ f s)
                            (F.map_comp (homOfLE hi) (homOfLE j.property)).symm }
                    (βs j).toRingHom =
                      (Algebra.TensorProduct.map αij (AlgHom.id (F.obj i₀) B₀)).toRingHom)) :
      let J := {j : I // i ≤ j}
                  ∃ (μs : ∀ j : J,
                    letI := (colimit.ι F i₀).hom.toAlgebra
                    letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                    letI := aPs j
                    letI := aP
                    (↥(F.obj j.val) ⊗[F.obj i₀] B₀) →ₐ[P]
                      (↥(colimit F) ⊗[F.obj i₀] B₀)),
                  (∀ j : J,
                    letI := (colimit.ι F i₀).hom.toAlgebra
                    letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                    let αj : F.obj j.val →ₐ[F.obj i₀] ↥(colimit F) :=
                      { (colimit.ι F j.val).hom with
                        commutes' := fun s ↦
                          congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s)
                            (colimit.w F (homOfLE (hi.trans j.property))) }
                    (μs j).toRingHom =
                      (Algebra.TensorProduct.map αj (AlgHom.id (F.obj i₀) B₀)).toRingHom) := by
  classical
  let J := {j : I // i ≤ j}
  let := (colimit.ι F i₀).hom.toAlgebra
  let := (F.map (homOfLE hi)).hom.toAlgebra
  let := aPi
  let := aP
  let αi : F.obj i →ₐ[F.obj i₀] ↥(colimit F) :=
    { (colimit.ι F i).hom with
      commutes' := fun s ↦ congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s)
        (colimit.w F (homOfLE hi)) }
  have μcomm (j : J) :
      letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
      letI := aPs j
      let αj : F.obj j.val →ₐ[F.obj i₀] ↥(colimit F) :=
        { (colimit.ι F j.val).hom with
          commutes' := fun s ↦ congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s)
            (colimit.w F (homOfLE (hi.trans j.property))) }
      ∀ z : P, Algebra.TensorProduct.map αj (AlgHom.id (F.obj i₀) B₀)
        (algebraMap P (↥(F.obj j.val) ⊗[F.obj i₀] B₀) z) =
        algebraMap P (↥(colimit F) ⊗[F.obj i₀] B₀) z := by
    let := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
    let := aPs j
    let αj : F.obj j.val →ₐ[F.obj i₀] ↥(colimit F) :=
      { (colimit.ι F j.val).hom with
        commutes' := fun s ↦ congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s)
          (colimit.w F (homOfLE (hi.trans j.property))) }
    let αij : F.obj i →ₐ[F.obj i₀] F.obj j.val :=
      { (F.map (homOfLE j.property)).hom with
        commutes' := fun s ↦ congrArg (fun f : F.obj i₀ ⟶ F.obj j.val ↦ f s)
          (F.map_comp (homOfLE hi) (homOfLE j.property)).symm }
    have hcomp : αj.comp αij = αi := by
      ext z
      exact congrArg (fun f : F.obj i ⟶ colimit F ↦ f z)
        (colimit.w F (homOfLE j.property))
    have hmap (z : ↥(F.obj i) ⊗[F.obj i₀] B₀) :
        Algebra.TensorProduct.map αj (AlgHom.id (F.obj i₀) B₀) (βs j z) = μB z := by
      have hb := DFunLike.congr_fun (hβs j) z
      have hm := DFunLike.congr_fun hμB z
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hb hm
      rw [hb, hm, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, hcomp]
      rfl
    dsimp only
    intro z
    change Algebra.TensorProduct.map αj (AlgHom.id (F.obj i₀) B₀)
      (algebraMap P (↥(F.obj j.val) ⊗[F.obj i₀] B₀) z) = _
    rw [← (βs j).commutes z, hmap, μB.commutes]
  refine ⟨fun j ↦ ?_, ?_⟩
  · letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
    letI := aPs j
    let αj : F.obj j.val →ₐ[F.obj i₀] ↥(colimit F) :=
      { (colimit.ι F j.val).hom with
        commutes' := fun s ↦ congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s)
          (colimit.w F (homOfLE (hi.trans j.property))) }
    exact { (Algebra.TensorProduct.map αj (AlgHom.id (F.obj i₀) B₀)).toRingHom with
      commutes' := μcomm j }
  · intro j
    rfl

end RingHom
