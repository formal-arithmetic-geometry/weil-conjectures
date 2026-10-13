/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Category.Ring.Colimits
import Sheaf.Paper.DirectedColimitBaseChangeElementwise

/-! # Colimits of coherent iterated tensor diagrams

Source: Stacks Project, Algebra, Tags 00D6, 00D7 and 00DD.
(blueprint: lem-weil-pbc-directed-tensor-cocones-colimit-n3)
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits

universe v w x y

namespace RingHom

/-- Canonical cocones of coherent tensor diagrams over a directed upper tail are colimits.

Source: Stacks Project, Algebra, Tags 00D6, 00D7 and 00DD.
(blueprint: lem-weil-pbc-directed-tensor-cocones-colimit-n3)

Proof: the tail above i is nonempty and cofinal. Representatives and eventual
equality in colimit F, after tensoring with B₀ or C₀, identify the colimits of
the canonical B and C diagrams with B = colimit F tensor B₀ and C = colimit F
tensor C₀. For a representative whose index is not above i, pass to a common
upper bound with i. The transition equations hDt and hEt identify the given
diagrams with these tensor diagrams (and, for D, their further tensors with Q).
For E, compatible ring maps out of its stages therefore extend uniquely to C.
Addition, multiplication and the unit are preserved by passing representatives
to a common upper stage; eventual equality makes the extension well-defined.
For D, restrict a compatible family to Bⱼ and Q. The Q maps coincide since
the tail is directed and all transition maps fix Q. The Bⱼ maps descend to a
ring map out of B by representatives and eventual equality. Their agreement
with the fixed Q map on P holds already at each stage, by hμs. The tensor
universal property extends this pair uniquely to B tensor_P Q. Conversely,
any map out of B tensor_P Q restricts to the compatible family. Thus the two
canonical cocones have the universal properties of colimits. The equations
hcD and hcE and the equivalences dLim and cLim transport these properties to the
given cocones. This argument includes zero rings and the singleton tail;
no finite-presentation hypothesis and no comparison map is needed.
-/
theorem isColimit_directed_tensor_cocones
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{v}) [HasColimit F]
    (i₀ : I) (B₀ : Type w) (C₀ : Type x) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (P Q : Type y) [CommRing P] [CommRing Q] [Algebra P Q]
    (aP : letI := (colimit.ι F i₀).hom.toAlgebra
      Algebra P (↥(colimit F) ⊗[F.obj i₀] B₀))
    (i : I) (hi : i₀ ≤ i)
    (aPs : ∀ j : {j : I // i ≤ j},
      letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
      Algebra P (↥(F.obj j.val) ⊗[F.obj i₀] B₀))
    (D E : {j : I // i ≤ j} ⥤ CommRingCat.{max v w x y})
    (d : ∀ j : {j : I // i ≤ j},
      letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
      letI := aPs j
      ↥(D.obj j) ≃+* (↥(F.obj j.val) ⊗[F.obj i₀] B₀) ⊗[P] Q)
    (c : ∀ j : {j : I // i ≤ j},
      letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
      ↥(E.obj j) ≃+* (↥(F.obj j.val) ⊗[F.obj i₀] C₀))
    (cD : Cocone D) (cE : Cocone E)
    (dLim : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := aP
      ↥cD.pt ≃+* (↥(colimit F) ⊗[F.obj i₀] B₀) ⊗[P] Q)
    (cLim : letI := (colimit.ι F i₀).hom.toAlgebra
      ↥cE.pt ≃+* (↥(colimit F) ⊗[F.obj i₀] C₀))
    (μs : ∀ j : {j : I // i ≤ j},
      letI := (colimit.ι F i₀).hom.toAlgebra
      letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
      letI := aPs j
      letI := aP
      (↥(F.obj j.val) ⊗[F.obj i₀] B₀) →ₐ[P]
        (↥(colimit F) ⊗[F.obj i₀] B₀))
    (hμs : ∀ j : {j : I // i ≤ j},
      letI := (colimit.ι F i₀).hom.toAlgebra
      letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
      let αj : F.obj j.val →ₐ[F.obj i₀] ↥(colimit F) :=
        { (colimit.ι F j.val).hom with
          commutes' := fun s ↦
            congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s)
              (colimit.w F (homOfLE (hi.trans j.property))) }
      (μs j).toRingHom =
        (Algebra.TensorProduct.map αj (AlgHom.id (F.obj i₀) B₀)).toRingHom)
    (hcD : ∀ j : {j : I // i ≤ j},
      letI := (colimit.ι F i₀).hom.toAlgebra
      letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
      letI := aPs j
      letI := aP
      dLim.toRingHom.comp (cD.ι.app j).hom =
        (Algebra.TensorProduct.map (μs j) (AlgHom.id P Q)).toRingHom.comp
          (d j).toRingHom)
    (hDt : ∀ {j k : {j : I // i ≤ j}} (r : j ⟶ k),
      letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
      letI := (F.map (homOfLE (hi.trans k.property))).hom.toAlgebra
      letI := aPs j
      letI := aPs k
      ∃ β : (↥(F.obj j.val) ⊗[F.obj i₀] B₀) →ₐ[P]
          (↥(F.obj k.val) ⊗[F.obj i₀] B₀),
        (let αjk : F.obj j.val →ₐ[F.obj i₀] F.obj k.val :=
          { (F.map (homOfLE (leOfHom r))).hom with
            commutes' := fun s ↦
              congrArg (fun f : F.obj i₀ ⟶ F.obj k.val ↦ f s)
                (F.map_comp (homOfLE (hi.trans j.property))
                  (homOfLE (leOfHom r))).symm };
          β.toRingHom =
            (Algebra.TensorProduct.map αjk
              (AlgHom.id (F.obj i₀) B₀)).toRingHom) ∧
        (d k).toRingHom.comp (D.map r).hom =
          (Algebra.TensorProduct.map β (AlgHom.id P Q)).toRingHom.comp
            (d j).toRingHom)
    (hcE : ∀ j : {j : I // i ≤ j},
      letI := (colimit.ι F i₀).hom.toAlgebra
      letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
      let αj : F.obj j.val →ₐ[F.obj i₀] ↥(colimit F) :=
        { (colimit.ι F j.val).hom with
          commutes' := fun s ↦
            congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s)
              (colimit.w F (homOfLE (hi.trans j.property))) }
      cLim.toRingHom.comp (cE.ι.app j).hom =
        (Algebra.TensorProduct.map αj (AlgHom.id (F.obj i₀) C₀)).toRingHom.comp
          (c j).toRingHom)
    (hEt : ∀ {j k : {j : I // i ≤ j}} (r : j ⟶ k),
      letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
      letI := (F.map (homOfLE (hi.trans k.property))).hom.toAlgebra
      let αjk : F.obj j.val →ₐ[F.obj i₀] F.obj k.val :=
          { (F.map (homOfLE (leOfHom r))).hom with
            commutes' := fun s ↦
              congrArg (fun f : F.obj i₀ ⟶ F.obj k.val ↦ f s)
                (F.map_comp (homOfLE (hi.trans j.property))
                  (homOfLE (leOfHom r))).symm }
      (c k).toRingHom.comp (E.map r).hom =
        (Algebra.TensorProduct.map αjk (AlgHom.id (F.obj i₀) C₀)).toRingHom.comp
          (c j).toRingHom)
    : Nonempty (IsColimit cD) ∧ Nonempty (IsColimit cE) := by sorry

end RingHom
