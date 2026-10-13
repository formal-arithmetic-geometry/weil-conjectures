/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.Algebra.Category.Ring.Colimits

/-! # A tensor model at one finite stage

Source: Stacks Project, Algebra, Tag 02JO (3), final paragraph; Tag 05N9.
(blueprint: lem-pc-tensor-model-algebra-stage)
-/

@[expose] public section

universe v w x
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- A compatible finitely presented tensor model gives one pushout square at a finite stage.

Source: Stacks Project, Algebra, Tag 02JO (3), final paragraph; Tags 00QO and 05N9.
(blueprint: lem-pc-tensor-model-algebra-stage)

Proof:
1. Restrict the diagram to the directed upper tail above i. Tensoring with A and B
   gives colimits X and Y: each element has a stage representative and any equality
   holds at a later stage. Finite presentation of P over the integers descends its
   map to X to a map P to A_r at a stage r.
2. For j above r give B_j its P-structure through A_r to A_j to B_j. The given
   map Q to Y is P-linear: on P the left and right inclusions into X tensor_P Q
   agree, and he identifies the left inclusion with the extension of f. Finite
   presentation of Q over P factors this map through some B_s. The tensor lift
   A_s tensor_P Q to B_s then base changes to the given e.
3. B is finitely presented over A because B is finitely presented over F(i) and A
   is of finite type there. Thus B_s is finitely presented over A_s. The model
   A_s tensor_P Q is also finitely presented over A_s. The diagram A_j on the
   upper tail of s has colimit X. Apply descent of maps between finitely presented
   algebras to the inverse of e, using the tensor associativity identifications.
   Both inverse identities hold after passing to X, so descent of equality makes
   them hold at some common later k. The comparison at k is an isomorphism.
4. Transport the canonical tensor pushout along this isomorphism. Its restrictions
   are precisely f_k and the transition of the factor Q to B_s. Naturality gives
   the asserted equality after passage to Y. All constructions work for zero
   rings and empty presentations, without flatness or injective transitions.
-/
theorem exists_tensor_model_algebra_stage
    {I : Type v} [Preorder I] [IsDirectedOrder I]
    (F : I ⥤ CommRingCat.{v}) (c : Cocone F) (hc : IsColimit c)
    {i : I} {A B : Type w} [CommRing A] [CommRing B]
    [Algebra (F.obj i : Type v) A] [Algebra (F.obj i : Type v) B]
    [Algebra.FinitePresentation (F.obj i : Type v) A]
    [Algebra.FinitePresentation (F.obj i : Type v) B] (f : A →ₐ[F.obj i] B)
    (P Q : Type x) [CommRing P] [CommRing Q] [Algebra P Q]
    [Algebra.FinitePresentation ℤ P] [Algebra.FinitePresentation P Q]
    (aP : letI : Algebra (F.obj i : Type v) (c.pt : Type v) := (c.ι.app i).hom.toAlgebra
      Algebra P ((c.pt : Type v) ⊗[F.obj i] A))
    (e : letI : Algebra (F.obj i : Type v) (c.pt : Type v) := (c.ι.app i).hom.toAlgebra
      letI := aP
      ((c.pt : Type v) ⊗[F.obj i] A) ⊗[P] Q ≃+* (c.pt : Type v) ⊗[F.obj i] B)
    (he : letI : Algebra (F.obj i : Type v) (c.pt : Type v) := (c.ι.app i).hom.toAlgebra
      letI := aP
      e.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom =
        (Algebra.TensorProduct.map (Algebra.ofId (c.pt : Type v) (c.pt : Type v))
          f).toRingHom) :
    ∃ (k : I) (hik : i ≤ k),
      letI := (F.map (homOfLE hik)).hom.toAlgebra
      ∃ qk : Q →+* (F.obj k : Type v) ⊗[F.obj i] B,
        (letI : Algebra (F.obj i : Type v) (c.pt : Type v) :=
          (c.ι.app i).hom.toAlgebra
         let t : F.obj k →ₐ[F.obj i] c.pt :=
           { (c.ι.app k).hom with
             commutes' := fun s ↦ ConcreteCategory.congr_hom (c.w (homOfLE hik)) s }
         (Algebra.TensorProduct.map t (AlgHom.id (F.obj i) B)).toRingHom.comp qk =
           e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) ∧
        (let D := (F.obj k : Type v) ⊗[F.obj i] A
         let E := (F.obj k : Type v) ⊗[F.obj i] B
         let d : D →+* E :=
           (Algebra.TensorProduct.map (AlgHom.id (F.obj k) (F.obj k)) f).toRingHom
         letI : Algebra D E := d.toAlgebra
         letI : Algebra Q E := qk.toAlgebra
         ∃ aPk : Algebra P D,
           letI := aPk
           letI : Algebra P E := (d.comp (algebraMap P D)).toAlgebra
           letI : IsScalarTower P D E := .of_algebraMap_eq fun _ ↦ rfl
           ∃ hPQ : IsScalarTower P Q E,
             letI := hPQ
             Algebra.IsPushout P D Q E) := by sorry

end AlgebraicGeometry
