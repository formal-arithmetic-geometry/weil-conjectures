/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.Algebra.Category.Ring.Colimits

/-! # Descending the algebra part of a tensor model

Source: Stacks Project, Algebra, Tag 02JO (3), final paragraph; Tag 05N9.
(blueprint: lem-pc-tensor-model-algebra-descent)
-/

@[expose] public section

universe v w x
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The algebra part of a finitely presented tensor model descends to a compatible
family of pushout squares on a tail. This statement involves no modules.

Source: Stacks Project, Algebra, Tag 02JO (3), final paragraph; Tags 00QO and 05N9.
(blueprint: lem-pc-tensor-model-algebra-descent)

Proof:
1. On the cofinal tail above i, the tensors with A and B have colimits X and Y.
   Tensor products commute with filtered colimits, by representatives and eventual
   equality. Factor P to X through one stage using finite presentation over Z.
2. The map Q to Y induced by e is P-linear, by he. Factor it through a B stage
   using finite presentation of Q over P. The tensor universal property produces
   a comparison from the model algebra to the prescribed algebra there.
3. B is finitely presented over A: finite presentation over the common base and
   finite type of A imply this. Both sides of the comparison are therefore
   finitely presented over the A stage. Descend the inverse of e and both inverse
   identities by Tag 05N9, then take a common upper bound.
4. Extend the resulting algebra isomorphism and the two structure maps to every
   later stage by base change. Its tensor universal property is precisely the
   pushout square asserted here. The maps from Q are compatible with transition
   maps and with the given map to Y by construction. Zero rings and empty
   presentations require no separate nonvanishing or flatness hypothesis.
-/
theorem exists_tensor_model_algebra_tail
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
      ∃ q : ∀ (j : I) (hkj : k ≤ j),
        letI := (F.map (homOfLE (hik.trans hkj))).hom.toAlgebra
        Q →+* (F.obj j : Type v) ⊗[F.obj i] B,
      (∀ (j : I) (hkj : k ≤ j),
        letI := (F.map (homOfLE (hik.trans hkj))).hom.toAlgebra
        letI : Algebra (F.obj i : Type v) (c.pt : Type v) :=
          (c.ι.app i).hom.toAlgebra
        let t : F.obj j →ₐ[F.obj i] c.pt :=
          { (c.ι.app j).hom with
            commutes' := fun s ↦ ConcreteCategory.congr_hom
              (c.w (homOfLE (hik.trans hkj))) s }
        (Algebra.TensorProduct.map t (AlgHom.id (F.obj i) B)).toRingHom.comp
          (q j hkj) = e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) ∧
      (∀ (j l : I) (hkj : k ≤ j) (hkl : k ≤ l) (hjl : j ≤ l),
        letI := (F.map (homOfLE (hik.trans hkj))).hom.toAlgebra
        letI := (F.map (homOfLE (hik.trans hkl))).hom.toAlgebra
        let t : F.obj j →ₐ[F.obj i] F.obj l :=
          { (F.map (homOfLE hjl)).hom with
            commutes' := fun s ↦ (ConcreteCategory.congr_hom
              (F.map_comp (homOfLE (hik.trans hkj)) (homOfLE hjl)) s).symm }
        (Algebra.TensorProduct.map t (AlgHom.id (F.obj i) B)).toRingHom.comp
          (q j hkj) = q l hkl) ∧
      (∀ (j : I) (hkj : k ≤ j),
        letI := (F.map (homOfLE (hik.trans hkj))).hom.toAlgebra
        let D := (F.obj j : Type v) ⊗[F.obj i] A
        let E := (F.obj j : Type v) ⊗[F.obj i] B
        let d : D →+* E :=
          (Algebra.TensorProduct.map (AlgHom.id (F.obj j) (F.obj j)) f).toRingHom
        letI : Algebra D E := d.toAlgebra
        letI : Algebra Q E := (q j hkj).toAlgebra
        ∃ aPj : Algebra P D,
          letI := aPj
          letI : Algebra P E := (d.comp (algebraMap P D)).toAlgebra
          letI : IsScalarTower P D E := .of_algebraMap_eq fun _ ↦ rfl
          ∃ hPQ : IsScalarTower P Q E,
            letI := hPQ
            Algebra.IsPushout P D Q E) := by sorry

end AlgebraicGeometry
