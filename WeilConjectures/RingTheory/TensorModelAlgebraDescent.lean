/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.Algebra.Category.Ring.Colimits
import WeilConjectures.RingTheory.TensorModelAlgebraStage
import WeilConjectures.RingTheory.TensorModelPushoutBaseChange

/-! # Descending the algebra part of a tensor model

A tensor model `colim F ⊗ B ≅ (colim F ⊗ A) ⊗[P] Q` of finitely presented algebras over a
directed colimit of rings descends to a compatible family of pushout squares at the finite
stages of a tail of the system.

## Implementation details

On the tail above `i`, tensor products with `A` and `B` commute with the filtered colimit.
The map `P → colim F ⊗ A` factors through a stage by finite presentation of `P` over `ℤ`, and
the `P`-linear map `Q → colim F ⊗ B` through a stage by finite presentation of `Q` over `P`.
Both sides of the resulting comparison are finitely presented over the stage, so the inverse
of `e` and both inverse identities descend to a common stage by Tag 05N9. Base change then
extends the algebra isomorphism and structure maps to all later stages; no flatness or
nonvanishing hypothesis is needed.

## References

* [Stacks, Tag 02JO]
* [Stacks, Tag 00QO]
* [Stacks, Tag 05N9]
-/

@[expose] public section

universe v w x
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

private theorem tensor_map_comp_left
    {R S T U B : Type*} [CommRing R] [CommRing S] [CommRing T]
    [CommRing U] [CommRing B] [Algebra R S] [Algebra R T]
    [Algebra R U] [Algebra R B] (u : S →ₐ[R] T) (v : T →ₐ[R] U) :
    (Algebra.TensorProduct.map v (AlgHom.id R B)).toRingHom.comp
      (Algebra.TensorProduct.map u (AlgHom.id R B)).toRingHom =
      (Algebra.TensorProduct.map (v.comp u) (AlgHom.id R B)).toRingHom := by
  apply RingHom.ext
  intro x
  exact DFunLike.congr_fun
    (Algebra.TensorProduct.map_comp v u (AlgHom.id R B) (AlgHom.id R B)).symm x

/-- Let `f : A → B` be a map of finitely presented `F i`-algebras, `P → Q` a finitely presented
map with `P` finitely presented over `ℤ`, and suppose `colim F ⊗ B ≅ (colim F ⊗ A) ⊗[P] Q`
compatibly with `f`. Then on a tail `j ≥ k` this tensor model descends to a
compatible family of pushout squares: there are maps `Q → F j ⊗ B` compatible with the
transition maps and with `e`, and a `P`-structure on `F k ⊗ A` mapping to the given one on the
colimit, whose base changes to later stages are the induced ones. -/
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
      (letI := (F.map (homOfLE hik)).hom.toAlgebra
       ∃ aPk : Algebra P ((F.obj k : Type v) ⊗[F.obj i] A),
        (letI : Algebra (F.obj i : Type v) (c.pt : Type v) := (c.ι.app i).hom.toAlgebra
         let t : F.obj k →ₐ[F.obj i] c.pt :=
           { (c.ι.app k).hom with
             commutes' := fun s ↦ ConcreteCategory.congr_hom (c.w (homOfLE hik)) s }
         letI := aPk
         letI := aP
         (Algebra.TensorProduct.map t (AlgHom.id (F.obj i) A)).toRingHom.comp
             (algebraMap P ((F.obj k : Type v) ⊗[F.obj i] A)) =
           algebraMap P ((c.pt : Type v) ⊗[F.obj i] A)) ∧
        ∀ (j : I) (hkj : k ≤ j),
          letI := (F.map (homOfLE (hik.trans hkj))).hom.toAlgebra
          let t : F.obj k →ₐ[F.obj i] F.obj j :=
            { (F.map (homOfLE hkj)).hom with
              commutes' := fun s ↦ (ConcreteCategory.congr_hom
                (F.map_comp (homOfLE hik) (homOfLE hkj)) s).symm }
          let D := (F.obj j : Type v) ⊗[F.obj i] A
          let E := (F.obj j : Type v) ⊗[F.obj i] B
          let d : D →+* E :=
            (Algebra.TensorProduct.map (AlgHom.id (F.obj j) (F.obj j)) f).toRingHom
          letI : Algebra D E := d.toAlgebra
          letI : Algebra Q E := (q j hkj).toAlgebra
          letI : Algebra P D :=
            ((Algebra.TensorProduct.map t (AlgHom.id (F.obj i) A)).toRingHom.comp
              (@algebraMap P ((F.obj k : Type v) ⊗[F.obj i] A) _ _ aPk)).toAlgebra
          letI : Algebra P E := (d.comp (algebraMap P D)).toAlgebra
          letI : IsScalarTower P D E := .of_algebraMap_eq fun _ ↦ rfl
          ∃ hPQ : IsScalarTower P Q E,
            letI := hPQ
            Algebra.IsPushout P D Q E) := by
  obtain ⟨k, hik, qk, hlimit, aPk, hcompat, hpush⟩ :=
    exists_tensor_model_algebra_stage F c hc f P Q aP e he
  let := (F.map (homOfLE hik)).hom.toAlgebra
  let : Algebra (F.obj i : Type v) (c.pt : Type v) := (c.ι.app i).hom.toAlgebra
  let t (j : I) (hkj : k ≤ j) :
      let := (F.map (homOfLE (hik.trans hkj))).hom.toAlgebra
      F.obj k →ₐ[F.obj i] F.obj j := by
    let := (F.map (homOfLE (hik.trans hkj))).hom.toAlgebra
    exact { (F.map (homOfLE hkj)).hom with
      commutes' := fun s ↦ (ConcreteCategory.congr_hom
        (F.map_comp (homOfLE hik) (homOfLE hkj)) s).symm }
  let q (j : I) (hkj : k ≤ j) :
      let := (F.map (homOfLE (hik.trans hkj))).hom.toAlgebra
      Q →+* (F.obj j : Type v) ⊗[F.obj i] B := by
    let := (F.map (homOfLE (hik.trans hkj))).hom.toAlgebra
    exact (Algebra.TensorProduct.map (t j hkj)
      (AlgHom.id (F.obj i) B)).toRingHom.comp qk
  refine ⟨k, hik, q, ?_, ?_, aPk, hcompat, ?_⟩
  · intro j hkj
    let := (F.map (homOfLE (hik.trans hkj))).hom.toAlgebra
    let cj : F.obj j →ₐ[F.obj i] c.pt :=
      { (c.ι.app j).hom with
        commutes' := fun s ↦ ConcreteCategory.congr_hom
          (c.w (homOfLE (hik.trans hkj))) s }
    let ck : F.obj k →ₐ[F.obj i] c.pt :=
      { (c.ι.app k).hom with
        commutes' := fun s ↦ ConcreteCategory.congr_hom (c.w (homOfLE hik)) s }
    have ht : cj.comp (t j hkj) = ck := by
      ext s
      exact ConcreteCategory.congr_hom (c.w (homOfLE hkj)) s
    change (Algebra.TensorProduct.map cj (AlgHom.id (F.obj i) B)).toRingHom.comp
      ((Algebra.TensorProduct.map (t j hkj) (AlgHom.id (F.obj i) B)).toRingHom.comp
        qk) = _
    rw [← RingHom.comp_assoc, tensor_map_comp_left, ht]
    exact hlimit
  · intro j l hkj hkl hjl
    let := (F.map (homOfLE (hik.trans hkj))).hom.toAlgebra
    let := (F.map (homOfLE (hik.trans hkl))).hom.toAlgebra
    let tjl : F.obj j →ₐ[F.obj i] F.obj l :=
      { (F.map (homOfLE hjl)).hom with
        commutes' := fun s ↦ (ConcreteCategory.congr_hom
          (F.map_comp (homOfLE (hik.trans hkj)) (homOfLE hjl)) s).symm }
    have ht : tjl.comp (t j hkj) = t l hkl := by
      ext s
      exact (ConcreteCategory.congr_hom
        (F.map_comp (homOfLE hkj) (homOfLE hjl)) s).symm
    change (Algebra.TensorProduct.map tjl (AlgHom.id (F.obj i) B)).toRingHom.comp
      ((Algebra.TensorProduct.map (t j hkj) (AlgHom.id (F.obj i) B)).toRingHom.comp
        qk) = _
    rw [← RingHom.comp_assoc, tensor_map_comp_left, ht]
  · intro j hkj
    let := (F.map (homOfLE (hik.trans hkj))).hom.toAlgebra
    exact tensor_model_pushout_base_change (F.obj i) (F.obj k) (F.obj j)
      A B P Q (t j hkj) f qk aPk hpush

end AlgebraicGeometry
