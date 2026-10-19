/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.Algebra.Category.Ring.Colimits
public import WeilConjectures.RingTheory.TensorModelAlgebraDescent

/-! # The algebra part of a tensor model, in the form used by `Sheaf.RingTheory.FpModuleTensorModelComparison`

The former `Sheaf.RingTheory.TensorModelAlgebraDescent` was retired in favour of its upstream twin
`WeilConjectures.RingTheory.TensorModelAlgebraDescent` (2026-10-20). Upstream strengthened the statement: the
`P`-structure at every later stage is the one induced from the first stage. This module keeps the earlier,
weaker statement under a new name and derives it from the upstream theorem.
(blueprint: lem-pc-tensor-model-algebra-descent)
-/

@[expose] public section

universe v w x

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The earlier statement of `exists_tensor_model_algebra_tail`: at every later stage some `P`-structure makes the
square a pushout. It follows from the upstream statement, which fixes that structure. -/
theorem exists_tensor_model_algebra_tail_compat
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
            Algebra.IsPushout P D Q E) := by
  obtain ⟨k, hik, q, hqC, hq, aPk, -, hpush⟩ :=
    exists_tensor_model_algebra_tail F c hc f P Q aP e he
  exact ⟨k, hik, q, hqC, hq, fun j hkj ↦ ⟨_, hpush j hkj⟩⟩

end AlgebraicGeometry
