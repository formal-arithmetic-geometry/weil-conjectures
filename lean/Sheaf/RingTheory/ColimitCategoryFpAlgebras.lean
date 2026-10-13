/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Order.Directed
import Sheaf.Paper.DirectedColimitBaseChangeElementwise

/-! # Maps of finitely presented algebras over a directed colimit

Source: Stacks Project, Algebra, Lemma Tag 05N9, parts (2) and (3)
(blueprint: lem-weil-pbc-colimit-category-fp-algebras).
-/

@[expose] public section

universe v w z

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace RingHom

-- Source: Stacks Project, Algebra, Tag 05N8(3), as used in Tag 05N9(2).
-- Represent the finitely many polynomial generators at a common stage. The finitely
-- many kernel generators vanish at a common later stage, so the polynomial map
-- factors through the presentation. Tensor commutativity lets us use the existing
-- left-tensor elementwise colimit theorem for the right-tensor convention here.
private theorem exists_tensorStage_factorization
    {Λ : Type v} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (F : Λ ⥤ CommRingCat.{v}) [HasColimit F]
    (i : Λ) (A : Type w) (A' : Type z) [CommRing A] [CommRing A']
    [Algebra (F.obj i) A] [Algebra (F.obj i) A']
    [Algebra.FinitePresentation (F.obj i) A] :
    let S := F.obj i
    let R := colimit F
    letI : Algebra S R := (colimit.ι F i).hom.toAlgebra
    ∀ g : A →ₐ[S] (A' ⊗[S] R), ∃ (μ : Λ) (h : i ≤ μ),
      letI : Algebra S (F.obj μ) := (F.map (homOfLE h)).hom.toAlgebra
      let t : F.obj μ →ₐ[S] R :=
        { (colimit.ι F μ).hom with
          commutes' := fun s ↦
            congrArg (fun f : F.obj i ⟶ colimit F ↦ f s) (colimit.w F (homOfLE h)) }
      ∃ gμ : A →ₐ[S] (A' ⊗[S] (F.obj μ)),
        ∀ a : A, Algebra.TensorProduct.map (AlgHom.id S A') t (gμ a) = g a := by
  classical
  dsimp only
  let S := F.obj i
  let R := colimit F
  let : Algebra S R := (colimit.ι F i).hom.toAlgebra
  let J := {j : Λ // i ≤ j}
  let : Nonempty J := ⟨⟨i, le_rfl⟩⟩
  let : IsDirectedOrder J := ⟨fun j k ↦ by
    obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j.val k.val
    exact ⟨⟨l, j.property.trans hjl⟩, hjl, hkl⟩⟩
  let : ∀ j : J, Algebra S (F.obj j.val) :=
    fun j ↦ (F.map (homOfLE j.property)).hom.toAlgebra
  let B (j : J) := A' ⊗[S] (F.obj j.val)
  let t (j k : J) (h : j ≤ k) : F.obj j.val →ₐ[S] F.obj k.val :=
    { (F.map (homOfLE h)).hom with
      commutes' := fun s ↦
        congrArg (fun f : F.obj i ⟶ F.obj k.val ↦ f s)
          (F.map_comp (homOfLE j.property) (homOfLE h)).symm }
  let α (j : J) : F.obj j.val →ₐ[S] R :=
    { (colimit.ι F j.val).hom with
      commutes' := fun s ↦
        congrArg (fun f : F.obj i ⟶ colimit F ↦ f s)
          (colimit.w F (homOfLE j.property)) }
  let q (j : J) : B j →ₐ[S] (A' ⊗[S] R) :=
    Algebra.TensorProduct.map (AlgHom.id S A') (α j)
  let f (j k : J) (h : j ≤ k) : B j →ₐ[S] B k :=
    Algebra.TensorProduct.map (AlgHom.id S A') (t j k h)
  have compat (j k : J) (h : j ≤ k) (x : B j) : q k (f j k h x) = q j x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a r =>
      change a ⊗ₜ[S] ((colimit.ι F k.val).hom ((F.map (homOfLE h)).hom r)) =
        a ⊗ₜ[S] ((colimit.ι F j.val).hom r)
      exact congrArg (fun b ↦ a ⊗ₜ[S] b)
        (ConcreteCategory.congr_hom (colimit.w F (homOfLE h)) r)
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  have rep (x : A' ⊗[S] R) : ∃ (j : J) (y : B j), q j y = x := by
    obtain ⟨j, hj, y, hy⟩ :=
      (TensorProduct.directedColimitBaseChangeElementwise F i A').1
        (TensorProduct.comm S A' R x)
    let : Algebra S (F.obj j) := (F.map (homOfLE hj)).hom.toAlgebra
    refine ⟨⟨j, hj⟩, TensorProduct.comm S (F.obj j) A' y, ?_⟩
    have hc : ∀ y : F.obj j ⊗[S] A',
        q ⟨j, hj⟩ (TensorProduct.comm S (F.obj j) A' y) =
          TensorProduct.comm S R A' ((α ⟨j, hj⟩).toLinearMap.rTensor A' y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul r a => rfl
      | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    rw [hc, hy]
    exact (TensorProduct.comm S A' R).symm_apply_apply x
  have zero (j : J) (x : B j) (hx : q j x = 0) :
      ∃ (k : J) (h : j ≤ k), f j k h x = 0 := by
    let y := TensorProduct.comm S A' (F.obj j.val) x
    have hc : (α j).toLinearMap.rTensor A' y =
        TensorProduct.comm S A' R (q j x) := by
      clear hx
      dsimp only [y]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a r => rfl
      | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    obtain ⟨k, h, hk⟩ :=
      (TensorProduct.directedColimitBaseChangeElementwise F i A').2 j.val j.property y
        (by rw [hc, hx, map_zero])
    let : Algebra S (F.obj k) :=
      (F.map (homOfLE (j.property.trans h))).hom.toAlgebra
    let k' : J := ⟨k, j.property.trans h⟩
    have hc' : (t j k' h).toLinearMap.rTensor A' y =
        TensorProduct.comm S A' (F.obj k) (f j k' h x) := by
      clear hx hc hk
      dsimp only [y]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a r => rfl
      | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    refine ⟨k', h, ?_⟩
    apply (TensorProduct.comm S A' (F.obj k)).injective
    rw [map_zero, ← hc']
    exact hk
  intro g
  obtain ⟨n, π, hπ, tπ, htπ⟩ := Algebra.FinitePresentation.out (R := S) (A := A)
  choose j y hy using fun a : Fin n ↦ rep (g (π (MvPolynomial.X a)))
  obtain ⟨ν, hν⟩ := (Finset.univ.image j).exists_le
  let p : MvPolynomial (Fin n) S →ₐ[S] B ν :=
    MvPolynomial.aeval (fun a ↦ f (j a) ν (hν (j a) (Finset.mem_image.mpr
      ⟨a, Finset.mem_univ a, rfl⟩)) (y a))
  have hp : (q ν).comp p = g.comp π := by
    apply MvPolynomial.algHom_ext
    intro a
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, p]
    exact (compat _ _ _ _).trans (hy a)
  have rel (r : tπ) : ∃ (k : J) (h : ν ≤ k), f ν k h (p r) = 0 := by
    apply zero
    have hr : π r = 0 := htπ.le (Ideal.subset_span r.property)
    have he := DFunLike.congr_fun hp (r : MvPolynomial (Fin n) S)
    change q ν (p (r : MvPolynomial (Fin n) S)) =
      g (π (r : MvPolynomial (Fin n) S)) at he
    rw [hr, map_zero] at he
    exact he
  choose k hk ek using rel
  obtain ⟨κ, hκ⟩ := (Finset.univ.image k).exists_le
  obtain ⟨ω, hνω, hκω⟩ := exists_ge_ge ν κ
  let pω := (f ν ω hνω).comp p
  have hker : RingHom.ker π.toRingHom ≤ RingHom.ker pω.toRingHom := by
    rw [← htπ, Ideal.span_le]
    intro r hr
    let hρω : k ⟨r, hr⟩ ≤ ω :=
      (hκ _ (Finset.mem_image.mpr ⟨⟨r, hr⟩, Finset.mem_univ _, rfl⟩)).trans hκω
    have hf : (f (k ⟨r, hr⟩) ω hρω).comp (f ν (k ⟨r, hr⟩) (hk ⟨r, hr⟩)) =
        f ν ω hνω := by
      apply AlgHom.ext
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        change a ⊗ₜ[S] ((F.map (homOfLE hρω)).hom
          ((F.map (homOfLE (hk ⟨r, hr⟩))).hom b)) =
          a ⊗ₜ[S] ((F.map (homOfLE hνω)).hom b)
        exact congrArg (fun c ↦ a ⊗ₜ[S] c)
          (ConcreteCategory.congr_hom
            (F.map_comp (homOfLE (hk ⟨r, hr⟩)) (homOfLE hρω)) b).symm
      | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    change f ν ω hνω (p r) = 0
    rw [← hf, AlgHom.comp_apply, ek ⟨r, hr⟩, map_zero]
  refine ⟨ω.val, ω.property, π.liftOfSurjective hπ pω hker, ?_⟩
  intro a
  obtain ⟨r, rfl⟩ := hπ a
  rw [AlgHom.liftOfSurjective_apply]
  exact (compat ν ω hνω (p r)).trans (DFunLike.congr_fun hp r)


/-- Source: Stacks Project, Algebra, Lemma Tag 05N9, parts (2) and (3)
(blueprint: lem-weil-pbc-colimit-category-fp-algebras).

Maps between finitely presented algebras descend to a stage, and equality of two maps
holds at a stage if it holds over the colimit. The first clause uses the commuting square
with the canonical maps to the colimit tensors to express equality after base change.

Proof:
1. Restrict to the cofinal directed upper set of `i`. By the tensor pushout universal
property (lem-weil-pbc-algebra-tensor-pushout-universal-property), the target tensor
`A' ⊗[S] R` is the colimit of `A' ⊗[S] F.obj μ`. This is also a ring colimit by
lem-weil-pbc-filtered-colimit-algebras-elementwise.
2. Restrict the given map to `A`. Finite presentation gives a factorization through
one target tensor by lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit.
The base-change adjunction (lem-weil-pbc-algebra-tensor-base-change-universal-property)
extends it to the desired stage map. Its extension agrees with the given map on `a ⊗ 1`
and on the coefficient ring, hence everywhere.
3. Choose finitely many algebra generators of `A`. Equality over `R` kills the finitely
many differences of their images. By lem-weil-pbc-directed-colimit-base-change-elementwise
each difference vanishes at a stage. A common upper bound kills them all, so the maps
agree there. If there are no generators, take `μ = i`.
-/
theorem exists_map_of_finitePresentation_colimit
    {Λ : Type v} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (F : Λ ⥤ CommRingCat.{v}) [HasColimit F]
    (i : Λ) (A : Type w) (A' : Type z) [CommRing A] [CommRing A']
    [Algebra (F.obj i) A] [Algebra (F.obj i) A']
    [Algebra.FinitePresentation (F.obj i) A]
    [Algebra.FinitePresentation (F.obj i) A'] :
    let S := F.obj i
    let R := colimit F
    letI : Algebra S R := (colimit.ι F i).hom.toAlgebra
    letI : Algebra R (A ⊗[S] R) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra R (A' ⊗[S] R) := Algebra.TensorProduct.rightAlgebra
    (∀ u : (A ⊗[S] R) →ₐ[R] (A' ⊗[S] R), ∃ (μ : Λ) (h : i ≤ μ),
      letI : Algebra S (F.obj μ) := (F.map (homOfLE h)).hom.toAlgebra
      let t : F.obj μ →ₐ[S] R :=
        { (colimit.ι F μ).hom with
          commutes' := fun s ↦
            congrArg (fun f : F.obj i ⟶ colimit F ↦ f s) (colimit.w F (homOfLE h)) }
      letI : Algebra (F.obj μ) (A ⊗[S] (F.obj μ)) := Algebra.TensorProduct.rightAlgebra
      letI : Algebra (F.obj μ) (A' ⊗[S] (F.obj μ)) := Algebra.TensorProduct.rightAlgebra
      ∃ uμ : (A ⊗[S] (F.obj μ)) →ₐ[F.obj μ] (A' ⊗[S] (F.obj μ)),
        ∀ x : A ⊗[S] (F.obj μ),
          Algebra.TensorProduct.map (AlgHom.id S A') t (uμ x) =
            u (Algebra.TensorProduct.map (AlgHom.id S A) t x)) ∧
    (∀ v w : A →ₐ[S] A',
      Algebra.TensorProduct.map v (AlgHom.id S R) =
        Algebra.TensorProduct.map w (AlgHom.id S R) →
      ∃ (μ : Λ) (h : i ≤ μ),
        letI : Algebra S (F.obj μ) := (F.map (homOfLE h)).hom.toAlgebra
        Algebra.TensorProduct.map v (AlgHom.id S (F.obj μ)) =
          Algebra.TensorProduct.map w (AlgHom.id S (F.obj μ))) := by
  -- Implement the finite-generator/finite-relation proof of Tag 05N8 directly,
  -- using elementwise tensor descent instead of constructing an algebra colimit.
  classical
  dsimp only
  let S := F.obj i
  let R := colimit F
  let : Algebra S R := (colimit.ι F i).hom.toAlgebra
  let : Algebra R (A ⊗[S] R) := Algebra.TensorProduct.rightAlgebra
  let : Algebra R (A' ⊗[S] R) := Algebra.TensorProduct.rightAlgebra
  constructor
  · intro u
    let g : A →ₐ[S] (A' ⊗[S] R) :=
      (u.restrictScalars S).comp Algebra.TensorProduct.includeLeft
    obtain ⟨μ, h, gμ, hgμ⟩ := exists_tensorStage_factorization F i A A' g
    let : Algebra S (F.obj μ) := (F.map (homOfLE h)).hom.toAlgebra
    let t : F.obj μ →ₐ[S] R :=
      { (colimit.ι F μ).hom with
        commutes' := fun s ↦
          congrArg (fun f : F.obj i ⟶ colimit F ↦ f s) (colimit.w F (homOfLE h)) }
    let : Algebra (F.obj μ) (A ⊗[S] (F.obj μ)) :=
      Algebra.TensorProduct.rightAlgebra
    let : Algebra (F.obj μ) (A' ⊗[S] (F.obj μ)) :=
      Algebra.TensorProduct.rightAlgebra
    let l : (A ⊗[S] (F.obj μ)) →ₐ[S] (A' ⊗[S] (F.obj μ)) :=
      Algebra.TensorProduct.lift gμ Algebra.TensorProduct.includeRight (fun _ _ ↦ .all _ _)
    let uμ : (A ⊗[S] (F.obj μ)) →ₐ[F.obj μ] (A' ⊗[S] (F.obj μ)) :=
      { l.toRingHom with
        commutes' := by
          intro r
          change l (1 ⊗ₜ[S] r) = 1 ⊗ₜ[S] r
          simp [l] }
    refine ⟨μ, h, uμ, ?_⟩
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a r =>
      change Algebra.TensorProduct.map (AlgHom.id S A') t
        (gμ a * (1 ⊗ₜ[S] r)) = u (a ⊗ₜ[S] t r)
      rw [map_mul, hgμ]
      simp only [Algebra.TensorProduct.map_tmul, map_one]
      change u (a ⊗ₜ[S] 1) * (1 ⊗ₜ[S] t r) = u (a ⊗ₜ[S] t r)
      have hu : u (1 ⊗ₜ[S] t r) = 1 ⊗ₜ[S] t r := u.commutes (t r)
      rw [← hu, ← map_mul]
      congr 1
      simp
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  · intro v w hvw
    have pointwise (a : A) : ∃ (μ : Λ) (h : i ≤ μ),
        letI : Algebra S (F.obj μ) := (F.map (homOfLE h)).hom.toAlgebra
        v a ⊗ₜ[S] (1 : F.obj μ) = w a ⊗ₜ[S] (1 : F.obj μ) := by
      have he : v a ⊗ₜ[S] (1 : R) = w a ⊗ₜ[S] (1 : R) := by
        have he := DFunLike.congr_fun hvw (a ⊗ₜ[S] (1 : R))
        change v a ⊗ₜ[S] (1 : R) = w a ⊗ₜ[S] (1 : R) at he
        exact he
      have hz : (1 : R) ⊗ₜ[S] (v a - w a) = 0 := by
        have he' := congrArg (TensorProduct.comm S A' R) he
        simpa only [TensorProduct.comm_tmul, TensorProduct.tmul_sub, sub_eq_zero] using he'
      obtain ⟨j, hij, _⟩ := exists_ge_ge i i
      let : Algebra S (F.obj j) := (F.map (homOfLE hij)).hom.toAlgebra
      let α : F.obj j →ₐ[S] R :=
        { (colimit.ι F j).hom with
          commutes' := fun s ↦ congrArg (fun f : F.obj i ⟶ colimit F ↦ f s)
            (colimit.w F (homOfLE hij)) }
      have hz' : α.toLinearMap.rTensor A' ((1 : F.obj j) ⊗ₜ[S] (v a - w a)) = 0 := by
        simpa only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one] using hz
      obtain ⟨μ, h, hm⟩ :=
        (TensorProduct.directedColimitBaseChangeElementwise F i A').2 j hij
          ((1 : F.obj j) ⊗ₜ[S] (v a - w a)) hz'
      refine ⟨μ, hij.trans h, ?_⟩
      let : Algebra S (F.obj μ) := (F.map (homOfLE (hij.trans h))).hom.toAlgebra
      change (F.map (homOfLE h)).hom 1 ⊗ₜ[S] (v a - w a) = 0 at hm
      rw [map_one] at hm
      have hm' := congrArg (TensorProduct.comm S (F.obj μ) A') hm
      simpa only [TensorProduct.comm_tmul, map_zero, TensorProduct.sub_tmul,
        sub_eq_zero] using hm'
    choose μ hμ eμ using pointwise
    obtain ⟨s, hs⟩ := (Algebra.FiniteType.out (R := S) (A := A))
    let : Nonempty Λ := ⟨i⟩
    obtain ⟨k, hk⟩ := (s.image μ).exists_le
    obtain ⟨ν, hiν, hkν⟩ := exists_ge_ge i k
    let : Algebra S (F.obj ν) := (F.map (homOfLE hiν)).hom.toAlgebra
    have heν (a : A) (ha : a ∈ s) :
        v a ⊗ₜ[S] (1 : F.obj ν) = w a ⊗ₜ[S] (1 : F.obj ν) := by
      have hαν : μ a ≤ ν := (hk (μ a) (Finset.mem_image.mpr ⟨a, ha, rfl⟩)).trans hkν
      let : Algebra S (F.obj (μ a)) := (F.map (homOfLE (hμ a))).hom.toAlgebra
      let t : F.obj (μ a) →ₐ[S] F.obj ν :=
        { (F.map (homOfLE hαν)).hom with
          commutes' := fun r ↦
            congrArg (fun f : F.obj i ⟶ F.obj ν ↦ f r)
              (F.map_comp (homOfLE (hμ a)) (homOfLE hαν)).symm }
      have he := congrArg (Algebra.TensorProduct.map (AlgHom.id S A') t) (eμ a)
      simpa only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one] using he
    let vν : A →ₐ[S] (A' ⊗[S] (F.obj ν)) := Algebra.TensorProduct.includeLeft.comp v
    let wν : A →ₐ[S] (A' ⊗[S] (F.obj ν)) := Algebra.TensorProduct.includeLeft.comp w
    have he : vν = wν := AlgHom.ext_of_adjoin_eq_top hs (fun a ha ↦ heν a ha)
    refine ⟨ν, hiν, ?_⟩
    apply AlgHom.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul a r =>
      have hea : v a ⊗ₜ[S] (1 : F.obj ν) = w a ⊗ₜ[S] (1 : F.obj ν) :=
        DFunLike.congr_fun he a
      have hem := congrArg (fun x : A' ⊗[S] (F.obj ν) ↦ x * (1 ⊗ₜ[S] r)) hea
      simpa only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] using hem

end RingHom
