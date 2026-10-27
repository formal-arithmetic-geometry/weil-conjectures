/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import WeilConjectures.RingTheory.FilteredColimitAlgebrasTensorElementwise

/-! # Directed colimits of tensor embeddings with integral image

Source: Stacks Project, Algebra, Tag 0CBF,
lemma-integral-closure-commutes-colim-smooth, filtered-colimit argument.
(blueprint: lem-sfb-directed-tensor-integral-embedding).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Algebra.TensorProduct

private theorem tensor_elementwise
    (R N : Type u) [CommRing R] [CommRing N] [Algebra R N]
    (I : Type u) [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ CommAlgCat.{u, u} R) (c : Cocone F) (hc : IsColimit c) :
    (∀ x : (c.pt : Type u) ⊗[R] N,
      ∃ (i : I) (t : (F.obj i : Type u) ⊗[R] N),
        rTensor (R := R) N (c.ι.app i).hom t = x) ∧
    (∀ (i : I) (t : (F.obj i : Type u) ⊗[R] N),
      rTensor (R := R) N (c.ι.app i).hom t = 0 →
      ∃ (j : I) (f : i ⟶ j), rTensor (R := R) N (F.map f).hom t = 0) := by
  let : HasColimit F := HasColimit.mk ⟨c, hc⟩
  let e : colimit F ≅ c.pt := colimit.isoColimitCocone ⟨c, hc⟩
  let E : (colimit F : CommAlgCat.{u, u} R) ⊗[R] N ≃ₐ[R] (c.pt : Type u) ⊗[R] N :=
    congr (CommAlgCat.algEquivOfIso e) (AlgEquiv.refl : N ≃ₐ[R] N)
  have hE (i : I) :
      E.toAlgHom.comp (rTensor (R := R) N (colimit.ι F i).hom) =
        rTensor (R := R) N (c.ι.app i).hom := by
    apply ext'
    intro a n
    have h := ConcreteCategory.congr_hom (colimit.isoColimitCocone_ι_hom ⟨c, hc⟩ i) a
    change e.hom.hom ((colimit.ι F i).hom a) = (c.ι.app i).hom a at h
    change e.hom.hom ((colimit.ι F i).hom a) ⊗ₜ[R] n = (c.ι.app i).hom a ⊗ₜ[R] n
    rw [h]
  obtain ⟨hlift, hzero⟩ := CommAlgCat.filteredColimit_tensorProduct_elementwise R F N
  constructor
  · intro x
    obtain ⟨i, t, ht⟩ := hlift (E.symm x)
    refine ⟨i, t, ?_⟩
    calc
      rTensor (R := R) N (c.ι.app i).hom t =
          E (rTensor (R := R) N (colimit.ι F i).hom t) :=
        (DFunLike.congr_fun (hE i) t).symm
      _ = x := by
        rw [show rTensor (R := R) N (colimit.ι F i).hom t = E.symm x from ht]
        exact E.apply_symm_apply x
  · intro i t ht
    apply hzero i t
    apply E.injective
    change E (rTensor (R := R) N (colimit.ι F i).hom t) = E 0
    calc
      E (rTensor (R := R) N (colimit.ι F i).hom t) =
          rTensor (R := R) N (c.ι.app i).hom t := DFunLike.congr_fun (hE i) t
      _ = E 0 := ht.trans (map_zero E).symm

/-- Stagewise tensor embeddings with integral image pass to any specified directed
algebra colimit, and restrict to an embedding into its integral closure. The last two
clauses give compatibility with transition maps and with the colimit coprojections.
All carriers and the index lie in the common universe `u`; no flatness or injectivity
of the transition maps or of `v` is assumed.

Source: Stacks Project, Algebra, Tag 0CBF,
lemma-integral-closure-commutes-colim-smooth, filtered-colimit argument.
(blueprint: lem-sfb-directed-tensor-integral-embedding).

Proof:
1. Use the tensor universal property (def-weil-pbc-module-tensor-product) to form
   `lTensor` and `rTensor`. Multiplication, units and scalar maps are preserved by
   the algebra tensor structure. On pure tensors both transition composites send
   `s tensor c` to `a_ij(s) tensor v(c)`, and both coprojection composites send it
   to `a_i(s) tensor v(c)`. Generation by pure tensors proves both identities.
2. A nonempty directed preorder is filtered (def-weil-pbc-category-colimit). Apply
   lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise to `F`, first with `C`
   and then with `B`. Transport its chosen colimit to the specified colimit `c`
   by the unique cocone-compatible isomorphism furnished by `hc`. Every source
   tensor lifts to a stage; every target tensor that maps to zero vanishes later.
3. Lift `x` in the kernel to `x_i`. Compatibility and eventual zero give a stage
   `j` at which `f_j` kills the transition image of `x_i`. Its injectivity makes
   that transition image zero, hence `x = 0`. Apply this to differences to get
   injectivity of the colimit tensor map.
4. Lift any source tensor to `x_i`. A monic equation over `F.obj i` for `f_i(x_i)`
   exists by h_integral (def-weil-pbc-integral-closure). Apply the target tensor
   coprojection, a ring map. It sends each coefficient `r tensor 1` to
   `a_i(r) tensor 1` and preserves the leading coefficient 1. The resulting
   monic equation shows that the colimit image is integral over `c.pt`.
5. Restrict the codomain to `integralClosure c.pt (c.pt tensor B)`, whose carrier
   is the set of integral elements. The algebra laws are inherited from the
   tensor map. Equality after restriction implies equality in the target tensor,
   hence equality of inputs by step 3. The defining restriction gives the formula
   for all tensors, and its pure-tensor specialization is `s tensor v(c)`.
-/
theorem directed_integral_embedding
    (R C B : Type u) [CommRing R] [CommRing C] [CommRing B]
    [Algebra R C] [Algebra R B] (v : C →ₐ[R] B)
    (I : Type u) [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ CommAlgCat.{u, u} R) (c : Cocone F) (hc : IsColimit c)
    (h_injective : ∀ i : I,
      Function.Injective (lTensor (S := R) (F.obj i) v))
    (h_integral : ∀ (i : I) (x : (F.obj i : Type u) ⊗[R] C),
      IsIntegral (F.obj i) (lTensor (S := R) (F.obj i) v x)) :
    Function.Injective (lTensor (S := R) c.pt v) ∧
    (∀ x : (c.pt : Type u) ⊗[R] C,
      IsIntegral c.pt (lTensor (S := R) c.pt v x)) ∧
    (∃ q : (c.pt : Type u) ⊗[R] C →ₐ[c.pt]
        integralClosure c.pt ((c.pt : Type u) ⊗[R] B),
      Function.Injective q ∧
      (∀ x : (c.pt : Type u) ⊗[R] C,
        (q x : (c.pt : Type u) ⊗[R] B) = lTensor (S := R) c.pt v x) ∧
      (∀ (s : c.pt) (z : C),
        (q (s ⊗ₜ[R] z) : (c.pt : Type u) ⊗[R] B) = s ⊗ₜ[R] v z)) ∧
    (∀ (i j : I) (hij : i ≤ j),
      (rTensor B (F.map (homOfLE hij)).hom).comp (lTensor (S := R) (F.obj i) v) =
        (lTensor (S := R) (F.obj j) v).comp (rTensor C (F.map (homOfLE hij)).hom)) ∧
    (∀ i : I,
      (rTensor B (c.ι.app i).hom).comp (lTensor (S := R) (F.obj i) v) =
        (lTensor (S := R) c.pt v).comp (rTensor C (c.ι.app i).hom)) := by
  have htrans (i j : I) (f : i ⟶ j) :
      (rTensor (R := R) B (F.map f).hom).comp (lTensor (S := R) (F.obj i) v) =
        (lTensor (S := R) (F.obj j) v).comp (rTensor (R := R) C (F.map f).hom) := by
    apply ext'
    intro a z
    rfl
  have hcop (i : I) :
      (rTensor (R := R) B (c.ι.app i).hom).comp (lTensor (S := R) (F.obj i) v) =
        (lTensor (S := R) c.pt v).comp (rTensor (R := R) C (c.ι.app i).hom) := by
    apply ext'
    intro a z
    rfl
  have hcomp (i j : I) (f : i ⟶ j) :
      (rTensor (R := R) C (c.ι.app j).hom).comp (rTensor (R := R) C (F.map f).hom) =
        rTensor (R := R) C (c.ι.app i).hom := by
    apply ext'
    intro a z
    have h := ConcreteCategory.congr_hom (c.w f) a
    change (c.ι.app j).hom ((F.map f).hom a) = (c.ι.app i).hom a at h
    change (c.ι.app j).hom ((F.map f).hom a) ⊗ₜ[R] z =
      (c.ι.app i).hom a ⊗ₜ[R] z
    rw [h]
  obtain ⟨hlift, _⟩ := tensor_elementwise R C I F c hc
  obtain ⟨_, hzero⟩ := tensor_elementwise R B I F c hc
  have hkernel (x : (c.pt : Type u) ⊗[R] C)
      (hx : lTensor (S := R) c.pt v x = 0) : x = 0 := by
    obtain ⟨i, t, rfl⟩ := hlift x
    have ht : rTensor (R := R) B (c.ι.app i).hom (lTensor (S := R) (F.obj i) v t) = 0 := by
      exact (DFunLike.congr_fun (hcop i) t).trans hx
    obtain ⟨j, f, hf⟩ := hzero i _ ht
    have hf' : lTensor (S := R) (F.obj j) v (rTensor (R := R) C (F.map f).hom t) = 0 := by
      exact (DFunLike.congr_fun (htrans i j f) t).symm.trans hf
    have ht' : rTensor (R := R) C (F.map f).hom t = 0 :=
      h_injective j (hf'.trans (map_zero _).symm)
    calc
      rTensor (R := R) C (c.ι.app i).hom t =
          rTensor (R := R) C (c.ι.app j).hom (rTensor (R := R) C (F.map f).hom t) :=
        (DFunLike.congr_fun (hcomp i j f) t).symm
      _ = 0 := by rw [ht', map_zero]
  have hinj : Function.Injective (lTensor (S := R) c.pt v) := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hkernel
    rw [map_sub, hxy, sub_self]
  have hint (x : (c.pt : Type u) ⊗[R] C) :
      IsIntegral c.pt (lTensor (S := R) c.pt v x) := by
    obtain ⟨i, t, rfl⟩ := hlift x
    have hcoeff :
        (algebraMap c.pt ((c.pt : Type u) ⊗[R] B)).comp (c.ι.app i).hom.toRingHom =
          (rTensor (R := R) B (c.ι.app i).hom).toRingHom.comp
            (algebraMap (F.obj i) ((F.obj i : Type u) ⊗[R] B)) := by
      ext a
      simp
    have h := IsIntegral.map_of_comp_eq
      (T := (c.pt : Type u)) (U := (c.pt : Type u) ⊗[R] B)
      (c.ι.app i).hom.toRingHom
      (rTensor (R := R) B (c.ι.app i).hom).toRingHom hcoeff (h_integral i t)
    exact (DFunLike.congr_fun (hcop i) t) ▸ h
  refine ⟨hinj, hint, ?_, fun i j hij ↦ htrans i j (homOfLE hij), hcop⟩
  let f : (c.pt : Type u) ⊗[R] C →ₐ[c.pt] (c.pt : Type u) ⊗[R] B :=
    lTensor (S := c.pt) c.pt v
  let q := f.codRestrict (integralClosure c.pt ((c.pt : Type u) ⊗[R] B)) hint
  refine ⟨q, ?_, fun _ ↦ rfl, fun _ _ ↦ rfl⟩
  intro x y hxy
  apply hinj
  exact congrArg (fun z : integralClosure c.pt ((c.pt : Type u) ⊗[R] B) ↦
    (z : (c.pt : Type u) ⊗[R] B)) hxy

end Algebra.TensorProduct
