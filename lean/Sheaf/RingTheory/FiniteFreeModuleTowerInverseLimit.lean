/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Free
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Sheaf.RingTheory.CompatibleFiniteFreeModuleBases

/-! # Finite-free module towers over nilpotent quotient rings

Source: Stacks Project, More on Algebra, Tag 0CQF.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory Module
open scoped TensorProduct

namespace ModuleCat

/-- Compatible finite-free modules have a finite-free tuple limit and recover each level.
Source: Stacks Project, More on Algebra, Tag 0CQF, compatible-basis calculation
(blueprint: lem-weil-pbc-finite-free-module-tower-inverse-limit).

Proof: Choose a finite basis at level zero. Inductively lift its vectors through u.
The resulting vectors form a basis upstairs. Indeed the associated map from a free
module reduces to an isomorphism. Lift its inverse matrix; both error matrices have
entries in the nilpotent kernel. The finite geometric series inverts each error,
giving a left and a right inverse for the lifted basis map. They agree, so the map is
an isomorphism. This also handles rank zero and zero rings. The compatible bases
identify the tuple limit with a fixed finite power of the ring of compatible scalar
tuples. The given scalar universal property identifies this ring with A. The universal
property of P gives the corresponding A-linear isomorphism from P to this finite power,
hence freeness and finiteness. In these coordinates every p_n is coordinatewise q_n.
Its scalar-extension adjoint sends each standard vector tensor 1 to the standard vector;
it is therefore an isomorphism. The argument is independent of differentials and upper
bounds, which play no role in this degreewise assertion. -/
theorem finiteFree_moduleTower_inverseLimit
    (R : ℕ → Type u) [∀ n, CommRing (R n)]
    (φ : ∀ n, R (n + 1) →+* R n)
    (hsurj : ∀ n, Function.Surjective (φ n))
    (hnil : ∀ n, IsNilpotent (RingHom.ker (φ n)))
    (A : Type u) [CommRing A] (q : ∀ n, A →+* R n)
    (hq : ∀ n, q n = (φ n).comp (q (n + 1)))
    (hlim : ∀ x : ∀ n, R n, (∀ n, φ n (x (n + 1)) = x n) →
      ∃! a : A, ∀ n, q n a = x n)
    (N : ∀ n, ModuleCat.{max u v} (R n))
    (uₙ : ∀ n, N (n + 1) ⟶ (restrictScalars (φ n)).obj (N n))
    (θₙ : ∀ n, (extendScalars (φ n)).obj (N (n + 1)) ≅ N n)
    (hterms : ∀ n, Module.Free (R n) (N n) ∧ Module.Finite (R n) (N n))
    (hsurju : ∀ n, Function.Surjective (uₙ n))
    (hθₙ : ∀ n, (extendRestrictScalarsAdj (φ n)).homEquiv
      (N (n + 1)) (N n) (θₙ n).hom = uₙ n)
    (P : ModuleCat.{max u v} A)
    (p : ∀ n, P ⟶ (restrictScalars (q n)).obj (N n))
    (hp : ∀ n (y : P), uₙ n (p (n + 1) y) = p n y)
    (hP : ∀ x : ∀ n, N n, (∀ n, uₙ n (x (n + 1)) = x n) →
      ∃! y : P, ∀ n, p n y = x n) :
    (Module.Free A P ∧ Module.Finite A P) ∧
      ∀ n, IsIso (((extendRestrictScalarsAdj (q n)).homEquiv P (N n)).symm (p n)) := by
  classical
  obtain ⟨r, e, he⟩ := exists_compatible_finiteFree_module_coordinates
    R φ hsurj hnil N uₙ θₙ hterms hsurju hθₙ
  have hcompat (y : P) (j : Fin r) :
      ∀ n, φ n (e (n + 1) (p (n + 1) y) j) = e n (p n y) j := by
    intro n
    rw [← he, hp]
  let f : P → Fin r → A := fun y j ↦
    (hlim (fun n ↦ e n (p n y) j) (hcompat y j)).choose
  have hf (y : P) (j : Fin r) (n : ℕ) : q n (f y j) = e n (p n y) j :=
    (hlim (fun n ↦ e n (p n y) j) (hcompat y j)).choose_spec.1 n
  have hsep {a b : A} (h : ∀ n, q n a = q n b) : a = b := by
    have hc : ∀ n, φ n (q (n + 1) b) = q n b := fun n ↦
      (RingHom.congr_fun (hq n) b).symm
    obtain ⟨c, hc, huniq⟩ := hlim (fun n ↦ q n b) hc
    exact (huniq a h).trans (huniq b (fun _ ↦ rfl)).symm
  let fl : P →ₗ[A] (Fin r → A) :=
    { toFun := f
      map_add' := by
        intro y z
        funext j
        apply hsep
        intro n
        simp only [Pi.add_apply, map_add, hf]
      map_smul' := by
        intro a y
        funext j
        apply hsep
        intro n
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, hf]
        change e n (p n (a • y)) j = q n a * e n (p n y) j
        rw [map_smul]
        change e n (q n a • p n y) j = q n a * e n (p n y) j
        simp }
  have hfl : Function.Bijective fl := by
    constructor
    · intro y z hyz
      have hpn (n : ℕ) : p n y = p n z := by
        apply (e n).injective
        funext j
        rw [← hf y j n, ← hf z j n]
        exact congrArg (fun f ↦ q n (f j)) hyz
      obtain ⟨a, ha, huniq⟩ := hP (fun n ↦ p n z) (fun n ↦ hp n z)
      exact (huniq y hpn).trans (huniq z (fun _ ↦ rfl)).symm
    · intro a
      let x := fun n ↦ (e n).symm (fun j ↦ q n (a j))
      have hx (n : ℕ) : uₙ n (x (n + 1)) = x n := by
        apply (e n).injective
        funext j
        rw [he]
        simp only [x, LinearEquiv.apply_symm_apply]
        exact (RingHom.congr_fun (hq n) (a j)).symm
      obtain ⟨y, hy, _⟩ := hP x hx
      refine ⟨y, ?_⟩
      funext j
      apply hsep
      intro n
      change q n (f y j) = q n (a j)
      rw [hf, hy]
      simp [x]
  let eP := LinearEquiv.ofBijective fl hfl
  have hfree : Module.Free A P := Module.Free.of_equiv eP.symm
  have hfinite : Module.Finite A P := Module.Finite.equiv eP.symm
  refine ⟨⟨hfree, hfinite⟩, ?_⟩
  intro n
  let : Algebra A (R n) := (q n).toAlgebra
  let bP := Basis.ofEquivFun eP
  let bN := Basis.ofEquivFun (e n)
  let θ := (bP.baseChange (R n)).equiv bN (Equiv.refl _)
  let g := (((extendRestrictScalarsAdj (q n)).homEquiv P (N n)).symm (p n))
  have hpb (j : Fin r) : p n (bP j) = bN j := by
    apply (e n).injective
    funext k
    rw [← hf (bP j) k n]
    have hj : f (bP j) = Pi.single j 1 := by
      change eP (bP j) = _
      simp [bP, Basis.coe_ofEquivFun]
    rw [hj]
    simp [bN, Basis.coe_ofEquivFun, Pi.single_apply]
  have hg : g.hom = θ.toLinearMap := by
    apply (bP.baseChange (R n)).ext
    intro j
    change g.hom ((bP.baseChange (R n)) j) = θ ((bP.baseChange (R n)) j)
    rw [Basis.equiv_apply, Basis.baseChange_apply]
    have h := congrArg (fun k : P ⟶ (restrictScalars (q n)).obj (N n) ↦ k (bP j))
      (((extendRestrictScalarsAdj (q n)).homEquiv P (N n)).apply_symm_apply (p n))
    rw [extendRestrictScalarsAdj_homEquiv_apply] at h
    exact h.trans (hpb j)
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective g.hom
  rw [hg]
  exact θ.bijective

end ModuleCat
