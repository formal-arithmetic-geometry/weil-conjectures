/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FormalKernelPolynomialAction
import WeilConjectures.AlgebraicGeometry.GradedSerreVanishing
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Uniform vanishing for kernels of coherent formal systems

## References

* [Stacks Project, Tag 0884](https://stacks.math.columbia.edu/tag/0884)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- For a coherent formal system over a proper Noetherian base, an ample twist kills
first cohomology of every successive kernel with a single bound. The index `op k`
represents F_(k+1). The zero case uses ker(F_1 → 0) ≅ F_1. Tensor exponents are natural
numbers; the bound is an integer. -/
theorem coherentFormalModule_kernel_twist_vanishing
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (L : X.Modules) [L.IsInvertible] (hL : Scheme.Modules.IsAmple X L)
    (F : @CoherentFormalModule X (isNoetherian_of_locallyOfFiniteType f)
      ((Scheme.IdealSheafData.ofIdealTop
        (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)) :
    ∃ d₀ : ℤ, ∀ (n d : ℕ), d₀ ≤ (d : ℤ) →
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj
        (Scheme.Modules.tensorObj (match n with
          | 0 => F.obj.obj (op 0)
          | k + 1 => kernel (F.obj.map (homOfLE (Nat.le_succ k)).op)) (L.tensorPow d))) := by
  classical
  let : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  let G := formalKernelPiece F
  have hG : ∀ m : ℕ, (G m).IsQuasicoherent := by
    intro m
    have hF (k : ℕ) : (F.obj.obj (op k)).IsQuasicoherent :=
      ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp
        (F.property.1 k)).1
    cases m with
    | zero => exact hF 0
    | succ k =>
      have := hF k
      have := hF (k + 1)
      exact Scheme.Modules.isQuasicoherent_kernel
        (F.obj.map (homOfLE (Nat.le_succ k)).op)
  obtain ⟨r, mu, hadd, hmul, hscalar, hgen⟩ := formalKernel_polynomial_action I f F
  let graded := MvPolynomial.homogeneousSubmodule (Fin r) A
  have hg : DirectSum.IsInternal graded := by
    let : DirectSum.Decomposition graded := MvPolynomial.decomposition
    exact DirectSum.Decomposition.isInternal graded
  have hu : (1 : MvPolynomial (Fin r) A) ∈ graded 0 :=
    MvPolynomial.isHomogeneous_one (Fin r) A
  have hm : ∀ (k l : ℕ) {x y : MvPolynomial (Fin r) A},
      x ∈ graded k → y ∈ graded l → x * y ∈ graded (k + l) := by
    intro k l x y hx hy
    exact hx.mul hy
  have hs : ∀ a : A, algebraMap A (MvPolynomial (Fin r) A) a ∈ graded 0 :=
    fun a ↦ MvPolynomial.isHomogeneous_C (Fin r) a
  have hfinite : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      ∃ (s : ℕ) (d : Fin s → ℕ) (t : ∀ i : Fin s, (G (d i)).val.obj (op U)),
        ∀ (m : ℕ) (V : X.Opens) (hVU : V ≤ U) (v : (G m).val.obj (op V))
          (y : X), y ∈ V → ∃ (W : X.Opens) (hWV : W ≤ V), y ∈ W ∧
            (G m).val.map (homOfLE hWV).op v ∈
              Submodule.span ((moduleRings X.toRingedSpace).obj.obj (op W))
                {z | ∃ (i : Fin s), d i ≤ m ∧ ∃ b : graded (m - d i),
                  HEq z ((mu (d i) (m - d i) b).val.app (op W)
                    ((G (d i)).val.map (homOfLE (hWV.trans hVU)).op (t i)))} := by
    intro x
    obtain ⟨U, hx, s, t, ht⟩ := hgen x
    refine ⟨U, hx, s, fun _ ↦ 0, t, ?_⟩
    intro m V hVU v y hy
    obtain ⟨W, hWV, hyW, hv⟩ := ht m V hVU v y hy
    refine ⟨W, hWV, hyW, ?_⟩
    apply Submodule.span_mono ?_ hv
    rintro z ⟨i, b, hz⟩
    exact ⟨i, Nat.zero_le m, b, hz⟩
  obtain ⟨d₀, hv⟩ := graded_serre_vanishing graded hg hu hm hs f G hG mu
    hadd hmul hscalar hfinite L hL
  refine ⟨(d₀ : ℤ), ?_⟩
  intro n d hd
  have hd' : d₀ ≤ d := by exact_mod_cast hd
  have hz := hv 1 d (by decide) hd'
  let π : (∐ G) ⟶ G n := Sigma.desc
    (fun j ↦ if h : j = n then eqToHom (congrArg G h) else 0)
  have hπ : Sigma.ι G n ≫ π = 𝟙 (G n) := by
    simp [π]
  let T := CategoryTheory.MonoidalCategory.tensorRight (L.tensorPow d) ⋙
    RingedSpace.moduleCohomology X.toRingedSpace 1
  change IsZero (T.obj (G n))
  apply (IsZero.iff_id_eq_zero _).mpr
  rw [← T.map_id, ← hπ, T.map_comp]
  rw [(show IsZero (T.obj (∐ G)) from hz).eq_zero_of_tgt (T.map (Sigma.ι G n))]
  simp

end AlgebraicGeometry
