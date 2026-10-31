/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.RingTheory.PolynomialActionReduction

/-!
# Finite presentation over a finite type algebra

Source: Stacks Project, `algebra.tex`, Lemma Tag 0561
(lemma-finitely-presented-over-subring), statement and proof
(blueprint: lem-trf-finitely-presented-over-subring).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Module.FinitePresentation

/-- An `S`-module finitely presented over `R` is finitely presented over `S` when the ring map
`R → S` is of finite type. The `R`-module structure is restriction along the given ring map.

Source: Stacks Project, `algebra.tex`, Lemma Tag 0561
(lemma-finitely-presented-over-subring), statement and proof
(blueprint: lem-trf-finitely-presented-over-subring).

Proof: (1) By `def-weil-pbc-finite-type-algebra`, choose algebra generators `x₁, …, xₙ` of `S`.
By `def-sc-finitely-presented-module`, choose `R`-module generators `y₁, …, yₘ` of `M` and
finitely many vectors generating their relation module.
(2) Express each `xᵢ yⱼ` as an `R`-linear combination of the `yₖ`. Define `N` with the same
`m` generators over `S`, the original finitely many relations, and these `nm` action
relations. This is a finite presentation of `N` over `S`.
(3) Sending the generators of `N` to the corresponding `yⱼ` respects every relation and
induces a surjective `S`-linear map `N → M`, since the `yⱼ` already generate over `R`.
(4) By `lem-trf-polynomial-action-reduction`, the action relations lower polynomial degree
and express any element of `N` as an `R`-linear combination of the generators. If its image
in `M` vanishes, its coefficient vector belongs to the `R`-span of the original relation
vectors, which are relations in `N` too. Thus the map is injective.
(5) The map is an isomorphism, so the finite presentation of `N` transfers to `M`.
-/
theorem of_finiteType_subring
    {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [AddCommGroup M]
    (f : R →+* S) [Module S M] (hS : RingHom.FiniteType f)
    (hM : @Module.FinitePresentation R M _ _ (Module.compHom M f)) :
    Module.FinitePresentation S M := by
  classical
  let : Algebra R S := f.toAlgebra
  let : Module R M := Module.compHom M f
  have : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : Module.FinitePresentation R M := hM
  obtain ⟨s, hs⟩ := hS.out
  let x : Fin s.card → S := fun i ↦ s.equivFin.symm i
  have hx : Algebra.adjoin R (Set.range x) = ⊤ := by
    have hrange : Set.range x = (s : Set S) := by
      ext z
      constructor
      · rintro ⟨i, rfl⟩
        exact (s.equivFin.symm i).property
      · intro hz
        exact ⟨s.equivFin ⟨z, hz⟩, by simp [x]⟩
    simpa [hrange] using hs
  obtain ⟨m, y, hy⟩ := Module.Finite.exists_fin (R := R) (M := M)
  let p : (Fin m → R) →ₗ[R] M := Fintype.linearCombination R y
  have hp : Function.Surjective p :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination R y).mp hy
  have hker : (LinearMap.ker p).FG := fg_ker p hp
  let t : (Fin m → R) →ₗ[R] (Fin m → S) :=
    LinearMap.pi fun j ↦ (Algebra.linearMap R S).comp (LinearMap.proj j)
  let q : (Fin m → S) →ₗ[S] M := Fintype.linearCombination S y
  have hqt (c : Fin m → R) : q (t c) = p c := by
    simp [q, p, t, Fintype.linearCombination_apply, algebraMap_smul]
  choose a ha using fun (i : Fin s.card) (j : Fin m) ↦ hp (x i • y j)
  let d : Fin s.card × Fin m → (Fin m → S) := fun ij ↦
    x ij.1 • Pi.single ij.2 1 - t (a ij.1 ij.2)
  let L₀ : Submodule S (Fin m → S) :=
    Submodule.span S ((LinearMap.ker p).map t : Set (Fin m → S))
  let L₁ : Submodule S (Fin m → S) := Submodule.span S (Set.range d)
  let L : Submodule S (Fin m → S) := L₀ ⊔ L₁
  have hL : L.FG := (hker.map t).span.sup (Submodule.fg_span (Set.finite_range d))
  have htmem {c : Fin m → R} (hc : p c = 0) : t c ∈ L := by
    exact (show L₀ ≤ L from le_sup_left) (Submodule.subset_span ⟨c, hc, rfl⟩)
  have hLq : L ≤ LinearMap.ker q := by
    apply sup_le
    · apply Submodule.span_le.mpr
      rintro _ ⟨c, hc, rfl⟩
      change q (t c) = 0
      rw [hqt]
      exact hc
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨i, j⟩, rfl⟩
      simp [d, q, hqt, ha, Fintype.linearCombination_apply_single]
  let e : Fin m → ((Fin m → S) ⧸ L) := fun j ↦ L.mkQ (Pi.single j 1)
  have hsum (v : Fin m → S) : (∑ j, v j • e j) = L.mkQ v := by
    have hb (j : Fin m) :
        (fun k : Fin m ↦ if j = k then (1 : S) else 0) = Pi.single j 1 := by
      ext k
      simp [Pi.single_apply, eq_comm]
    simpa only [hb] using (LinearMap.pi_apply_eq_sum_univ L.mkQ v).symm
  have htq (c : Fin m → R) : L.mkQ (t c) = ∑ j, c j • e j := by
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro j _
    exact algebraMap_smul S (c j) (e j)
  have he : Submodule.span S (Set.range e) = ⊤ := by
    apply (span_range_eq_top_iff_surjective_fintypeLinearCombination S e).mpr
    intro z
    obtain ⟨v, rfl⟩ := L.mkQ_surjective z
    exact ⟨v, hsum v⟩
  have hea (i : Fin s.card) (j : Fin m) :
      x i • e j = ∑ k, a i j k • e k := by
    have hd : d (i, j) ∈ L :=
      (show L₁ ≤ L from le_sup_right) (Submodule.subset_span ⟨(i, j), rfl⟩)
    have hz : L.mkQ (d (i, j)) = 0 := by simpa using hd
    apply sub_eq_zero.mp
    simpa only [d, map_sub, map_smul, ← htq, e] using hz
  let φ : ((Fin m → S) ⧸ L) →ₗ[S] M := L.liftQ q hLq
  have hφq (v : Fin m → S) : φ (L.mkQ v) = q v := rfl
  have hφ : Function.Surjective φ := by
    intro z
    obtain ⟨c, rfl⟩ := hp z
    exact ⟨L.mkQ (t c), hqt c⟩
  have hφinj : Function.Injective φ := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro z hz
    obtain ⟨c, hc⟩ := Module.exists_eq_sum_smul_of_polynomial_action x e hx he a hea z
    have hzc : z = L.mkQ (t c) := hc.trans (htq c).symm
    have hpc : p c = 0 := by rw [hzc, hφq, hqt] at hz; exact hz
    rw [hzc]
    simpa using htmem hpc
  have : Module.FinitePresentation S ((Fin m → S) ⧸ L) :=
    Module.finitePresentation_of_surjective L.mkQ L.mkQ_surjective (by simpa using hL)
  exact of_equiv (LinearEquiv.ofBijective φ ⟨hφinj, hφ⟩)

end Module.FinitePresentation
