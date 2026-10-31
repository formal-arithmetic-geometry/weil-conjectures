/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LogRegularPair
import WeilConjectures.GroupTheory.SharpConeLatticeIntersection
import WeilConjectures.TraceFormula.RationalConeDualIntegralForms

/-!
# Lattice-intersection embedding of a sharp fs monoid

Source: ILO, Exposé VIII 3.1.17 and Remark 3.1.29, printed pp. 101 and 103
(blueprint: lem-trf-sharp-fs-orthant-embedding).
-/

set_option autoImplicit false

@[expose] public section

open Set

universe u

namespace AlgebraicGeometry

private theorem hull_range_eq_nonneg_sum {V : Type u} [AddCommGroup V] [Module ℚ V]
    (m : ℕ) (v : Fin m → V) :
    (PointedCone.hull ℚ (Set.range v) : Set V) =
      {x | ∃ q : Fin m → ℚ≥0, x = ∑ j, (q j : ℚ) • v j} := by
  ext x
  change x ∈ Submodule.span {q : ℚ // 0 ≤ q} (Set.range v) ↔ _
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨fun i ↦ ⟨(q i).1, (q i).2⟩, hq.symm⟩
  · rintro ⟨q, hq⟩
    exact ⟨fun i ↦ ⟨(q i : ℚ), (q i).2⟩, hq.symm⟩

/-- A finitely generated integral saturated sharp commutative monoid embeds in an
integer lattice so that its image is exactly the lattice points in a nonnegative
orthant.  The multiplicative presentation of monoids in Lean is identified with
the additive notation of the source by the Grothendieck group construction and
`Additive` type synonym. Source: ILO, Exposé VIII 3.1.17 and Remark 3.1.29,
printed pp. 101 and 103 (blueprint: lem-trf-sharp-fs-orthant-embedding).

Proof plan: apply the sharp rational-cone lattice-intersection statement and the
integral dual-cone description to obtain finitely many integral linear forms;
their product map is injective because the forms span the rational dual, and its
nonnegative locus is precisely the original monoid. The empty family handles the
trivial monoid, so rank zero is included.
-/
theorem exists_sharp_fs_orthant_embedding (P : Type u) [CommMonoid P]
    (hP : IsFineSaturatedMonoid P)
    (hsharp : ∀ a b : P, a * b = 1 → a = 1 ∧ b = 1) :
    ∃ (r : ℕ)
      (embedding : Additive (Algebra.GrothendieckGroup P) →+ (Fin r → ℤ)),
      Function.Injective embedding ∧
        (embedding '' Set.range (fun p : P => (Algebra.GrothendieckGroup.of p))) =
          Set.range embedding ∩ Set.Ici (0 : Fin r → ℤ) := by
  classical
  let G := Additive (Algebra.GrothendieckGroup P)
  let V := TensorProduct ℤ ℚ G
  let C : PointedCone ℚ V := PointedCone.hull ℚ
    (Set.range (fun p : P ↦ TensorProduct.tmul ℤ (1 : ℚ)
      (Additive.ofMul (Algebra.GrothendieckGroup.of p))))
  have hsharp' : ∀ p : Additive P, IsAddUnit p → p = 0 := by
    intro p hp
    obtain ⟨q, hpq, _⟩ := isAddUnit_iff_exists.mp hp
    exact (hsharp p.toMul q.toMul hpq).1
  obtain ⟨hbasis, htensor, hfinite, hpointed, hspan, hlattice⟩ :=
    sharp_fs_monoid_cone_lattice_intersection (Additive P) hP hsharp' C rfl
  obtain ⟨d, ⟨b⟩⟩ := hbasis
  let : Module.Free ℤ G := Module.Free.of_basis b
  let : Module.Finite ℤ G := Module.Finite.of_basis b
  change ∃ (m : ℕ) (v : Fin m → G),
    C = PointedCone.hull ℚ (Set.range (fun j ↦ TensorProduct.tmul ℤ (1 : ℚ) (v j))) at hfinite
  change ∀ x : V, ∃ a ∈ (C : Set V), ∃ b ∈ (C : Set V), x = a - b at hspan
  obtain ⟨m, v, hv⟩ := hfinite
  have hC : (C : Set V) =
      {x | ∃ q : Fin m → ℚ≥0, x = ∑ j, (q j : ℚ) • TensorProduct.tmul ℤ (1 : ℚ) (v j)} := by
    rw [hv]
    exact hull_range_eq_nonneg_sum m _
  have hpointed' : (C : Set V) ∩ (-(C : Set V)) = {0} := by
    apply Set.Subset.antisymm
    · intro x hx
      exact Set.mem_singleton_iff.mpr (hpointed x hx.1 (by simpa using hx.2))
    · rintro x rfl
      exact ⟨C.zero_mem, by simp⟩
  obtain ⟨⟨r, φ, Φ, hcompat, _, hcut, _⟩, _⟩ :=
    rationalConeDualIntegralForms G m v (by simpa only [hC] using hpointed')
      (by simpa only [hC] using hspan)
  let embedding : G →+ (Fin r → ℤ) :=
    { toFun := fun g i ↦ φ i g
      map_zero' := by ext i; exact map_zero (φ i)
      map_add' := by intros; ext i; exact map_add (φ i) _ _ }
  have hnonneg (g : G) : (∀ i, 0 ≤ φ i g) ↔ TensorProduct.tmul ℤ (1 : ℚ) g ∈ C := by
    change (∀ i, 0 ≤ φ i g) ↔ TensorProduct.tmul ℤ (1 : ℚ) g ∈ (C : Set V)
    rw [hC, hcut]
    simp only [Set.mem_ofPred_eq, hcompat, Int.cast_nonneg_iff]
  have hinj : Function.Injective embedding := by
    apply (injective_iff_map_eq_zero embedding).mpr
    intro g hg
    have hzero (i : Fin r) : φ i g = 0 := congrFun hg i
    have hpos : TensorProduct.tmul ℤ (1 : ℚ) g ∈ C :=
      (hnonneg g).mp (fun i ↦ by rw [hzero i])
    have hneg : -(TensorProduct.tmul ℤ (1 : ℚ) g) ∈ C := by
      rw [← TensorProduct.tmul_neg]
      exact (hnonneg (-g)).mp (fun i ↦ by simp [hzero])
    apply htensor
    simpa using hpointed _ hpos hneg
  refine ⟨r, embedding, hinj, ?_⟩
  ext x
  constructor
  · rintro ⟨g, ⟨p, rfl⟩, rfl⟩
    refine ⟨⟨Additive.ofMul (Algebra.GrothendieckGroup.of p), rfl⟩, ?_⟩
    change ∀ i, 0 ≤ φ i (Additive.ofMul (Algebra.GrothendieckGroup.of p))
    apply (hnonneg _).mpr
    exact (hlattice _).mpr ⟨Additive.ofMul p, rfl⟩
  · rintro ⟨⟨g, rfl⟩, hg⟩
    have hmem : TensorProduct.tmul ℤ (1 : ℚ) g ∈ C := (hnonneg g).mp hg
    obtain ⟨p, hp⟩ := (hlattice g).mp hmem
    exact ⟨g, ⟨p.toMul, hp⟩, rfl⟩

end AlgebraicGeometry
