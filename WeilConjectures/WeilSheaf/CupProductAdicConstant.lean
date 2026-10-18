/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicConstantCup
public import WeilConjectures.WeilSheaf.CohomologyAdicConstantLattice

/-!
# The cup product on the cohomology of the constant Weil sheaf

Let `Y` be a `k₀`-scheme of finite type whose geometric fiber `Ȳ = Y ⊗ k̄` is connected,
quasi-compact and quasi-separated, with finite cohomology groups `Hᵏ(Ȳ, ℤ/ℓᵐ)`. Through the
identification `Hʳ(Y ⊗ k̄, ℚ̄_ℓ) ≅ Hʳ(Ȳ_proét, ℚ̄_ℓ)`, under which the geometric Frobenius is the
pullback along the geometric Galois Frobenius
(`AlgebraicGeometry.WeilSheaf.exists_linearEquiv_adicConstantH_cohomology_adicConstantHPullback`),
the cup product of `Hⁿ(Ȳ, ℚ̄_ℓ)` (`AlgebraicGeometry.ProEtale.adicConstantCup`) defines a cup
product `Hⁱ × Hʲ ⟶ Hᵏ`, `i + j = k`, on the cohomology of the constant Weil sheaf
(`AlgebraicGeometry.WeilSheaf.adicConstantCup`, zero in negative degrees). It commutes with the
geometric Frobenius (`AlgebraicGeometry.WeilSheaf.adicConstantCup_frobenius`) and is graded
commutative (`AlgebraicGeometry.WeilSheaf.adicConstantCup_comm`): these are the fields `cup`,
`cup_frobenius` and `cup_comm` of `FrobeniusModule.TraceCup`.

The construction assumes that the finite-level cup products are compatible with the transition
maps `Hⁿ(Ȳ, ℤ/ℓᵐ⁺¹) ⟶ Hⁿ(Ȳ, ℤ/ℓᵐ)` (`AlgebraicGeometry.ProEtale.FiniteAdicCupCompatible`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

namespace WeilSheaf

variable [Fact (ringChar k₀ ≠ l)] {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

/-- The identification of the cohomology groups in equal degrees. -/
noncomputable def cohomologyCast (F : WeilSheaf k₀ l Y) {r r' : ℤ} (h : r = r') :
    (F.cohomology r).carrier ≃ₗ[PadicAlgCl l] (F.cohomology r').carrier := by
  subst h
  exact LinearEquiv.refl _ _

lemma cohomologyCast_frobenius (F : WeilSheaf k₀ l Y) {r r' : ℤ} (h : r = r')
    (x : (F.cohomology r).carrier) :
    cohomologyCast F h ((F.cohomology r).frobenius x) =
      (F.cohomology r').frobenius (cohomologyCast F h x) := by
  subst h
  rfl

variable (k₀ l Y) in
/-- A chosen Frobenius-equivariant identification `Hʳ(Ȳ_proét, ℚ̄_ℓ) ≅ Hʳ(Y ⊗ k̄, ℚ̄_ℓ)`. -/
noncomputable def adicConstantHEquiv (r : ℕ) :
    AdicConstantH l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber r ≃ₗ[PadicAlgCl l]
      ((WeilSheaf.adicConstant k₀ l Y).cohomology r).carrier :=
  (exists_linearEquiv_adicConstantH_cohomology_adicConstantHPullback (k₀ := k₀) (l := l)
    (Y := Y) r).choose

lemma adicConstantHEquiv_symm_frobenius (r : ℕ)
    (z : ((WeilSheaf.adicConstant k₀ l Y).cohomology r).carrier) :
    (adicConstantHEquiv k₀ l Y r).symm
        (((WeilSheaf.adicConstant k₀ l Y).cohomology r).frobenius z) =
      adicConstantHPullback l (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius r
        ((adicConstantHEquiv k₀ l Y r).symm z) := by
  rw [LinearEquiv.symm_apply_eq, adicConstantHEquiv,
    (exists_linearEquiv_adicConstantH_cohomology_adicConstantHPullback r).choose_spec,
    ← adicConstantHEquiv, LinearEquiv.apply_symm_apply]

variable [CompactSpace (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber]
  [QuasiSeparatedSpace (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber]
  (hfin : ∀ m k, Finite (FiniteAdicH (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber l m k))
  (hc : FiniteAdicCupCompatible l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)

/-- The cup product `Hᵃ × Hᵇ ⟶ Hⁿ`, `a + b = n`, on the cohomology of the constant Weil sheaf,
for natural degrees. -/
noncomputable def adicConstantCupNat (a b n : ℕ) (hn : a + b = n) :
    ((WeilSheaf.adicConstant k₀ l Y).cohomology a).carrier →ₗ[PadicAlgCl l]
      ((WeilSheaf.adicConstant k₀ l Y).cohomology b).carrier →ₗ[PadicAlgCl l]
        ((WeilSheaf.adicConstant k₀ l Y).cohomology n).carrier :=
  ((adicConstantCup hfin hc a b n hn).compr₂ (adicConstantHEquiv k₀ l Y n).toLinearMap).compl₁₂
    (adicConstantHEquiv k₀ l Y a).symm.toLinearMap (adicConstantHEquiv k₀ l Y b).symm.toLinearMap

lemma adicConstantCupNat_apply (a b n : ℕ) (hn : a + b = n)
    (x : ((WeilSheaf.adicConstant k₀ l Y).cohomology a).carrier)
    (y : ((WeilSheaf.adicConstant k₀ l Y).cohomology b).carrier) :
    adicConstantCupNat hfin hc a b n hn x y = adicConstantHEquiv k₀ l Y n
      (adicConstantCup hfin hc a b n hn ((adicConstantHEquiv k₀ l Y a).symm x)
        ((adicConstantHEquiv k₀ l Y b).symm y)) :=
  rfl

/-- **The cup product on the cohomology of the constant Weil sheaf**
`Hⁱ(Y ⊗ k̄, ℚ̄_ℓ) × Hʲ(Y ⊗ k̄, ℚ̄_ℓ) ⟶ Hᵏ(Y ⊗ k̄, ℚ̄_ℓ)`, `i + j = k`: the cup product of
`Hⁿ(Ȳ_proét, ℚ̄_ℓ)` (`AlgebraicGeometry.ProEtale.adicConstantCup`), zero in negative degrees. -/
noncomputable def adicConstantCup (i j k : ℤ) (h : i + j = k) :
    ((WeilSheaf.adicConstant k₀ l Y).cohomology i).carrier →ₗ[PadicAlgCl l]
      ((WeilSheaf.adicConstant k₀ l Y).cohomology j).carrier →ₗ[PadicAlgCl l]
        ((WeilSheaf.adicConstant k₀ l Y).cohomology k).carrier :=
  if hij : 0 ≤ i ∧ 0 ≤ j then
    ((adicConstantCupNat hfin hc i.toNat j.toNat k.toNat (by omega)).compl₁₂
      (cohomologyCast _ (by omega : i = (i.toNat : ℤ))).toLinearMap
      (cohomologyCast _ (by omega : j = (j.toNat : ℤ))).toLinearMap).compr₂
        (cohomologyCast _ (by omega : (k.toNat : ℤ) = k)).toLinearMap
  else 0

lemma adicConstantCup_apply (i j k : ℤ) (h : i + j = k) (hij : 0 ≤ i ∧ 0 ≤ j)
    (x : ((WeilSheaf.adicConstant k₀ l Y).cohomology i).carrier)
    (y : ((WeilSheaf.adicConstant k₀ l Y).cohomology j).carrier) :
    adicConstantCup hfin hc i j k h x y = cohomologyCast _ (by omega : (k.toNat : ℤ) = k)
      (adicConstantCupNat hfin hc i.toNat j.toNat k.toNat (by omega)
        (cohomologyCast _ (by omega : i = (i.toNat : ℤ)) x)
        (cohomologyCast _ (by omega : j = (j.toNat : ℤ)) y)) := by
  simp [adicConstantCup, hij]

set_option maxRecDepth 4000 in
/-- **The cup product commutes with the geometric Frobenius**: `F x ⌣ F y = F (x ⌣ y)`. -/
theorem adicConstantCup_frobenius [ConnectedSpace (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    (i j k : ℤ) (h : i + j = k) (x : ((WeilSheaf.adicConstant k₀ l Y).cohomology i).carrier)
    (y : ((WeilSheaf.adicConstant k₀ l Y).cohomology j).carrier) :
    adicConstantCup hfin hc i j k h (((WeilSheaf.adicConstant k₀ l Y).cohomology i).frobenius x)
        (((WeilSheaf.adicConstant k₀ l Y).cohomology j).frobenius y) =
      ((WeilSheaf.adicConstant k₀ l Y).cohomology k).frobenius
        (adicConstantCup hfin hc i j k h x y) := by
  by_cases hij : 0 ≤ i ∧ 0 ≤ j
  · rw [adicConstantCup_apply _ _ _ _ _ _ hij, adicConstantCup_apply _ _ _ _ _ _ hij,
      ← cohomologyCast_frobenius, cohomologyCast_frobenius, cohomologyCast_frobenius]
    congr 1
    rw [adicConstantCupNat_apply, adicConstantCupNat_apply, adicConstantHEquiv_symm_frobenius,
      adicConstantHEquiv_symm_frobenius, adicConstantCup_pullback]
    exact (exists_linearEquiv_adicConstantH_cohomology_adicConstantHPullback _).choose_spec _
  · simp [adicConstantCup, hij]

/-- **The cup product is graded commutative**: `y ⌣ x = (-1)^{ij} x ⌣ y`. -/
theorem adicConstantCup_comm (i j k : ℤ) (h : i + j = k)
    (x : ((WeilSheaf.adicConstant k₀ l Y).cohomology i).carrier)
    (y : ((WeilSheaf.adicConstant k₀ l Y).cohomology j).carrier) :
    adicConstantCup hfin hc j i k ((add_comm j i).trans h) y x =
      (i * j).negOnePow • adicConstantCup hfin hc i j k h x y := by
  by_cases hij : 0 ≤ i ∧ 0 ≤ j
  · rw [adicConstantCup_apply _ _ _ _ _ _ ⟨hij.2, hij.1⟩, adicConstantCup_apply _ _ _ _ _ _ hij,
      Units.smul_def, ← map_zsmul, adicConstantCupNat_apply, adicConstantCupNat_apply,
      ProEtale.adicConstantCup_comm hfin hc i.toNat j.toNat k.toNat (by omega), map_zsmul]
    congr 3
    simp [Int.toNat_of_nonneg hij.1, Int.toNat_of_nonneg hij.2]
  · have hji : ¬ (0 ≤ j ∧ 0 ≤ i) := fun h' ↦ hij ⟨h'.2, h'.1⟩
    simp [adicConstantCup, hij, hji]

end WeilSheaf

end AlgebraicGeometry
