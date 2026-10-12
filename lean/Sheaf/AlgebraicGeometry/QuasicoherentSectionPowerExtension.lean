/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.AlgebraicGeometry.QuasicoherentSectionPowerTorsion

/-! # Extending sections from a principal open of a qcqs open

Source: Stacks Project, Tag 01LC, localization of the finite section equalizer.
(blueprint: pqf-lem-qcoh-qcqs-section-power-extension).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- A section of a quasi-coherent module on `D(a)` inside a quasi-compact,
quasi-separated open extends to that open after multiplication by a power of `a`.
Source: Stacks Project, Tag 01LC, surjectivity of the localized section equalizer.
(blueprint: pqf-lem-qcoh-qcqs-section-power-extension).

Proof: choose a finite affine cover of the open. Affine localization extends the
given section after a power on each member; increasing to the maximum gives local
lifts with a common power. Their differences on the overlaps vanish on `D(a)`.
Each overlap is quasi-compact by quasi-separatedness, so the power-torsion lemma
kills each difference by a further power. A maximum over the finitely many pairs
therefore makes all local lifts compatible. Glue them by the sheaf axiom and check
on the principal-open cover that the glued section restricts to the original
section multiplied by the sum of the two chosen exponents. -/
theorem exists_map_eq_pow_smul_of_isCompact_of_isQuasiSeparated
    {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    {W : X.Opens} (hW : IsCompact (W : Set X)) (hqs : IsQuasiSeparated (W : Set X))
    (a : Γ(X, W)) (s₀ : Γ(F, X.basicOpen a)) :
    ∃ (n : ℕ) (t : Γ(F, W)),
      F.presheaf.map (homOfLE (X.basicOpen_le a)).op t =
        X.presheaf.map (homOfLE (X.basicOpen_le a)).op a ^ n • s₀ := by
  classical
  obtain ⟨s, hs, he⟩ :=
    isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp ⟨hW, W.isOpen⟩
  have he' : W = ⨆ i : s, (i.1 : X.Opens) := by
    ext1
    simpa using he
  let U : s → X.Opens := fun i ↦ i.1.1
  have hle (i : s) : U i ≤ W := by
    rw [he']
    exact le_iSup (fun i : s ↦ (i.1 : X.Opens)) i
  have := hs.to_subtype
  let := Fintype.ofFinite s
  let b (i : s) : Γ(X, U i) := X.presheaf.map (homOfLE (hle i)).op a
  have hD (i : s) : X.basicOpen (b i) = U i ⊓ X.basicOpen a := X.basicOpen_res _ _
  have hDle (i : s) : X.basicOpen (b i) ≤ X.basicOpen a := (hD i).le.trans inf_le_right
  have hlift (i : s) := exists_map_eq_pow_smul_of_isAffineOpen F i.1.2 (b i)
    (F.presheaf.map (homOfLE (hDle i)).op s₀)
  choose n t ht using hlift
  let N := Finset.univ.sup n
  have hn (i : s) : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
  let v (i : s) : Γ(F, U i) := b i ^ (N - n i) • t i
  have hv (i : s) :
      F.presheaf.map (homOfLE (X.basicOpen_le (b i))).op (v i) =
        X.presheaf.map (homOfLE ((X.basicOpen_le (b i)).trans (hle i))).op a ^ N •
          F.presheaf.map (homOfLE (hDle i)).op s₀ := by
    dsimp only [v]
    rw [map_smul, ht, map_pow, smul_smul, ← pow_add, Nat.sub_add_cancel (hn i)]
    simp only [b, ← Functor.map_comp_apply, ← op_comp, homOfLE_comp]
  have hv' (i : s) {V : X.Opens} (hV : V ≤ X.basicOpen (b i)) :
      F.presheaf.map (homOfLE (hV.trans (X.basicOpen_le (b i)))).op (v i) =
        X.presheaf.map (homOfLE (hV.trans ((X.basicOpen_le (b i)).trans (hle i)))).op a
          ^ N • F.presheaf.map (homOfLE (hV.trans (hDle i))).op s₀ := by
    have h := congrArg (F.presheaf.map (homOfLE hV).op) (hv i)
    simpa only [map_smul, map_pow, ← Functor.map_comp_apply, ← op_comp, homOfLE_comp] using h
  let c (i j : s) : Γ(X, U i ⊓ U j) :=
    X.presheaf.map (homOfLE (inf_le_left.trans (hle i))).op a
  let d (i j : s) : Γ(F, U i ⊓ U j) :=
    F.presheaf.map (homOfLE inf_le_left).op (v i) -
      F.presheaf.map (homOfLE inf_le_right).op (v j)
  have hzero (i j : s) :
      F.presheaf.map (homOfLE (X.basicOpen_le (c i j))).op (d i j) = 0 := by
    have hDi : X.basicOpen (c i j) ≤ X.basicOpen (b i) := by
      have hc : X.basicOpen (c i j) = (U i ⊓ U j) ⊓ X.basicOpen a :=
        X.basicOpen_res _ _
      rw [hD i]
      exact le_inf ((X.basicOpen_le (c i j)).trans inf_le_left)
        (hc.le.trans inf_le_right)
    have hDj : X.basicOpen (c i j) ≤ X.basicOpen (b j) := by
      have hc : X.basicOpen (c i j) = (U i ⊓ U j) ⊓ X.basicOpen a :=
        X.basicOpen_res _ _
      rw [hD j]
      exact le_inf ((X.basicOpen_le (c i j)).trans inf_le_right)
        (hc.le.trans inf_le_right)
    dsimp only [d]
    rw [map_sub]
    simp only [← Functor.map_comp_apply, ← op_comp, homOfLE_comp]
    rw [hv' i hDi, hv' j hDj, sub_self]
  have hkill (i j : s) := exists_pow_smul_eq_zero_of_isCompact F
    (hqs _ _ (hle i) (U i).isOpen i.1.2.isCompact
      (hle j) (U j).isOpen j.1.2.isCompact) (c i j) (d i j) (hzero i j)
  choose k hk using hkill
  let K := Finset.univ.sup fun p : s × s ↦ k p.1 p.2
  have hkK (i j : s) : k i j ≤ K :=
    Finset.le_sup (f := fun p : s × s ↦ k p.1 p.2) (Finset.mem_univ (i, j))
  have hkillK (i j : s) : c i j ^ K • d i j = 0 := by
    rw [← Nat.sub_add_cancel (hkK i j), pow_add, mul_smul, hk, smul_zero]
  let z (i : s) : Γ(F, U i) := b i ^ K • v i
  let G : TopCat.Sheaf AddCommGrpCat X := ⟨F.presheaf, F.isSheaf⟩
  have hcompat : TopCat.Presheaf.IsCompatible G.1 U z := by
    intro i j
    change F.presheaf.map (homOfLE inf_le_left).op (z i) =
      F.presheaf.map (homOfLE inf_le_right).op (z j)
    rw [← sub_eq_zero]
    dsimp only [z, b]
    simp only [map_smul, map_pow, ← Functor.map_comp_apply, ← op_comp, homOfLE_comp]
    exact (smul_sub (c i j ^ K) _ _).symm.trans (hkillK i j)
  obtain ⟨z₀, hz₀, -⟩ := G.existsUnique_gluing' U W (fun i ↦ homOfLE (hle i)) he'.le z hcompat
  refine ⟨K + N, z₀, ?_⟩
  apply G.eq_of_locally_eq' (fun i ↦ X.basicOpen (b i)) (X.basicOpen a)
    (fun i ↦ homOfLE (hDle i))
  · intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (he'.le (X.basicOpen_le a hx))
    exact Opens.mem_iSup.mpr ⟨i, (hD i).ge ⟨hi, hx⟩⟩
  · intro i
    change F.presheaf.map (homOfLE (hDle i)).op
        (F.presheaf.map (homOfLE (X.basicOpen_le a)).op z₀) =
      F.presheaf.map (homOfLE (hDle i)).op (_ ^ (K + N) • s₀)
    have hz : F.presheaf.map (homOfLE (hle i)).op z₀ = z i := hz₀ i
    rw [map_smul, map_pow]
    simp only [← Functor.map_comp_apply, ← op_comp, homOfLE_comp]
    have hz' := congrArg
      (F.presheaf.map (homOfLE (X.basicOpen_le (b i))).op) hz
    simp only [← Functor.map_comp_apply, ← op_comp, homOfLE_comp] at hz'
    rw [hz']
    dsimp only [z]
    rw [map_smul, map_pow, hv, smul_smul]
    simp only [b, ← Functor.map_comp_apply, ← op_comp, homOfLE_comp]
    rw [← pow_add]

end AlgebraicGeometry.Scheme.Modules
