/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.NonvanishingCommonDegree
import WeilConjectures.AlgebraicGeometry.NonvanishingTransitionFunctions
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Separatedness from an ample invertible module

## References

* Stacks Project, Tag 09MP
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

universe u

private theorem separatingPair_of_basicOpen {X : Scheme.{u}} {U V : X.Opens}
    (hU : IsAffineOpen U) (f : Γ(X, U)) (g : Γ(X, V))
    (hbasic : U ⊓ V = X.basicOpen f)
    (hfg : (X.presheaf.map (homOfLE inf_le_left).op) f *
      (X.presheaf.map (homOfLE inf_le_right).op) g = 1) :
    IsAffineOpen (U ⊓ V) ∧ IsSeparatingPair X U V := by
  refine ⟨hbasic ▸ hU.basicOpen f, ?_⟩
  have hfrac_aux (W : X.Opens) (hWU : W ≤ U) (hb : W = X.basicOpen f)
      (v : Γ(X, W)) (hv : (X.presheaf.map (homOfLE hWU).op) f * v = 1)
      (z : Γ(X, W)) : ∃ (a : Γ(X, U)) (n : ℕ),
        z = (X.presheaf.map (homOfLE hWU).op) a * v ^ n := by
    subst W
    have := hU.isLocalization_basicOpen f
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj f z
    refine ⟨a, n, ?_⟩
    have ha' : z * ((X.presheaf.map (homOfLE hWU).op) f) ^ n =
        (X.presheaf.map (homOfLE hWU).op) a := ha
    calc
      z = z * (((X.presheaf.map (homOfLE hWU).op) f * v) ^ n) := by rw [hv]; simp
      _ = (z * ((X.presheaf.map (homOfLE hWU).op) f) ^ n) * v ^ n := by
        rw [mul_pow, mul_assoc]
      _ = _ := by rw [ha']
  have hfrac := hfrac_aux (U ⊓ V) inf_le_left hbasic
    ((X.presheaf.map (homOfLE inf_le_right).op) g) hfg
  unfold IsSeparatingPair
  apply top_unique
  intro z _
  obtain ⟨a, n, ha⟩ := hfrac ((U ⊓ V).topIso.hom z)
  have hz : z = (U ⊓ V).topIso.inv
      ((X.presheaf.map (homOfLE inf_le_left).op) a *
        ((X.presheaf.map (homOfLE inf_le_right).op) g) ^ n) := by
    rw [← ha, CommRingCat.inv_hom_apply]
  rw [hz, map_mul, map_pow]
  apply Subring.mul_mem
  · rw [← Scheme.homOfLE_appTop_topIso_inv inf_le_left]
    exact Subring.subset_closure (Set.mem_union_left _ ⟨U.topIso.inv a, by simp⟩)
  · apply Subring.pow_mem
    rw [← Scheme.homOfLE_appTop_topIso_inv inf_le_right]
    exact Subring.subset_closure (Set.mem_union_right _ ⟨V.topIso.inv g, by simp⟩)

/-- The affine nonvanishing loci of positive tensor-power sections covering a scheme
already imply separatedness; no quasi-compactness assumption is required
(Stacks, Tags 01PY and 09MP). -/
theorem isSeparated_of_affine_nonvanishing_cover (X : Scheme.{u}) (L : X.Modules)
    [L.IsInvertible]
    (hcover : ∀ x : X, ∃ n : ℕ, 0 < n ∧
      ∃ s : (L.tensorPow n).val.presheaf.obj (Opposite.op ⊤), ∃ U : X.Opens,
        x ∈ U ∧ IsAffineOpen U ∧ (U : Set X) = nonvanishingLocus (L.tensorPow n) s) :
    X.IsSeparated := by
  classical
  choose n hn s U hx hU hlocus using hcover
  have hcov : TopologicalSpace.IsOpenCover U := by
    change iSup U = ⊤
    apply top_unique
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  have hpairs (x y : X) :
      IsAffineOpen (U x ⊓ U y) ∧ IsSeparatingPair X (U x) (U y) := by
    obtain ⟨M, hM, s', t', hs, ht⟩ :=
      exists_common_degree_nonvanishing L (n x) (n y) (hn x) (hn y) (s x) (s y)
    have := hM
    obtain ⟨f, g, hbasic, hfg⟩ := exists_nonvanishing_transition_functions M s' t'
      (U x) (U y) ((hlocus x).trans hs.symm) ((hlocus y).trans ht.symm)
    exact separatingPair_of_basicOpen (hU x) f g hbasic hfg
  exact Scheme.isSeparated_of_isSeparatingPair U hcov hU
    (fun x y ↦ (hpairs x y).1) (fun x y ↦ (hpairs x y).2)

/-- A scheme carrying an ample invertible module is separated (Stacks, Tag 09MP). -/
theorem isSeparated_of_isAmple (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    (hL : L.IsAmple) : X.IsSeparated := by
  apply isSeparated_of_affine_nonvanishing_cover X L
  intro x
  obtain ⟨n, hn, s, U, hx, hU, hlocus⟩ := hL.2 x
  exact ⟨n, hn, s, U, hx, hU, Set.ext hlocus⟩


end AlgebraicGeometry
