/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Power torsion for sections on a quasi-compact open

Source: Stacks Project, Tag 01LC, localization of the finite section equalizer;
Mathlib's structure-sheaf proof in Morphisms.QuasiCompact.
(blueprint: pqf-lem-qcoh-compact-section-power-torsion).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- A section of a quasi-coherent module on a quasi-compact open which vanishes on
`D(a)` is killed by a power of `a`.
Source: Stacks Project, Tag 01LC, injectivity of the localized section equalizer.
(blueprint: pqf-lem-qcoh-compact-section-power-torsion).

Proof: cover the quasi-compact open by finitely many affine opens. On each member,
the affine localization theorem kills the restricted section by some power of the
restricted function. Take the maximum of the finitely many powers. Its product with
the original section restricts to zero on every member, hence is zero by the sheaf
uniqueness axiom. No quasi-separatedness is needed for this half of localization. -/
theorem exists_pow_smul_eq_zero_of_isCompact
    {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    {W : X.Opens} (hW : IsCompact (W : Set X)) (a : Γ(X, W)) (t : Γ(F, W))
    (ht : F.presheaf.map (homOfLE (X.basicOpen_le a)).op t = 0) :
    ∃ n : ℕ, a ^ n • t = 0 := by
  classical
  obtain ⟨s, hs, he⟩ :=
    isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp ⟨hW, W.isOpen⟩
  have he' : W = ⨆ i : s, (i.1 : X.Opens) := by
    ext1
    simpa using he
  have hle (i : s) : (i.1 : X.Opens) ≤ W := by
    rw [he']
    exact le_iSup (fun i : s ↦ (i.1 : X.Opens)) i
  have hzero (i : s) :
      F.presheaf.map
        (homOfLE (X.basicOpen_le (X.presheaf.map (homOfLE (hle i)).op a))).op
        (F.presheaf.map (homOfLE (hle i)).op t) = 0 := by
    have hD : X.basicOpen (X.presheaf.map (homOfLE (hle i)).op a) ≤ X.basicOpen a := by
      rw [X.basicOpen_res]
      exact inf_le_right
    have h := congrArg (F.presheaf.map (homOfLE hD).op) ht
    rw [map_zero] at h
    simpa only [← Functor.map_comp_apply, ← op_comp, homOfLE_comp] using h
  have hlocal (i : s) := exists_pow_smul_eq_zero_of_isAffineOpen F i.1.2
    (X.presheaf.map (homOfLE (hle i)).op a)
    (F.presheaf.map (homOfLE (hle i)).op t) (hzero i)
  choose n hn using hlocal
  have := hs.to_subtype
  let := Fintype.ofFinite s
  refine ⟨Finset.univ.sup n, ?_⟩
  let G : TopCat.Sheaf AddCommGrpCat X := ⟨F.presheaf, F.isSheaf⟩
  apply G.eq_of_locally_eq' (fun i : s ↦ (i.1 : X.Opens)) W
    (fun i ↦ homOfLE (hle i)) he'.le
  intro i
  change F.presheaf.map (homOfLE (hle i)).op _ =
    F.presheaf.map (homOfLE (hle i)).op (0 : Γ(F, W))
  rw [map_zero, map_smul, map_pow]
  rw [← Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ i) : n i ≤ Finset.univ.sup n),
    pow_add, mul_smul, hn, smul_zero]

end AlgebraicGeometry.Scheme.Modules
