/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
import WeilConjectures.AlgebraicGeometry.Modules.QcqsSections

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-!
# Quasi-coherence of pushforward along a qcqs morphism

## References

* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

private lemma section_extension_of_basicOpen_eq
    {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    {W O : X.Opens} (hW : IsCompact (W : Set X)) (hqs : IsQuasiSeparated (W : Set X))
    (a : Γ(X, W)) (hO : O = X.basicOpen a) (hle : O ≤ W) (s : Γ(F, O)) :
    ∃ (n : ℕ) (t : Γ(F, W)), F.presheaf.map (homOfLE hle).op t =
      X.presheaf.map (homOfLE hle).op a ^ n • s := by
  subst O
  exact exists_map_eq_pow_smul_of_isCompact_of_isQuasiSeparated F hW hqs a s

private lemma section_torsion_of_basicOpen_eq
    {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    {W O : X.Opens} (hW : IsCompact (W : Set X)) (a : Γ(X, W))
    (hO : O = X.basicOpen a) (hle : O ≤ W) (t : Γ(F, W))
    (ht : F.presheaf.map (homOfLE hle).op t = 0) : ∃ n : ℕ, a ^ n • t = 0 := by
  subst O
  exact exists_pow_smul_eq_zero_of_isCompact F hW a t ht

/-- Pushforward along a quasi-compact, quasi-separated morphism preserves quasi-coherence. -/
theorem isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] :
    ((pushforward f).obj F).IsQuasicoherent := by
  refine isQuasicoherent_of_forall_isAffineOpen _ (fun W hW a s ↦ ?_)
    (fun W hW a t ht ↦ ?_)
  · obtain ⟨n, t, ht⟩ := section_extension_of_basicOpen_eq F
      (f.isCompact_preimage hW.isCompact)
      (f.isQuasiSeparated_preimage hW.isQuasiSeparated) (f.app W a)
      (f.preimage_basicOpen a) (f.preimage_mono (S.basicOpen_le a)) s
    refine ⟨n, t, ht.trans ?_⟩
    have he : f.app (S.basicOpen a) (S.presheaf.map (homOfLE (S.basicOpen_le a)).op a) =
        X.presheaf.map (homOfLE (f.preimage_mono (S.basicOpen_le a))).op (f.app W a) := by
      rw [← ConcreteCategory.comp_apply, f.naturality]
      rfl
    rw [← he, ← map_pow]
    rfl
  · obtain ⟨n, hn⟩ := section_torsion_of_basicOpen_eq F
      (f.isCompact_preimage hW.isCompact) (f.app W a)
      (f.preimage_basicOpen a) (f.preimage_mono (S.basicOpen_le a)) t ht
    rw [← map_pow] at hn
    exact ⟨n, hn⟩

end AlgebraicGeometry.Scheme.Modules
