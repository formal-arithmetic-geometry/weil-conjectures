/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleMapIsoLocus
import Mathlib.CategoryTheory.Sites.LocalProperties

/-! # Pullback preserves local invertibility on the image

## References

* [Stacks, Tag 0097](https://stacks.math.columbia.edu/tag/0097)
* [Stacks, Tag 04TN](https://stacks.math.columbia.edu/tag/04TN)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

private theorem isIso_tensorPullback_iff_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (φ : M ⟶ N) :
    IsIso ((tensorPullback f).map φ) ↔ IsIso ((pullback f).map φ) := by
  obtain ⟨adj⟩ := nonempty_tensorPullbackAdjunction f
  exact NatIso.isIso_map_iff (adj.leftAdjointUniq (pullbackPushforwardAdjunction f)) φ

/-- Pulling a map back to a scheme whose image lies in its locally invertible open
produces an isomorphism. No finite generation assumption is needed (Stacks, Tags 0097
and 04TN). -/
theorem isIso_tensorPullback_of_range_subset_moduleMapIsoLocus {W T : Scheme.{u}}
    {M N : W.Modules} (φ : M ⟶ N) (h : T ⟶ W)
    (hh : Set.range h ⊆ (moduleMapIsoLocus φ : Set W)) :
    IsIso ((tensorPullback h).map φ) := by
  rw [isIso_tensorPullback_iff_pullback]
  let I := {U : W.Opens // IsIso ((tensorPullback U.ι).map φ)}
  let V : I → T.Opens := fun i ↦ h ⁻¹ᵁ i.1
  have hcover : ⨆ i, V i = ⊤ := by
    ext x
    change x ∈ (⨆ i, V i) ↔ x ∈ (⊤ : T.Opens)
    simp only [TopologicalSpace.Opens.mem_iSup, TopologicalSpace.Opens.mem_top, iff_true]
    obtain ⟨U, hU, hx⟩ := (mem_moduleMapIsoLocus φ (h x)).1 (hh ⟨x, rfl⟩)
    exact ⟨⟨U, hU⟩, hx⟩
  have hlocal (i : I) : IsIso (((pullback h).map φ).over (V i)) := by
    have : IsIso ((pullback i.1.ι).map φ) :=
      (isIso_tensorPullback_iff_pullback i.1.ι φ).1 i.2
    have e : pullback h ⋙ pullback (V i).ι ≅
        pullback i.1.ι ⋙ pullback (h ∣_ i.1) :=
      pullbackComp _ _ ≪≫ pullbackCongr (morphismRestrict_ι h i.1).symm ≪≫
        (pullbackComp _ _).symm
    have : IsIso ((pullback (V i).ι).map ((pullback h).map φ)) :=
      (NatIso.isIso_map_iff e φ).2
        (inferInstanceAs (IsIso ((pullback (h ∣_ i.1)).map ((pullback i.1.ι).map φ))))
    have : IsIso ((restrictFunctor (V i).ι).map ((pullback h).map φ)) :=
      (NatIso.isIso_map_iff (restrictFunctorIsoPullback (V i).ι) _).2 this
    have : IsIso ((overEquiv (V i)).functor.map (((pullback h).map φ).over (V i))) :=
      (NatIso.isIso_map_iff (overFunctorEquiv (V i)) _).2 this
    exact isIso_of_reflects_iso _ (overEquiv (V i)).functor
  have : IsIso ((SheafOfModules.toSheaf T.ringCatSheaf).map ((pullback h).map φ)) := by
    apply Sheaf.isIso_of_coversTop ((Opens.coversTop_iff T V).2
      (show TopologicalSpace.IsOpenCover V from hcover))
    intro i
    have := hlocal i
    change IsIso ((SheafOfModules.toSheaf (T.ringCatSheaf.over (V i))).map
      (((pullback h).map φ).over (V i)))
    infer_instance
  have : (SheafOfModules.toSheaf T.ringCatSheaf).ReflectsIsomorphisms := by
    infer_instance
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf T.ringCatSheaf)

end AlgebraicGeometry.Scheme.Modules
