/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Sheaves.Abelian
import WeilConjectures.Topology.AbelianSheafShortExactStalkwise
import WeilConjectures.Topology.ClosedPushforwardAbelianStalks

/-!
# Exactness of closed-subset pushforward for abelian sheaves

## References

* Stacks Project, Tag 01AX.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace TopCat.Sheaf

/-- Pushforward along the inclusion of a closed subset preserves short exact sequences
of abelian sheaves. The existing `pushforward` evaluates on an open `U` by evaluating
on its inverse image in `Z`, namely `U ∩ Z` with the subspace topology. -/
theorem shortExact_map_pushforward_closedSubset
    (X : TopCat.{u}) (Z : Set X) (hZ : IsClosed Z)
    (S : ShortComplex ((TopCat.of Z).Sheaf AddCommGrpCat.{u}))
    (hS : S.ShortExact) :
    (S.map (pushforward AddCommGrpCat.{u}
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of Z ⟶ X))).ShortExact := by
  classical
  let i : TopCat.of Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  apply (shortExact_iff_stalkFunctor_map_shortExact _).mpr
  intro x
  by_cases hx : x ∈ Z
  · let z : TopCat.of Z := ⟨x, hx⟩
    let Φ := Sheaf.forget AddCommGrpCat X ⋙
      Presheaf.stalkFunctor (X := X) AddCommGrpCat.{u} x
    let Ψ := Sheaf.forget AddCommGrpCat (TopCat.of Z) ⋙
      Presheaf.stalkFunctor (X := TopCat.of Z) AddCommGrpCat.{u} z
    let c (F : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) :
        Φ.obj ((pushforward AddCommGrpCat i).obj F) ≅ Ψ.obj F := by
      have := (closedPushforwardAbelianStalks Z hZ F).2.1 z
      exact asIso (Presheaf.stalkPushforward AddCommGrpCat i F.obj z)
    let e : (S.map (pushforward AddCommGrpCat i)).map Φ ≅ S.map Ψ :=
      ShortComplex.isoMk (c S.X₁) (c S.X₂) (c S.X₃)
        ((closedPushforwardAbelianStalks Z hZ S.X₁).2.2 S.X₂ S.f z).symm
        ((closedPushforwardAbelianStalks Z hZ S.X₂).2.2 S.X₃ S.g z).symm
    exact ShortComplex.shortExact_of_iso e.symm
      ((shortExact_iff_stalkFunctor_map_shortExact S).mp hS z)
  · have hz (F : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) :=
      (closedPushforwardAbelianStalks Z hZ F).1 x hx
    refine ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_isZero_X₂ _ (hz S.X₂)) ?_ ?_
    · exact (hz S.X₁).mono _
    · exact (hz S.X₃).epi _

end TopCat.Sheaf
