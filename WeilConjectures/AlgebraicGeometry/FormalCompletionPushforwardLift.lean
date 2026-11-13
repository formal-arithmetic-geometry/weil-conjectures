/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import WeilConjectures.AlgebraicGeometry.FormalCompletionPushforwardLimitIso
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleLimitFull
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleLimitProjectionEpi
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Lifting compatible maps through the formal-functions comparison

## References

* Stacks Project, Tag 088B
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Any compatible map from a coherent adic system lifts through the canonical completed
proper pushforward comparison (Stacks, Tag 088B). -/
theorem formalCompletion_pushforward_lift {X Y : Scheme.{u}} [IsNoetherian Y]
    (J : Y.IdealSheafData) (f : X ⟶ Y) [IsProper f]
    (G : CoherentFormalModule Y J) (F : CoherentModules X)
    (h : RingedSpace.IsCoherent Y.toRingedSpace
      ((Scheme.Modules.pushforward f).obj F.obj))
    (κ : formalCompletionSystem J ((Scheme.Modules.pushforward f).obj F.obj) ⟶
      formalCompletionSystem (J.comap f) F.obj ⋙ Scheme.Modules.pushforward f)
    (hκ : ∀ n : ℕ,
      formalModuleQuotientπ J (n + 1) ((Scheme.Modules.pushforward f).obj F.obj) ≫
        κ.app (op n) = (Scheme.Modules.pushforward f).map
          (formalModuleQuotientπ (J.comap f) (n + 1) F.obj))
    (γ : G.obj ⟶ formalCompletionSystem (J.comap f) F.obj ⋙
      Scheme.Modules.pushforward f) :
    ∃ α : G ⟶ (completion Y J).obj
        ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩,
      α.hom ≫ κ = γ := by
  have : IsIso (lim.map κ) := formalCompletion_pushforward_limit_isIso J f F h κ hκ
  let H : CoherentFormalModule Y J :=
    (completion Y J).obj ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩
  let β : limit G.obj ⟶ limit H.obj := lim.map γ ≫ inv (lim.map κ)
  obtain ⟨α, hα⟩ := coherentFormalModule_limit_full J G H β
  refine ⟨α, ?_⟩
  have heq : lim.map (α.hom ≫ κ) = lim.map γ := by
    rw [Functor.map_comp, hα]
    simp [β]
  apply NatTrans.ext
  funext j
  obtain ⟨n⟩ := j
  have : Epi (limit.π G.obj (op n)) :=
    coherentFormalModule_limit_projection_epi J G n
  apply (cancel_epi (limit.π G.obj (op n))).1
  simpa only [lim_map, limMap_π] using
    congrArg (fun b ↦ b ≫ limit.π _ (op n)) heq

end AlgebraicGeometry
