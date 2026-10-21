/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.CategoryTheory.RingedKoszulSystem
import Sheaf.CategoryTheory.RingedCechCompletionUnitIdempotence
import Sheaf.Paper.ExtendedCechCompletionModel

/-! # Unit cancellation into Cech-complete objects

Source: Stacks Project, algebraization.tex, Tag 099B.
(blueprint: lem-weil-pbc-ringed-cech-completion-hom-injective).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory



variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u}) (r : ℕ)
variable (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
variable [HasDerivedCategory.{w} (SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]

/-- Precomposition with the Cech completion unit distinguishes morphisms into a
Cech-completed object. Only injectivity, rather than the full reflector theorem,
is needed for uniqueness of the comparison and of its restriction maps.

Source: Stacks Project, algebraization.tex, Tag 099B.
(blueprint: lem-weil-pbc-ringed-cech-completion-hom-injective).

Proof: descend evaluation at one on functorial K-injective representatives to obtain
naturality of the actual completion unit. The idempotence theorem makes L(eta_E)
and eta_(L Y) invertible. If eta_E f = eta_E g, applying L and cancelling L(eta_E)
gives L(f) = L(g). Naturality gives f eta_(L Y) = eta_(L E) L(f) and the analogous
identity for g. Cancel the invertible eta_(L Y) to obtain f = g. No ideal subsheaf,
restriction comparison, or presentation of a Koszul limit is used. -/
theorem ringed_cech_completion_unit_hom_injective
    (E Y : ringedSiteDerived O) :
    Function.Injective
      (fun f : (ringedCechCompletionFunctor O (ringedExtendedCech O r b).1).obj E ⟶
          (ringedCechCompletionFunctor O (ringedExtendedCech O r b).1).obj Y ↦
        ringedCechCompletionUnit O (ringedExtendedCech O r b).1
          (ringedExtendedCech O r b).2 E ≫ f) := by
  let L := ringedCechCompletionFunctor O (ringedExtendedCech O r b).1
  let eta := ringedCechCompletionUnit O (ringedExtendedCech O r b).1
    (ringedExtendedCech O r b).2
  have hE : IsIso (L.map (eta E)) :=
    (ringed_cech_completion_unit_idempotence O r b E).1
  have hY : IsIso (eta (L.obj Y)) :=
    (ringed_cech_completion_unit_idempotence O r b Y).2
  intro f g hfg
  have hmap : L.map f = L.map g := by
    apply (cancel_epi (L.map (eta E))).mp
    simpa only [Functor.map_comp] using congrArg L.map hfg
  apply (cancel_mono (eta (L.obj Y))).mp
  have hf := completion_unit_natural O (ringedExtendedCech O r b).1
    (ringedExtendedCech O r b).2 _ _ f
  have hg := completion_unit_natural O (ringedExtendedCech O r b).1
    (ringedExtendedCech O r b).2 _ _ g
  change eta (L.obj E) ≫ L.map f = f ≫ eta (L.obj Y) at hf
  change eta (L.obj E) ≫ L.map g = g ≫ eta (L.obj Y) at hg
  rw [← hf, ← hg, hmap]

end CategoryTheory
