/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M4
-/
module

public import Sheaf.CategoryTheory.LocalCoefficientLocalization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.CategoryTheory.SliceAwayLocalizationFreeResolution

/-! # The telescope presentation of the localized coefficient module

Source: Stacks Project, algebraization.tex, Tag 0997, displayed free resolution.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u}) (U : C) (f : R.obj.obj (op U))

/-- The countable free module used in the localization telescope (Stacks, Tag 0997). -/
abbrev localCoefficientFreeSum :=
  SheafOfModules.free (R := (localCoefficientRings R).over U) (ULift.{u} ℕ)

/-- The telescope map sends `e_n` to `e_n - f e_(n+1)` (Stacks, Tag 0997). -/
def localCoefficientTelescopeMap : localCoefficientFreeSum R U ⟶
    localCoefficientFreeSum R U :=
  Sigma.desc fun n : ULift.{u} ℕ ↦ SheafOfModules.ιFree n -
    localSectionMultiplication R U f (SheafOfModules.unit _) ≫
      SheafOfModules.ιFree (ULift.up (n.down + 1))

/-- The quotient map sends `e_n` to the `n`-th stage of the localization colimit. -/
def localCoefficientTelescopeQuotient : localCoefficientFreeSum R U ⟶
    localCoefficientLocalization R U f :=
  Sigma.desc fun n : ULift.{u} ℕ ↦ colimit.ι
    (Functor.ofSequence (X := fun _ : ℕ ↦ SheafOfModules.unit _)
      (fun _ ↦ localSectionMultiplication R U f _)) n.down

/-- Successive colimit structure maps annihilate the telescope relation.
Source: Stacks Project, Tag 0997, the displayed localization free resolution.
(blueprint: lem-weil-pbc-local-coefficient-telescope). -/
theorem localCoefficientTelescope_zero :
    localCoefficientTelescopeMap R U f ≫ localCoefficientTelescopeQuotient R U f = 0 := by
  apply Sigma.hom_ext
  intro n
  simp only [localCoefficientTelescopeMap, localCoefficientTelescopeQuotient,
    SheafOfModules.ιFree, Sigma.ι_desc_assoc, Preadditive.sub_comp, Category.assoc,
    Sigma.ι_desc, comp_zero]
  simpa only [Functor.ofSequence_map_homOfLE_succ] using sub_eq_zero.mpr (colimit.w
    (Functor.ofSequence (X := fun _ : ℕ ↦ SheafOfModules.unit _)
      (fun _ ↦ localSectionMultiplication R U f _))
    (homOfLE (Nat.le_succ n.down))).symm

/-- The canonical short complex presenting the coefficient localization. -/
def localCoefficientTelescope :
    ShortComplex (ringedSiteModules.{u} ((localCoefficientRings R).over U)) :=
  ShortComplex.mk (localCoefficientTelescopeMap R U f)
    (localCoefficientTelescopeQuotient R U f) (localCoefficientTelescope_zero R U f)

private def telescope_isCokernel : IsColimit
    (CokernelCofork.ofπ (localCoefficientTelescopeQuotient R U f)
      (localCoefficientTelescope_zero R U f)) := by
  let F := Functor.ofSequence (X := fun _ : ℕ ↦ SheafOfModules.unit _)
    (fun _ ↦ localSectionMultiplication R U f _)
  have hcompat {W : ringedSiteModules.{u} ((localCoefficientRings R).over U)}
      (g : localCoefficientFreeSum R U ⟶ W)
      (hg : localCoefficientTelescopeMap R U f ≫ g = 0) (n : ℕ) :
      localSectionMultiplication R U f (SheafOfModules.unit _) ≫
        SheafOfModules.ιFree (ULift.up (n + 1)) ≫ g =
          SheafOfModules.ιFree (ULift.up n) ≫ g := by
    have h := congrArg (fun k ↦ SheafOfModules.ιFree (ULift.up n) ≫ k) hg
    symm
    simpa only [localCoefficientTelescopeMap, SheafOfModules.ιFree, Sigma.ι_desc_assoc,
      Preadditive.sub_comp, Category.assoc, comp_zero, sub_eq_zero] using h
  let coc {W : ringedSiteModules.{u} ((localCoefficientRings R).over U)}
      (g : localCoefficientFreeSum R U ⟶ W)
      (hg : localCoefficientTelescopeMap R U f ≫ g = 0) : Cocone F :=
    ⟨W, NatTrans.ofSequence (fun n ↦ SheafOfModules.ιFree (ULift.up n) ≫ g)
      (fun n ↦ by simpa [F] using hcompat g hg n)⟩
  refine CokernelCofork.IsColimit.ofπ _ _ ?_ ?_ ?_
  · intro W g hg
    exact colimit.desc F (coc g hg)
  · intro W g hg
    apply Sigma.hom_ext
    intro n
    simp [localCoefficientTelescopeQuotient, coc, SheafOfModules.ιFree, F]
  · intro W g hg m hm
    apply colimit.hom_ext
    intro n
    have h := congrArg (fun k ↦ SheafOfModules.ιFree (ULift.up n) ≫ k) hm
    simpa [localCoefficientTelescopeQuotient, coc, SheafOfModules.ιFree, F] using h

/-- The canonical telescope of unit modules resolves the coefficient localization.

Source: Stacks Project, algebraization.tex, Tag 0997, displayed free resolution
(blueprint: lem-weil-pbc-local-coefficient-telescope).

Proof: The free resolution on the slice supplies a monic map whose formula on every
basis summand is `e_n - f e_(n+1)`. Coproduct extensionality identifies it with the map
constructed here. The sequential-colimit universal property identifies the canonical
quotient as its cokernel: a map annihilates the telescope map exactly when its basis
components form a compatible cocone. Hence the displayed short complex is short exact.
This does not require cancellation of f, and includes f=0 and the zero ring. -/
theorem localCoefficientTelescope_shortExact :
    (localCoefficientTelescope R U f).ShortExact := by
  obtain ⟨L, d, q, ⟨⟨hz, hseq⟩, hd, hq⟩⟩ :=
    sliceAwayLocalization_free_resolution R U f
  have heq : d = localCoefficientTelescopeMap R U f := by
    apply Sigma.hom_ext
    rintro ⟨n⟩
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    have hsub {M N : ringedSiteModules.{u} ((localCoefficientRings R).over U)}
        (a b : M ⟶ N) : (a - b).val = a.val - b.val :=
      (SheafOfModules.forget _).map_sub
    simp only [localCoefficientTelescopeMap, Sigma.ι_desc,
      hsub, SheafOfModules.comp_val, PresheafOfModules.sub_app,
      PresheafOfModules.comp_app, ModuleCat.hom_sub, ModuleCat.hom_comp,
      LinearMap.sub_apply, LinearMap.comp_apply, localSectionMultiplication]
    exact hd V n a
  have hm : Mono (localCoefficientTelescopeMap R U f) := heq ▸ hseq.mono_f
  have : Mono (localCoefficientTelescope R U f).f := hm
  exact ShortComplex.ShortExact.mk'
    ((localCoefficientTelescope R U f).exact_of_g_is_cokernel
      (telescope_isCokernel R U f)) inferInstance
    (epi_of_isColimit_cofork (telescope_isCokernel R U f))

end CategoryTheory
