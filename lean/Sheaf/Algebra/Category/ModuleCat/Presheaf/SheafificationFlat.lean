/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat

/-!
# Sheafification preserves flatness of module presheaves

Source: Stacks Project, Modules on Sites, Lemma 18.28.3, Tag 03ET
(blueprint: lem-pc-sites-modules-sheafification-flat).
-/

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  {O : Cᵒᵖ ⥤ CommRingCat.{u}} {R : Sheaf J CommRingCat.{u}}

/-- Sheafification of a flat presheaf of modules is flat. The locally bijective map `α`
identifies the sheaf of rings underlying `R` with the associated sheaf of `O`; module
sheafification equips the associated abelian sheaf with its induced module structure.
Source: Stacks Project, Tag 03ET (blueprint: lem-pc-sites-modules-sheafification-flat).

Proof:
1. Module sheafification `a` and restriction `ι` preserve finite limits, as can be checked
on underlying abelian (pre)sheaves using the module sheafification interface
[lem-pc-sites-module-sheafification-interface], sectionwise limits
[lem-weil-pbc-module-sheaves-colimits-forgetful], and exact abelian sheafification
[lem-weil-pbc-sheafification-exact]. Thus `ι ⋙ tensorRight F ⋙ a` preserves finite limits.
2. The tensor/sheafification comparison [lem-pc-sites-module-sheafification-tensor]
identifies this composite with tensoring sheaves with `a(F)`, using the sheaf tensor
product [def-pur-sheaf-tensor-product].
3. Consequently that tensor functor preserves finite limits. It also preserves finite
colimits, being a left adjoint [lem-pc-sheaf-modules-tensor-closed]. Hence it is exact,
which is flatness [def-pc-flat-sheaf-modules]. -/
theorem isFlat_sheafification_obj
    (α : (O ⋙ forget₂ CommRingCat.{u} RingCat.{u}) ⟶
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    (F : PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (hF : PreservesFiniteLimits (tensorRight F)) :
    (letI := SheafOfModules.monoidalCategory R
     PreservesFiniteLimits (tensorRight ((sheafification α).obj F))) ∧
      SheafOfModules.IsFlat ((sheafification α).obj F) := by
  sorry

end PresheafOfModules
