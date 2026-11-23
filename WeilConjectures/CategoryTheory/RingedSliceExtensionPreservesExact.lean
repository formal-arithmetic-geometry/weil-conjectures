/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExists

/-!
# Preservation of exactness by ringed-slice extension

Source: Stacks Project, Modules on Sites, Tag 0E8G.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

-- Direct sums of sectionwise injections remain injective (Stacks 03DJ).
private theorem extensionPresheaf_preservesMonomorphisms
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v}) (U : C) :
    (extensionByZeroPresheaf.{max u v} R U).PreservesMonomorphisms where
  preserves {F G} a ha := by
    classical
    apply PresheafOfModules.mono_of_injective
    intro V
    change Function.Injective (DirectSum.lmap (R := R.obj.obj V)
      (fun φ : V.unop ⟶ U ↦ (a.val.app (Opposite.op (Over.mk φ))).hom))
    apply (DirectSum.lmap_injective _).mpr
    intro φ
    apply (ModuleCat.mono_iff_injective _).mp
    exact (evaluation (R.over U) (Opposite.op (Over.mk φ))).map_mono a

/-- The sheafified direct-sum extension preserves exactness at the middle term.

Source: Stacks Project, Modules on Sites, Tags 03DI, 03DJ and 0E8G. -/
theorem ringedSliceExtension_preserves_exact
    {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{max u v}) (U : C)
    (S : ShortComplex (ringedSiteModules.{max u v} (((sheafCompose J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj O).over U)))
    (hS : S.Exact) :
    let R := (sheafCompose J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj O
    let L := extensionByZeroPresheaf.{max u v} R U ⋙
      PresheafOfModules.sheafification.{max u v} (𝟙 R.obj)
    imageSubobject (L.map S.f) = kernelSubobject (L.map S.g) := by
  let R := (sheafCompose J
    (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj O
  let L := extensionByZeroPresheaf.{max u v} R U ⋙
    PresheafOfModules.sheafification.{max u v} (𝟙 R.obj)
  have : (overFunctor.{max u v} R U).Additive := by
    constructor
    intro X Y f g
    ext V x
    rfl
  let adj := CategoryTheory.extensionSheafAdjunction R U
  have : L.Additive := adj.left_adjoint_additive
  have : PreservesColimitsOfSize.{0, 0} L := adj.leftAdjoint_preservesColimits
  have : PreservesFiniteColimits L := inferInstance
  have : (extensionByZeroPresheaf.{max u v} R U).PreservesMonomorphisms :=
    extensionPresheaf_preservesMonomorphisms R U
  have : L.PreservesMonomorphisms := inferInstance
  have hshort : ∀ T : ShortComplex (SheafOfModules.{max u v} (R.over U)),
      T.ShortExact → (T.map L).ShortExact := by
    intro T hT
    have : Mono T.f := hT.mono_f
    have : Mono (T.map L).f := L.map_mono T.f
    have hright : (T.map L).Exact ∧ Epi (T.map L).g :=
      (T.map L).exact_and_epi_g_iff_g_is_cokernel.mpr
        ⟨CokernelCofork.mapIsColimit _ hT.gIsCokernel L⟩
    have : Epi (T.map L).g := hright.2
    exact ⟨hright.1⟩
  have hex : ∀ T : ShortComplex (SheafOfModules.{max u v} (R.over U)),
      T.Exact → (T.map L).Exact := (L.exact_tfae.out 1 2).mp hshort
  exact (S.map L).exact_iff_image_eq_kernel.mp (hex S hS)

end SheafOfModules
