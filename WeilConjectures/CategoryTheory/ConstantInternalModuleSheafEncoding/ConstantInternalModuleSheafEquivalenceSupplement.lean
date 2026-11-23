/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.CategoryTheory.RingObjects.Ab
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.AlgebraicGeometry.ConstantInternalModuleSheafEquivalence

/-! # Encoding internal modules over a constant ring sheaf

Source: Bhatt--Scholze, Section 5.3, and Stacks Project, Tag 093I.
-/

@[expose] public section

universe u v w

open CategoryTheory MonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj

namespace CategoryTheory

namespace ConstantInternalModuleSheafEncoding

section PresheafEncoding

variable {C : Type u} [Category.{v} C] (R : Type w) [Ring R]

end PresheafEncoding

section ModuleLocalization

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J Ab.{w}] [(J.W (A := Ab.{w})).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

variable (A : Cᵒᵖ ⥤ Ab.{w}) [MonObj A]

end ModuleLocalization

section SheafEncoding

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J Ab.{w}] [(J.W (A := Ab.{w})).IsMonoidal]
  (R : Type w) [Ring R]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

variable (G : CategoryTheory.Mod Ab.{w} (AddCommGrpCat.of R) ⥤ ModuleCat.{w} R) [G.IsEquivalence]
    (hG : G ⋙ forget₂ (ModuleCat.{w} R) Ab.{w} = CategoryTheory.Mod.forget (AddCommGrpCat.of R))
    [J.HasSheafCompose (forget₂ (ModuleCat.{w} R) Ab.{w})]
    [HasLimitsOfSize.{v, u} (ModuleCat.{w} R)]
    [PreservesLimitsOfSize.{v, u} (forget₂ (ModuleCat.{w} R) Ab.{w})]
    [ReflectsLimitsOfSize.{v, u} (forget₂ (ModuleCat.{w} R) Ab.{w})]

/-- The sectionwise encoding leaves the underlying abelian sheaf unchanged. -/
noncomputable def sheafEncodingForgetIso :
    sheafEncoding J R G hG ⋙ sheafCompose J (forget₂ (ModuleCat.{w} R) Ab.{w}) ≅
      CategoryTheory.Mod.forget _ := by
  let U := sheafToPresheaf J Ab.{w}
  let e : (sheafEncoding J R G hG ⋙
      sheafCompose J (forget₂ (ModuleCat.{w} R) Ab.{w})) ⋙ U ≅
      CategoryTheory.Mod.forget ((presheafToSheaf J Ab.{w}).obj (A (C := Cᵒᵖ) R)) ⋙ U :=
    eqToIso (congrArg (fun P ↦ moduleLocalizationRight J (A (C := Cᵒᵖ) R) ⋙ P)
      (modulePresheafEncoding_forget (C := C) R G hG))
  exact ((Functor.FullyFaithful.ofFullyFaithful U).whiskeringRight _).preimageIso e

end SheafEncoding

end ConstantInternalModuleSheafEncoding

section SheafEncoding

open ConstantInternalModuleSheafEncoding

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J Ab.{w}] [(J.W (A := Ab.{w})).IsMonoidal]
  (R : Type w) [Ring R]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} R) Ab.{w})]
  [HasLimitsOfSize.{v, u} (ModuleCat.{w} R)]
  [PreservesLimitsOfSize.{v, u} (forget₂ (ModuleCat.{w} R) Ab.{w})]
  [ReflectsLimitsOfSize.{v, u} (forget₂ (ModuleCat.{w} R) Ab.{w})]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

/-- Internal modules over the sheafified constant ring are module-valued sheaves,
compatibly with the underlying abelian sheaves.

Source: Bhatt--Scholze, Section 5.3, and Stacks Project, Tag 093I.
-/
theorem constantInternalModuleSheaf_equivalence :
    ∃ F : CategoryTheory.Mod (Sheaf J Ab.{w}) (Sheaf.sheafifyRingPresheaf J
          ((Functor.const Cᵒᵖ).obj (RingCat.of R))) ⥤ Sheaf J (ModuleCat.{w} R),
      F.IsEquivalence ∧ Nonempty (F ⋙
        sheafCompose J (forget₂ (ModuleCat.{w} R) Ab.{w}) ≅ CategoryTheory.Mod.forget _) := by
  obtain ⟨G, hG, hforget⟩ := internalModuleAb_equivalence R
  have : G.IsEquivalence := hG
  let H := sheafEncoding J R G hforget
  have : H.Full := sheafEncodingFull J R G hforget
  have : H.Faithful := sheafEncodingFaithful J R G hforget
  have : H.EssSurj := sheafEncodingEssSurj J R G hforget
  have : H.IsEquivalence := {}
  refine ⟨H, inferInstance, ⟨?_⟩⟩
  let U := sheafToPresheaf J Ab.{w}
  let e : (H ⋙ sheafCompose J (forget₂ (ModuleCat.{w} R) Ab.{w})) ⋙ U ≅
      CategoryTheory.Mod.forget ((presheafToSheaf J Ab.{w}).obj (A (C := Cᵒᵖ) R)) ⋙ U :=
    eqToIso (congrArg (fun P ↦ moduleLocalizationRight J (A (C := Cᵒᵖ) R) ⋙ P)
      (modulePresheafEncoding_forget (C := C) R G hforget))
  exact ((Functor.FullyFaithful.ofFullyFaithful U).whiskeringRight _).preimageIso e

end SheafEncoding

end CategoryTheory
