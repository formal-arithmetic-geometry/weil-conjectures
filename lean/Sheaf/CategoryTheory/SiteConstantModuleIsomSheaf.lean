/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.CategoryTheory.SiteConstantModuleFunctor
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Module.FinitePresentation
import Sheaf.CategoryTheory.SiteConstantModuleHomInjective
import Sheaf.CategoryTheory.SiteConstantModuleHomSurjective

/-!
# Isomorphisms between constant finitely presented module sheaves

Source: Stacks Project, Modules on Sites, Tag 093T, part (2)
(blueprint: lem-sf-site-constant-module-isom-sheaf).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace CategoryTheory

/-- The local module-isomorphism presheaf is a sheaf, and the canonical comparison from
constant module isomorphisms is an isomorphism. The equivalences `e` identify its sections
with actual isomorphisms on the slice site, and the first equation specifies restriction
by further localization. The final equation specifies the canonical map on constant sections.

Source: Stacks Project, Modules on Sites, Tag 093T, part (2)
(blueprint: lem-sf-site-constant-module-isom-sheaf).

Proof:
1. The additive local Hom presheaf is a sheaf by Mathlib. Its linear maps form a
locally defined subpresheaf, so local module Hom is a sheaf as well. Glue a local
isomorphism and its inverse there; separatedness gives both inverse identities.
2. The constant-module sheafification unit is locally bijective. If maps from a
finitely generated module induce equal local sheaf maps, local injectivity of this
unit gives equality on each generator on a covering sieve. Their finite intersection
is covering and forces equality of the module maps.
3. A finite presentation gives finitely many generators and finitely many relations.
Local surjectivity of the unit lifts the images of all generators on one common
cover. Local injectivity makes the finitely many relations zero on a further common
cover. Descend the resulting linear map through the presentation. A map out of a
constant module sheaf on a slice is determined on constant sections, so this lift
induces the given local sheaf map. This proves local surjectivity of the Hom comparison.
4. Lift an isomorphism's forward and backward maps using step 3. Step 2, applied to
both endomorphism modules, makes the two inverse identities hold on a further cover.
Thus the constant Isom comparison is locally bijective. Extend it to the constant
set sheaf using sheafification. A locally bijective morphism of sheaves is an
isomorphism; the sheafification factorization gives the required constant-section equation. -/
theorem siteConstantModule_isomSheaf
    {C : Type u} [SmallCategory C] (J : Precoverage C)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (Λ : Type u) [CommRing Λ] (M N : ModuleCat.{u} Λ)
    [Module.FinitePresentation Λ M] [Module.FinitePresentation Λ N] :
    ∃ I : Cᵒᵖ ⥤ Type u,
      ∃ e : ∀ U : Cᵒᵖ, I.obj U ≃
        (((siteConstantModuleFunctor J.toGrothendieck Λ).obj M).over U.unop ≅
          ((siteConstantModuleFunctor J.toGrothendieck Λ).obj N).over U.unop),
        (∀ (U V : Cᵒᵖ) (f : U ⟶ V) (x : I.obj U),
          e V (I.map f x) =
            ((SheafOfModules.overFunctorMap
              ((constantSheaf J.toGrothendieck RingCat.{u}).obj (RingCat.of Λ))
              f.unop).app ((siteConstantModuleFunctor J.toGrothendieck Λ).obj M)).symm ≪≫
            (SheafOfModules.overMap
              ((constantSheaf J.toGrothendieck RingCat.{u}).obj (RingCat.of Λ))
              f.unop).mapIso (e U x) ≪≫
            (SheafOfModules.overFunctorMap
              ((constantSheaf J.toGrothendieck RingCat.{u}).obj (RingCat.of Λ))
              f.unop).app ((siteConstantModuleFunctor J.toGrothendieck Λ).obj N)) ∧
        ∃ hI : Presheaf.IsSheaf J.toGrothendieck I,
          ∃ comparison : (constantSheaf J.toGrothendieck (Type u)).obj (M ≅ N) ≅ ⟨I, hI⟩,
            ∀ (U : Cᵒᵖ) (a : M ≅ N),
              e U (comparison.hom.hom.app U
                ((toSheafify J.toGrothendieck
                  ((Functor.const Cᵒᵖ).obj (M ≅ N))).app U a)) =
                (SheafOfModules.overFunctor
                  ((constantSheaf J.toGrothendieck RingCat.{u}).obj (RingCat.of Λ))
                  U.unop).mapIso
                    ((siteConstantModuleFunctor J.toGrothendieck Λ).mapIso a) := by
  classical
  let K := J.toGrothendieck
  let F := siteConstantModuleFunctor K Λ
  let I := SheafOfModules.localIso (F.obj M) (F.obj N)
  refine ⟨I, fun _ ↦ Equiv.refl _, ?_, ?_⟩
  · intro U V f x
    rfl
  · let hI := SheafOfModules.localIso_isSheaf (F.obj M) (F.obj N)
    refine ⟨hI, ?_⟩
    let : Presheaf.IsLocallyInjective K (SheafOfModules.constantLocalHom F M N) :=
      siteConstantModuleHom_locallyInjective K Λ M N
    let : Presheaf.IsLocallyInjective K (SheafOfModules.constantLocalHom F M M) :=
      siteConstantModuleHom_locallyInjective K Λ M M
    let : Presheaf.IsLocallyInjective K (SheafOfModules.constantLocalHom F N N) :=
      siteConstantModuleHom_locallyInjective K Λ N N
    let : Presheaf.IsLocallySurjective K (SheafOfModules.constantLocalHom F M N) :=
      siteConstantModuleHom_locallySurjective K Λ M N
    let : Presheaf.IsLocallySurjective K (SheafOfModules.constantLocalHom F N M) :=
      siteConstantModuleHom_locallySurjective K Λ N M
    let α := SheafOfModules.constantLocalIso F M N
    have hα := SheafOfModules.constantLocalIso_locallyBijective F M N
    let : Presheaf.IsLocallyInjective K α := hα.1
    let : Presheaf.IsLocallySurjective K α := hα.2
    let c : (constantSheaf K (Type u)).obj (M ≅ N) ⟶ ⟨I, hI⟩ :=
      ⟨sheafifyLift K α hI⟩
    have hc : toSheafify K ((Functor.const Cᵒᵖ).obj (M ≅ N)) ≫ c.hom = α :=
      toSheafify_sheafifyLift K α hI
    let : Presheaf.IsLocallyInjective K c.hom := by
      apply (Presheaf.comp_isLocallyInjective_iff K
        (toSheafify K ((Functor.const Cᵒᵖ).obj (M ≅ N))) c.hom).mp
      rw [hc]
      infer_instance
    let : Presheaf.IsLocallySurjective K c.hom := by
      apply (Presheaf.comp_isLocallySurjective_iff K
        (toSheafify K ((Functor.const Cᵒᵖ).obj (M ≅ N))) c.hom).mp
      rw [hc]
      infer_instance
    let : IsIso c := (Sheaf.isLocallyBijective_iff_isIso c).mp ⟨inferInstance, inferInstance⟩
    refine ⟨asIso c, ?_⟩
    intro U a
    exact ConcreteCategory.congr_hom (congr_app hc U) a

end CategoryTheory
