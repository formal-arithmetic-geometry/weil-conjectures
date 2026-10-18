/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.Algebra.Module.FinitePresentation
import Sheaf.CategoryTheory.SiteConstantModuleHomInjective
import Sheaf.CategoryTheory.SiteConstantModuleHomSurjective
import Sheaf.CategoryTheory.SiteConstantModuleUnit
import Sheaf.CategoryTheory.LocalModuleHom
import Sheaf.Paper.SiteSheafificationSectionsLocal
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Internal Hom of constant module sheaves

Source: Stacks Project, Modules on Sites, Tag 093T (1), and Tag 0E8H
(blueprint: lem-pur-site-constant-module-hom).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type (max u v)) [CommRing Λ]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical identification of the constant ring sheaf with the underlying ring sheaf
of the constant commutative ring sheaf. Source: Stacks Tags 03CY and 093T
(blueprint: lem-pur-site-constant-module-hom). -/
def constantModuleHomRingIso :
    (constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ) ≅
      (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj
        ((constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of Λ)) :=
  letI : J.PreservesSheafification
      (forget₂ CommRingCat.{max u v} RingCat.{max u v}) :=
    GrothendieckTopology.instPreservesSheafification J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})
      (FD := fun A B : CommRingCat.{max u v} ↦ A →+* B)
      (CD := fun A : CommRingCat.{max u v} ↦ A)
      (FE := fun A B : RingCat.{max u v} ↦ A →+* B)
      (CE := fun A : RingCat.{max u v} ↦ A)
  (sheafComposeNatIso J (forget₂ CommRingCat.{max u v} RingCat.{max u v})
    (sheafificationAdjunction J CommRingCat.{max u v})
    (sheafificationAdjunction J RingCat.{max u v})).app
      ((Functor.const Cᵒᵖ).obj (CommRingCat.of Λ))

/-- The recorded constant-module functor, transported along the canonical ring isomorphism
so that the recorded internal Hom applies. Source: Stacks Tags 03CY and 093T
(blueprint: lem-pur-site-constant-module-hom). -/
def constantModuleHomFunctor :
    ModuleCat.{max u v} Λ ⥤ SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj
        ((constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of Λ))) :=
  siteConstantModuleFunctorGeneral J Λ ⋙
    SheafOfModules.pushforward (F := 𝟭 C) (constantModuleHomRingIso J Λ).inv

/-- The constant-section unit, retaining the underlying additive sheafification unit after
canonical coefficient transport. Source: Stacks Tags 03CY and 093T
(blueprint: lem-pur-site-constant-module-hom). -/
def constantModuleHomUnit (M : ModuleCat.{max u v} Λ) :
    (Functor.const Cᵒᵖ).obj ((forget₂ (ModuleCat Λ) AddCommGrpCat).obj M) ⟶
      ((constantModuleHomFunctor J Λ).obj M).val.presheaf :=
  toSheafify J ((siteConstantModulePresheafGeneral (C := C) Λ).obj M).presheaf

/-- The canonical Hom comparison for constant module sheaves, together with its naturality
and the same-map rule on each localized site.

Source: Stacks Project, Modules on Sites, Tag 093T (1), and Tag 0E8H
(blueprint: lem-pur-site-constant-module-hom).

Proof plan:
1. The local module Hom presheaf is a sheaf by lem-sf-local-module-hom-sheaf.
Send a constant linear map to its constant module sheaf map on each slice. The
sheafification unit formula proves additivity and compatibility with constant scalars.
2. A finite presentation implies finite generation, also in rank zero. Apply
lem-sf-constant-module-hom-locally-injective and
lem-sf-constant-module-hom-locally-surjective to the same constant-map comparison.
3. Apply lem-weil-pbc-site-sheafification-iso-locally-bijective and the universal
property of def-weil-pbc-sheafification. Since the local Hom is already a sheaf,
this gives the canonical additive comparison and its isomorphism assertion.
4. Use lem-sf-constant-module-unit-locally-bijective for local constant Hom sections,
lem-pc-sites-sheafification-underlying-sets and
lem-weil-pbc-site-sheafification-sections-local for local constant ring sections.
Refine both coverings, compute scalar compatibility on constants and use separatedness.
The inverse is linear by injectivity. Empty covering sieves give unique sections.
5. On constants the naturality square is functoriality applied to v f u. Local
constant representatives and separatedness extend it to all sections. For localization,
lem-weil-pbc-site-constant-restriction preserves the units and constant maps. The
recorded internal Hom and relocalization have the same slice morphisms and restrictions,
so both comparisons send a constant f to the same restricted sheaf map. -/
theorem siteConstantModule_hom
    (P Q : ModuleCat.{max u v} Λ) [Module.FinitePresentation Λ P] :
    ∃ comparison : ∀ M N : ModuleCat.{max u v} Λ,
      (constantModuleHomFunctor J Λ).obj (ModuleCat.of Λ (M →ₗ[Λ] N)) ⟶
        SheafOfModules.homObj (R := (constantSheaf J CommRingCat.{max u v}).obj
          (CommRingCat.of Λ))
          ((constantModuleHomFunctor J Λ).obj M) ((constantModuleHomFunctor J Λ).obj N),
      (∀ (M N : ModuleCat.{max u v} Λ) (U : Cᵒᵖ) (f : M →ₗ[Λ] N),
        (comparison M N).val.app U
            ((constantModuleHomUnit J Λ (ModuleCat.of Λ (M →ₗ[Λ] N))).app U f) =
          (PresheafOfModules.restrictOver
            ((constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of Λ)).obj U.unop).map
            (((constantModuleHomFunctor J Λ).map (ModuleCat.ofHom f)).val)) ∧
      IsIso (comparison P Q) ∧
      (∀ (M M' N N' : ModuleCat.{max u v} Λ) (a : M' ⟶ M) (b : N ⟶ N'),
        (constantModuleHomFunctor J Λ).map (ModuleCat.ofHom
          ((LinearMap.llcomp Λ M' N N' b.hom).comp (LinearMap.lcomp Λ N a.hom))) ≫
            comparison M' N' =
          comparison M N ≫ SheafOfModules.homObjMap
            (R := (constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of Λ))
            ((constantModuleHomFunctor J Λ).map a)
            ((constantModuleHomFunctor J Λ).map b)) ∧
      (∀ (U : C) (V : Over U) (f : P →ₗ[Λ] Q),
        (((comparison P Q).over U).val.app (op V)
          ((constantModuleHomUnit J Λ (ModuleCat.of Λ (P →ₗ[Λ] Q))).app (op V.left) f)).app
            (op (Over.mk (𝟙 V.left))) =
          (((constantModuleHomFunctor J Λ).map (ModuleCat.ofHom f)).over U).val.app (op V)) := by
  sorry

end CategoryTheory
