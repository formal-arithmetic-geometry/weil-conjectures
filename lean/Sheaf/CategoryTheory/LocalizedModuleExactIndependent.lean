/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Sheaf.Paper.RingedProjectionRestriction
public import Mathlib.CategoryTheory.Localization.Adjunction
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-!
# Exact localized module adjunction with independent site universes

Source: Stacks Project, Modules on Sites, Tags 03DI and 03DJ
(blueprint: lem-pur-site-restriction-module-adjunction-exact).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.ProjectionRestriction

namespace SheafOfModules

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u + 1}) (U : C)

/-- The existing direct-sum extension presheaf followed by module sheafification.
Source: Stacks 03DI (blueprint: lem-pur-site-restriction-module-adjunction-exact). -/
abbrev localizedModuleExtension :=
  extensionByZeroPresheaf.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) U ⋙
      PresheafOfModules.sheafification (𝟙 _)

/-- The existing sectionwise restriction to the slice ring.
Source: Stacks 03DJ (blueprint: lem-pur-site-restriction-module-adjunction-exact). -/
def localizedModuleRestriction :=
  overFunctor.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) U

/-- Both localized module functors are additive and exact at the original site universes.
Source: Stacks 03DI and 03DJ
(blueprint: lem-pur-site-restriction-module-adjunction-exact).
Proof:
1. By def-pur-localized-ringed-site, restriction keeps section modules, scalar actions,
   and restriction maps. Compose def-weil-extension-by-zero-presheaf with
   def-weil-presheaf-modules-sheafification to obtain the extension functor.
2. Construct the module Hom equivalence by composing with each direct-sum injection;
   its inverse uses DirectSum.toModule on the component linear maps. Check naturality
   and the inverse laws on summand generators. Compose with the sheafification Hom
   equivalence of lem-pc-sites-module-sheafification-interface to obtain the adjunction.
3. Forget a short exact complex to abelian sheaves using
   lem-weil-pbc-module-sheaves-colimits-forgetful. Restriction commutes with forgetting
   sectionwise, so lem-weil-pbc-site-restriction-exact applies. Reflect short exactness
   through the faithful exact module forgetful functor. Restriction is additive
   sectionwise; the abelian exactness criteria give both finite preservation clauses.
4. Direct-sum induction identifies extension followed by forgetting with the abelian
   extension presheaf. Use lem-pc-sites-module-sheafification-interface to sheafify this
   comparison. By lem-weil-pbc-site-extension-by-zero-presheaf-adjoint and uniqueness
   of left adjoints, the abelian extension is the constructed sheaf pullback. Transfer
   its additivity through the comparison and the faithful module forgetful functor.
   Apply lem-weil-pbc-site-extension-by-zero-exact, transport the short exact complex
   along the comparison, and reflect short exactness. The same abelian criteria give
   the extension's finite-limit and finite-colimit preservation. These comparisons
   retain the original site and coefficient universes throughout. -/
theorem localizedModuleExactIndependent :
    (localizedModuleExtension R U).Additive ∧
      PreservesFiniteLimits (localizedModuleExtension R U) ∧
      PreservesFiniteColimits (localizedModuleExtension R U) ∧
      (localizedModuleRestriction R U).Additive ∧
      PreservesFiniteLimits (localizedModuleRestriction R U) ∧
      PreservesFiniteColimits (localizedModuleRestriction R U) := sorry

/-- Additivity of extension. Source: Stacks 03DI
(blueprint: lem-pur-site-restriction-module-adjunction-exact). -/
instance localizedModuleExtension_additive : (localizedModuleExtension R U).Additive :=
  (localizedModuleExactIndependent R U).1

/-- Left exactness of extension. Source: Stacks 03DI
(blueprint: lem-pur-site-restriction-module-adjunction-exact). -/
instance localizedModuleExtension_limits :
    PreservesFiniteLimits (localizedModuleExtension R U) :=
  (localizedModuleExactIndependent R U).2.1

/-- Right exactness of extension. Source: Stacks 03DI
(blueprint: lem-pur-site-restriction-module-adjunction-exact). -/
instance localizedModuleExtension_colimits :
    PreservesFiniteColimits (localizedModuleExtension R U) :=
  (localizedModuleExactIndependent R U).2.2.1

/-- Additivity of restriction. Source: Stacks 03DJ
(blueprint: lem-pur-site-restriction-module-adjunction-exact). -/
instance localizedModuleRestriction_additive : (localizedModuleRestriction R U).Additive :=
  (localizedModuleExactIndependent R U).2.2.2.1

/-- Left exactness of restriction. Source: Stacks 03DJ
(blueprint: lem-pur-site-restriction-module-adjunction-exact). -/
instance localizedModuleRestriction_limits :
    PreservesFiniteLimits (localizedModuleRestriction R U) :=
  (localizedModuleExactIndependent R U).2.2.2.2.1

/-- Right exactness of restriction. Source: Stacks 03DJ
(blueprint: lem-pur-site-restriction-module-adjunction-exact). -/
instance localizedModuleRestriction_colimits :
    PreservesFiniteColimits (localizedModuleRestriction R U) :=
  (localizedModuleExactIndependent R U).2.2.2.2.2

open Classical in
/-- The canonical adjunction is fixed by insertion into the summand indexed by the
structure arrow, followed by the sheafification unit.
Source: Stacks 03DI (blueprint: lem-pur-site-restriction-module-adjunction-exact).
Proof: a map from the direct sum is a family of maps from its summands. Naturality
identifies this family with a map on the slice. Sheafification extends this bijection
to sheaves. Its unit is the displayed insertion, which determines the adjunction
uniquely since the summands generate the extension presheaf locally. -/
theorem localizedModuleAdjunctionIndependent_existsUnique :
    ∃! adj : localizedModuleExtension R U ⊣ localizedModuleRestriction R U,
      ∀ (M : Mod (R.over U)) (W : (Over U)ᵒᵖ) (m : M.val.obj W),
        (adj.unit.app M).val.app W m =
          ((PresheafOfModules.sheafificationAdjunction.{u + 1}
            (𝟙 ((sheafCompose J
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)).unit.app
            ((extensionByZeroPresheaf.{u + 1}
              ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) U).obj M)).app
                (op W.unop.left)
                  (DirectSum.lof (R.obj.obj (op W.unop.left)) (W.unop.left ⟶ U)
                    (fun a ↦ M.val.obj (op (Over.mk a))) W.unop.hom m) := sorry

/-- The uniquely normalized localized module adjunction.
Source: Stacks 03DI (blueprint: lem-pur-site-restriction-module-adjunction-exact). -/
def localizedModuleAdjunctionIndependent :
    localizedModuleExtension R U ⊣ localizedModuleRestriction R U :=
  Classical.choose (localizedModuleAdjunctionIndependent_existsUnique R U).exists

/-- Its termwise derived adjunction, obtained by localization at quasi-isomorphisms.
Source: Stacks 015F and 03DI
(blueprint: lem-pur-site-restriction-module-adjunction-exact). -/
def localizedModuleDerivedAdjunction :
    (localizedModuleExtension R U).mapDerivedCategory ⊣
      (localizedModuleRestriction R U).mapDerivedCategory :=
  letI : CatCommSq ((localizedModuleExtension R U).mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q
        (localizedModuleExtension R U).mapDerivedCategory :=
    ⟨(Functor.mapDerivedCategoryFactors _).symm⟩
  letI : CatCommSq ((localizedModuleRestriction R U).mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q
        (localizedModuleRestriction R U).mapDerivedCategory :=
    ⟨(Functor.mapDerivedCategoryFactors _).symm⟩
  ((localizedModuleAdjunctionIndependent R U).mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    (localizedModuleExtension R U).mapDerivedCategory
    (localizedModuleRestriction R U).mapDerivedCategory

end SheafOfModules
