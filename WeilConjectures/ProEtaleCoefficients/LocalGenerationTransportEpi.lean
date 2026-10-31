/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProEtaleCoefficients.LocalGenerationDefinitions
import WeilConjectures.ProEtaleCoefficients.LocalGenerationObjectComparisons

/-! # Transport of finite-free epimorphisms to the sectionwise localized module

The geometric comparison data is isolated in the two preceding modules.  This module
performs the resulting categorical epi transport.
(blueprint: lem-sfb-local-generation-transport-epi)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Transport the finite-free epimorphism through the comparison data.

The section functor preserves epimorphisms and the object-comparison isomorphisms
identify its two endpoints with the localized free sheaf and restricted constant module.
The composite of these isomorphisms with the image of `p` is therefore epi.
(blueprint: lem-sfb-local-generation-transport-epi)
-/
theorem localGenerationTransportEpi
    {Y Z W : Scheme.{u}} (g : Z ⟶ Y) (f : W ⟶ Z)
    [WeaklyEtale f] [WeaklyEtale (f ≫ g)]
    (B : Type (u + 1)) [CommRing B]
    (P : Type (u + 1)) [AddCommGroup P] [Module B P]
    (n : ℕ)
    (p : Mod.finiteFree
      ((upperStar AddCommGrpCat.{u + 1} f).obj
        ((upperStar AddCommGrpCat.{u + 1} g).obj
          (Sheaf.constRingSheaf (Scheme.ProEt.topology Y) B))) n ⟶
      ((upperStar AddCommGrpCat.{u + 1} f).mapMod
        ((upperStar AddCommGrpCat.{u + 1} g).obj
          (Sheaf.constRingSheaf (Scheme.ProEt.topology Y) B))).obj
        (((upperStar AddCommGrpCat.{u + 1} g).mapMod
          (Sheaf.constRingSheaf (Scheme.ProEt.topology Y) B)).obj
            (localGenerationConstantModule Y B P))) [Epi p] :
    ∃ q : SheafOfModules.free (R :=
        ((constantSheaf (Scheme.ProEt.topology Y) RingCat.{u + 1}).obj
          (RingCat.of B)).over (Scheme.ProEt.mk (f ≫ g)))
        (ULift.{u + 1} (Fin n)) ⟶
      localGenerationRestrictedModule Y (Scheme.ProEt.mk (f ≫ g)) B P,
      Epi q := by
  let F := localGenerationSectionFunctor g f B
  have : F.PreservesEpimorphisms :=
    localGenerationSectionFunctor_preservesEpimorphisms g f B
  let e₀ := localGenerationFiniteFreeComparison g f B n
  obtain ⟨e₁⟩ := localGenerationConstantModuleComparison g f B P
  let q := e₀.inv ≫ F.map p ≫ e₁.hom
  have hq : Epi q := by
    dsimp [q]
    infer_instance
  exact ⟨q, hq⟩

end AlgebraicGeometry.ProEtale
