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
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Sites.CoverLifting

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

Proof plan:
1. Glue local isomorphisms and their inverses sectionwise as linear maps on every object
of the slice. Uniqueness glues both inverse identities. This gives the sheaf condition.
2. For a finite free source, morphisms on each slice are determined by the images of its
basis. The module sheafification universal property and constant-restriction comparison
identify these with tuples of target sections. Exact abelian sheafification preserves
finite products, giving the constant-Hom comparison for a finite free source, including
rank zero (the empty tuple).
3. Choose a finite presentation of the source module. Sheafify its cokernel diagram and
restrict it to each slice using constant restriction. Maps from the cokernel are the
kernel of the map between finite free Hom sheaves. The ordinary module Hom is the same
kernel of the matrix map on tuples. Exact sheafification identifies these kernels, and
the comparisons respect composition and identity on constant sections and hence locally.
Apply this to both finitely presented modules and their endomorphisms.
4. Isomorphisms are mutually inverse pairs in the two Hom sheaves: the equalizer of
composition into the two endomorphism sheaves and the pair of identity sections. Set
sheafification preserves this finite-limit diagram. Compatibility of underlying sets
with algebraic sheafification identifies the equalizer with the constant sheaf of module
isomorphisms. Its map on constant sections is exactly constant module sheafification.
These are the four steps of the node, using the module sheafification interface, constant
restriction, exact abelian and set sheafification, and underlying-set compatibility. -/
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
  sorry

end CategoryTheory
