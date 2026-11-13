/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.Grp.Adjunctions

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-!
# Free resolutions from split étale hypercovers

The augmentation of the free abelian (or free module) sheaf on a split étale hypercover is a
quasi-isomorphism, and sections of an injective sheaf over a hypercover are acyclic in positive
degrees.
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.SplitEtaleHypercover

/-- The augmentation of the free abelian sheaf complex of a split étale hypercover is a
quasi-isomorphism. -/
theorem freeAbelian_augmentation_quasiIso
    {X : Scheme.{w}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : SplitEtaleHypercover X) :
    QuasiIso (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
      ((SimplicialObject.Augmented.whiskeringObj X.Etale _
        (uliftYoneda.{w + 1} ⋙
          (Functor.whiskeringRight X.Etaleᵒᵖ (Type (w + 1)) AddCommGrpCat.{w + 1}).obj
            AddCommGrpCat.free ⋙
          presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{w + 1})).obj
        (U.simplicial.augmentOfIsTerminal (terminalIsTerminal (C := X.Etale))))) := by
  sorry

/-- For an injective abelian sheaf `I`, sections over the zeroth stage of a split étale hypercover
form an exact augmented alternating coface complex: the augmentation is injective, its image is
the kernel of `d 0 1`, and the homology vanishes in positive degrees. -/
theorem injective_abelian_section_cohomology
    {X : Scheme.{w}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : SplitEtaleHypercover X)
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{w + 1}) [Injective I] :
    Function.Injective
        (I.obj.map (terminal.from
          (U.simplicial.obj (op (SimplexCategory.mk 0)))).op) ∧
      (∀ s : I.obj.obj (op (U.simplicial.obj (op (SimplexCategory.mk 0)))),
        ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{w + 1}).obj
          (U.simplicial.rightOp ⋙ I.obj)).d 0 1 s = 0 ↔
            s ∈ Set.range (I.obj.map (terminal.from
              (U.simplicial.obj (op (SimplexCategory.mk 0)))).op)) ∧
      ∀ p : ℕ, 0 < p → IsZero
        (((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{w + 1}).obj
          (U.simplicial.rightOp ⋙ I.obj)).homology p) := by
  sorry

/-- The augmentation of the free `R`-module sheaf complex of a split étale hypercover is a
quasi-isomorphism. -/
theorem freeModule_augmentation_quasiIso
    {X : Scheme.{w}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : SplitEtaleHypercover X) (R : Type (w + 1)) [CommRing R] :
    QuasiIso (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
      ((SimplicialObject.Augmented.whiskeringObj X.Etale _
        (uliftYoneda.{w + 1} ⋙
          (Functor.whiskeringRight X.Etaleᵒᵖ (Type (w + 1)) (ModuleCat.{w + 1} R)).obj
            (ModuleCat.free R) ⋙
          presheafToSheaf X.smallEtaleTopology (ModuleCat.{w + 1} R))).obj
        (U.simplicial.augmentOfIsTerminal (terminalIsTerminal (C := X.Etale))))) := by
  sorry

/-- For an injective sheaf `I` of `R`-modules, sections over the zeroth stage of a split étale
hypercover form an exact augmented alternating coface complex: the augmentation is injective, its
image is the kernel of `d 0 1`, and the homology vanishes in positive degrees. -/
theorem injective_module_section_cohomology
    {X : Scheme.{w}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : SplitEtaleHypercover X) (R : Type (w + 1)) [CommRing R]
    (I : Sheaf X.smallEtaleTopology (ModuleCat.{w + 1} R)) [Injective I] :
    Function.Injective
        (I.obj.map (terminal.from
          (U.simplicial.obj (op (SimplexCategory.mk 0)))).op) ∧
      (∀ s : I.obj.obj (op (U.simplicial.obj (op (SimplexCategory.mk 0)))),
        ((AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{w + 1} R)).obj
          (U.simplicial.rightOp ⋙ I.obj)).d 0 1 s = 0 ↔
            s ∈ Set.range (I.obj.map (terminal.from
              (U.simplicial.obj (op (SimplexCategory.mk 0)))).op)) ∧
      ∀ p : ℕ, 0 < p → IsZero
        (((AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{w + 1} R)).obj
          (U.simplicial.rightOp ⋙ I.obj)).homology p) := by
  sorry

end AlgebraicGeometry.SplitEtaleHypercover
