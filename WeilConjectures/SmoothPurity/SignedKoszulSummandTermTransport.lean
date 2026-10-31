/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
public import WeilConjectures.ProEtaleCoefficients.RingedStrictTowerHomotopyLimit
public import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
public import Mathlib.Algebra.Homology.Double
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Transport of one signed Koszul summand

Source: Stacks Project, algebraization.tex, Tag 0A0E,
lemma-derived-completion-koszul, finite free tensor calculation.
(blueprint: lem-cbc-signed-koszul-summand-term-transport).

This isolates the scalar-action and equality-transport calculation for one erased
index. It is strictly smaller than the finite sum differential theorem.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u z
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CategoryTheory

section Scalars

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u})

private abbrev scalarModules :=
  SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)

set_option hygiene false in
local notation "E" => scalarModules O
set_option hygiene false in
local notation "S" => RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat)

attribute [local instance] SheafOfModules.monoidalCategory

set_option maxHeartbeats 600000 in
-- The transport compares the canonical sheaf tensor and Hom scalar instances.
end Scalars

attribute [local irreducible] ringedNegativeKoszul ringedNegativeKoszulBasis

end CategoryTheory
