/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Proetale.Sheafification
public import WeilConjectures.SixFunctors.Etale.SupportCohomology

/-!
# Cohomology with support

Source: the blueprint, `sec-smooth-purity/sk-def-purity-conv`,
`def-pur-support-cohomology` (blueprint: def-pur-support-cohomology).

## Main definitions

* `CategoryTheory.Sheaf.supportedSectionsFunctor`: kernel of restriction on sections.
* `AlgebraicGeometry.Etale.supportCohomology`: the natural-number derived functors.
* `AlgebraicGeometry.Etale.derivedSupportSections`: bounded-below derived sections.
* `AlgebraicGeometry.Etale.supportHypercohomology`: their integer-indexed cohomology.
* The same three constructions in `AlgebraicGeometry.ProEtale` use the small pro-etale site.

The constructions are defined for all abelian sheaves, hence in particular on the torsion
sheaves and bounded-below complexes with torsion cohomology of the node. On the pro-etale
site the coefficient category may be `ModuleCat Λ`, in particular for each finite-torsion
coefficient ring of the purity conventions. No twist is needed to define supported sections.
-/

@[expose] public section

universe v w c a u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
variable (A : Type a) [Category.{w} A] [Abelian A] {V W : C} (j : W ⟶ V)

attribute [instance] supportedSectionsFunctor_additive

end CategoryTheory.Sheaf

namespace AlgebraicGeometry

namespace Etale

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

end Etale

namespace ProEtale

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

variable (Λ : Type (u + 1)) [CommRing Λ]

end ProEtale
end AlgebraicGeometry
