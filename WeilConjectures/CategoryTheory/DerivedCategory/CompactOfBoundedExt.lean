/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Constructions.Filtered
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfFiniteAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfHomologyProperty
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftComplete
public import WeilConjectures.CategoryTheory.Triangulated.CompactBoundedHom
public import WeilConjectures.CategoryTheory.Triangulated.CompactFamily
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.CoproductTriangle

/-!
# Compactness from a uniform Ext bound against a heart

Blueprints `sk-thm-constructible-compactness`, `sk-lem-finite-window` and
`det-prop-int-compactness-compact`, in the abstract form used there. Let `C` be an abelian
category with exact coproducts and exact countable products, and `P` a class of objects of `C`
closed under coproducts (the ind-constructible sheaves). Let `s` be an object of `D(C)` which is
bounded above (a constructible sheaf in degree `0`) such that

* `Hom(s, B[-n]) = 0` for `B` in `P` and `n` large (the uniform bound `Ext^q(s, B) = 0` for
  `q > d`), and
* `Hom(s, -[-n])` commutes with direct sums of objects of `P`.

Then `Hom(s, -)` commutes with direct sums of objects of `D(C)` with cohomology in `P`
(`DerivedCategory.compactFor_of_homologyProperty`).

The proof follows the blueprint: by induction on the amplitude, `s` is compact for uniformly
bounded families (`DerivedCategory.compactFor_of_isGE_of_isLE`); maps from `s` to an object
with cohomology in `P` in sufficiently negative degrees vanish, by induction on the amplitude for
bounded objects and by left completeness of `D(C)` in general
(`DerivedCategory.eq_zero_of_isLE`); hence morphisms out of `s` only see a finite window of
degrees, on which the bounded case applies.
-/

@[expose] public section

universe w

open CategoryTheory Category Limits Pretriangulated Preadditive

namespace CategoryTheory

namespace CompactFor

section Preadditive

variable {C : Type*} [Category* C] [Preadditive C]

end Preadditive

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

end CompactFor

end CategoryTheory

namespace DerivedCategory

open TStructure (t)

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions C] {J : Type*} [HasColimitsOfShape (Discrete J) C]
  [HasExactColimitsOfShape (Discrete J) C] {P : ObjectProperty C} [P.ContainsZero]
  [P.IsClosedUnderIsomorphisms]

section LeftComplete

variable [HasLimitsOfShape (Discrete ℕ) C] [HasExactLimitsOfShape (Discrete ℕ) C]

end LeftComplete

section Continuity

/-! ### Continuity of `Hom(s, -[n])` on objects of `C` -/

end Continuity

end DerivedCategory
