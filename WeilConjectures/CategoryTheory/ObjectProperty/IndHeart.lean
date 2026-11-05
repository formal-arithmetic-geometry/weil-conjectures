/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ColimCoyoneda
public import Mathlib.CategoryTheory.Comma.Final
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import WeilConjectures.CategoryTheory.DerivedCategory.CompactOfBoundedExt
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Ind-objects of a Serre-type subcategory

Let `C` be a Grothendieck abelian category and `P` a class of objects of `C` (the constructible
sheaves) containing zero and closed under kernels, cokernels and extensions, such that for `M`
in `P`, every morphism `M[0] ⟶ B[n]` in `D(C)` to a filtered colimit `B = colim Bᵢ` factors
through some `Bᵢ[n]` (`DerivedCategory.HomFactorsThroughFilteredColimits`). We show (blueprint
`sk-prop-ind-heart` (2)) that the ind-objects `ind P` are closed under kernels, cokernels,
extensions and direct sums
(`CategoryTheory.ObjectProperty.isClosedUnder_ind_of_homFactorsThroughFilteredColimits`):

* `det-ind-heart-full-faithfulness`: the objects of `P` are finitely presentable
  (`DerivedCategory.HomFactorsThroughFilteredColimits.isFinitelyPresentable`); injectivity of
  `colim Hom(M, Bᵢ) ⟶ Hom(M, colim Bᵢ)` comes from surjectivity applied to the kernels of
  `M ⟶ Bⱼ`;
* `det-ind-heart-canonical-presentation`: any presentation of an object of `ind P` is final in
  the category of morphisms from objects of `P`
  (`CategoryTheory.ObjectProperty.ColimitOfShape.final_toCostructuredArrow`), so that a morphism
  between objects of `ind P` is a filtered colimit of morphisms between objects of `P`
  (`CategoryTheory.ObjectProperty.exists_colimitOfShape_hom`);
* `det-ind-heart-kernels-cokernels`: filtered colimits being exact, kernels and cokernels are
  computed termwise (`CategoryTheory.ObjectProperty.ind_isClosedUnderKernels`,
  `CategoryTheory.ObjectProperty.ind_isClosedUnderCokernels`);
* `det-ind-heart-filtered-colimits`: `ind P` is closed under binary biproducts and, using
  `ind (ind P) = ind P`, under direct sums
  (`CategoryTheory.ObjectProperty.ind_isClosedUnderColimitsOfShape_discrete`);
* `det-ind-heart-extensions`: an extension of `B = colim Cₖ` by `N` is the filtered colimit of
  its pullbacks to the `Cₖ`; an extension of `C` in `P` by `N = colim Dᵢ` is, by the case
  `n = -1` of the factorization property applied to its class `C[0] ⟶ N[0][1]`, a pushout of an
  extension of `C` by some `Dᵢ` (`CategoryTheory.ObjectProperty.ind_isClosedUnderExtensions`).
-/

@[expose] public section

universe w v u

open CategoryTheory Category Limits

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

namespace HomFactorsThroughFilteredColimits

attribute [local instance] IsFiltered.isConnected

variable {X : C}
  (hX : DerivedCategory.HomFactorsThroughFilteredColimits.{w} ((singleFunctor C 0).obj X))
include hX

end HomFactorsThroughFilteredColimits

end DerivedCategory

namespace CategoryTheory.Limits.ColimitPresentation

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]

end CategoryTheory.Limits.ColimitPresentation

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

end CategoryTheory.ShortComplex

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] {P : ObjectProperty C}

section Abelian

variable [Abelian C] [IsGrothendieckAbelian.{w} C]

variable [HasDerivedCategory C]

end Abelian

end CategoryTheory.ObjectProperty
