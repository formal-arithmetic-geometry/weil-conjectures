/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebra
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraFreeComparison
public import WeilConjectures.CategoryTheory.ExactDerivedAdjunction

/-!
# Free algebras and right derived transports

Let `F`, `G` be additive autoequivalences of abelian categories `C`, `D` with exact coproducts
indexed by `ℤ`, `L : C ⥤ D` an additive functor and `e : L ⋙ G ≅ F ⋙ L`. The total right derived
functor `R(mapOfNatIso e)` of the transport of algebras is computed on underlying objects by `RL`
(`CategoryTheory.Endofunctor.IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso`). This file
shows that it commutes with the derived free algebra functors `D(Free)`, in the sense that the free
comparison `D(Free)(RL M) ⟶ R(mapOfNatIso e)(D(Free) M)` is an isomorphism, for `M = Q I` with `I`
K-injective, as soon as `L` preserves the coproducts `∐ₙ Fⁿ Iᵏ` and `RL` is computed by `L` on the
complex `∐ₙ Fⁿ I` (`CategoryTheory.Endofunctor.IsoAlgebra.isIso_freeComparison_rightDerivedFunctor`).

Indeed `D(Free)(RL (Q I)) ≅ Q(Free (L I)) ≅ Q(mapOfNatIso e (Free I)) ≅ R(mapOfNatIso e)(Q(Free I))`:
the first isomorphism since `I` is K-injective, the second is the free comparison of algebras
(`CategoryTheory.Endofunctor.IsoAlgebra.isIso_freeComparison_mapOfNatIso`), and the third since
the unit of `R(mapOfNatIso e)` at `Free I` is an isomorphism after forgetting.
-/

@[expose] public section

universe w w' v v' u u'

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] [Abelian C] {F : C ⥤ C} [F.Additive] [F.IsEquivalence]
  [HasColimitsOfShape (Discrete ℤ) C] [HasExactColimitsOfShape (Discrete ℤ) C]
  {D : Type u'} [Category.{v'} D] [Abelian D] {G : D ⥤ D} [G.Additive] [G.IsEquivalence]
  [HasColimitsOfShape (Discrete ℤ) D] [HasExactColimitsOfShape (Discrete ℤ) D]
  {L : C ⥤ D} [L.Additive] (e : L ⋙ G ≅ F ⋙ L)
  [HasDerivedCategory.{w} (IsoAlgebra F)] [HasDerivedCategory.{w'} (IsoAlgebra G)]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra F)]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra G)]
  [Abelian.HasKInjectiveResolutions C]

attribute [local instance] Functor.preservesFiniteLimits_of_preservesHomology
  Functor.preservesFiniteColimits_of_preservesHomology

/-- **Right derived transports commute with free algebras.** Let `I` be a K-injective complex
such that `L` preserves the coproducts `∐ₙ Fⁿ Iᵏ` and the unit of `RL` is an isomorphism at the
complex `∐ₙ Fⁿ I` underlying the free algebra on `I`. Then the free comparison
`D(Free)(RL (Q I)) ⟶ R(mapOfNatIso e)(D(Free) (Q I))` is an isomorphism. -/
theorem isIso_freeComparison_rightDerivedFunctor (I : CochainComplex C ℤ) [I.IsKInjective]
    [∀ k, PreservesColimit (Discrete.functor (Free.obj F (I.X k))) L]
    (hI : IsIso (L.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj
      (((Free.functor F ⋙ forget F).mapHomologicalComplex (.up ℤ)).obj I)))) :
    IsIso (Adjunction.freeComparison (Free.adjunction F).mapExactDerivedCategory
      (Free.adjunction G).mapExactDerivedCategory (mapOfNatIso e).rightDerivedFunctor
      L.rightDerivedFunctor (rightDerivedFunctorMapOfNatIsoCompForgetIso F e)
      (DerivedCategory.Q.obj I)) :=
  sorry

end CategoryTheory.Endofunctor.IsoAlgebra
