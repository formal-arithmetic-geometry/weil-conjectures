/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T5
-/
module

public import Sheaf.SixFunctors.IntegralOpenReductionComparison
public import Sheaf.Paper.IntegralOperationsScalarComparisons

/-! # Strict completion comparisons for the two exact open functors -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Both exact open functors commute with the specified quotient completion, preserving
its actual unit and the pulled strict Roos coordinates.
Source: Stacks 099N (2),(5), 0941 and 09BN;
(blueprint: lem-sf-open-roos-functor-transport).

Proof: constant normalization and the completed projection identities identify restriction
of each quotient tensor with the quotient tensor of restriction. On a flat-term K-flat
representative these are the balanced tensor maps, commuting with every transition and
with x mapped to x tensor 1. Restriction is exact and preserves countable products.
Apply the normalized exact-product strict-limit comparison and descend through the good
representative localization; the augmentation equation gives the stated unit identity.
The same construction before identifying the restricted tensor tower gives c: its two
Roos coordinates are precisely scalarRoosMap, and its unit formula is the displayed
pulled augmentation. For extension, quasi-compactness gives preservation of countable
products. The simultaneous semilinear open tensor comparison on flat-term K-flat models
identifies extension of the quotient tower with the quotient tower of extension, including
all augmentations and transitions. Its exact-product strict-limit comparison descends to
sigma and gives the second unit identity. No completeness hypothesis or boundedness is
used in either construction; the empty open is covered by the same slice construction. -/
theorem openRoosFunctorTransport
    {V W : Scheme.{t}} (e : V ⟶ W) [IsOpenImmersion e] [QuasiCompact e]
    (o : IntegralOpenReduction.Operations l E e)
    (hfinite : ∀ n : ℕ, IsIso (o.finiteMap n)) (hcompleted : IsIso o.completedMap) :
    (∃ rho : IntegralOnSlice.completion l E W none ⋙ IntegralOpenReduction.star l E e o ≅
        IntegralOpenReduction.star l E e o ⋙ IntegralOnSlice.completion l E V none,
      (∀ H : IntegralOnSlice.D l E W none,
        (IntegralOpenReduction.star l E e o).map
          ((IntegralOnSlice.completionUnit l E W none).app H) ≫ rho.hom.app H =
        (IntegralOnSlice.completionUnit l E V none).app
          ((IntegralOpenReduction.star l E e o).obj H)) ∧
      ∃ c : IntegralOnSlice.qGood l E W none ⋙
          (IntegralOnSlice.completion l E W none ⋙ IntegralOpenReduction.star l E e o) ≅
        (IntegralOnSlice.Good l E W none).ι ⋙ IntegralOnSlice.tower l E W none ⋙
          (Functor.whiskeringRight ℕᵒᵖ _ _).obj
            ((IntegralOpenReduction.restriction l E e o).mapHomologicalComplex (.up ℤ)) ⋙
          integralOperationsRoosFunctor ⋙ DerivedCategory.Q,
        ∀ P : (IntegralOnSlice.Good l E W none).FullSubcategory,
          (IntegralOpenReduction.star l E e o).map
              ((IntegralOnSlice.completionUnit l E W none).app (DerivedCategory.Q.obj P.obj)) ≫
              c.hom.app P =
            (IntegralOpenReduction.restriction l E e o).mapDerivedCategoryFactors.hom.app P.obj ≫
              DerivedCategory.Q.map
                (((IntegralOpenReduction.restriction l E e o).mapHomologicalComplex (.up ℤ)).map
                  (IntegralOnSlice.roosUnit l E W none P.obj) ≫
                  scalarRoosMap (IntegralOpenReduction.restriction l E e o)
                    ((IntegralOnSlice.tower l E W none).obj P.obj))) ∧
    (∃ sigma : IntegralOnSlice.completion l E V none ⋙ IntegralOpenReduction.shriek l E e o ≅
        IntegralOpenReduction.shriek l E e o ⋙ IntegralOnSlice.completion l E W none,
      ∀ M : IntegralOnSlice.D l E V none,
        (IntegralOpenReduction.shriek l E e o).map
          ((IntegralOnSlice.completionUnit l E V none).app M) ≫ sigma.hom.app M =
        (IntegralOnSlice.completionUnit l E W none).app
          ((IntegralOpenReduction.shriek l E e o).obj M)) := by
  sorry

end WeilConjectures
