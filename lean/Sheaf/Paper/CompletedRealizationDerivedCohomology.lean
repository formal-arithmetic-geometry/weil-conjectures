/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Sheaf.Paper.IntegralStratifiedPerfectModels
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Normalized completed realization on unbounded derived categories

Source: Stacks Project, Modules on Sites, Tags 093J and 093M; Derived Categories,
Tag 015F; Bhatt--Scholze, Propositions 6.6.11 and 6.8.11(3)
(blueprint: lem-weil-pbc-completed-realization-derived-cohomology).

The realization is the existing `integralConstantModule`, including restriction along
`(pbcCompletedComparison T d).inv`. The comparisons below are actual constructions from
termwise localization and the kernel/image/cokernel comparison, without chosen witnesses.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The shift structure of the existing termwise derived realization.
Source: Stacks Tag 015F, with the identity-on-components shift comparison of Tag 014X
(blueprint: lem-weil-pbc-completed-realization-derived-cohomology). -/
instance integralConstantDerived_commShift (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (integralConstantDerived T d).CommShift ℤ := by
  dsimp only [integralConstantDerived]
  infer_instance

/-- Localization factorization of the termwise completed realization, with its canonical
normalization. Source: Stacks Tag 015F, parts (3)--(4)
(blueprint: lem-weil-pbc-completed-realization-derived-cohomology).
This is `mapDerivedCategoryFactors`, so its shift structure is the one descended from
identity maps on the terms of shifted complexes. -/
def integralRealizationFactors (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    completedConstantQ (ModuleCat.{u + 1} A) ⋙ integralConstantDerived T d ≅
      (integralConstantModule T d).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  letI := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
  letI := (integralConstantModule_exact T d).1
  letI := (integralConstantModule_exact T d).2
  (integralConstantModule T d).mapDerivedCategoryFactors

/-- The natural comparison F(H^q(P)) ≅ H^q(DF(P)) for every unbounded derived object.
Source: Stacks Tag 015F, using Homology Tag 010N
(blueprint: lem-weil-pbc-completed-realization-derived-cohomology).
`mapDerivedCategoryHomologyFunctorIso` descends the inverse of the canonical complex
homology comparison, followed by the inverse of the localization factorization. Thus
it preserves the cycle, boundary and quotient normalization, including the coefficient
transport already present in `integralConstantModule`. -/
def integralRealizationHomologyIso (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (q : ℤ) :
    @DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) _ _
        (HasDerivedCategory.standard (ModuleCat.{u + 1} A)) q ⋙
        integralConstantModule T d ≅
      integralConstantDerived T d ⋙
        DerivedCategory.homologyFunctor (pbcModules T (pbcAdicCompletion T d)) q :=
  letI := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
  letI := (integralConstantModule_exact T d).1
  letI := (integralConstantModule_exact T d).2
  (integralConstantModule T d).mapDerivedCategoryHomologyFunctorIso q

/-- The comparison DF(M[r]) ≅ F(M)[r], natural in arbitrary modules M, for all integer r.
Source: Stacks Tag 015F(4), with the termwise shift normalization of Tag 014X
(blueprint: lem-weil-pbc-completed-realization-derived-cohomology).
First use the localized identity-on-components shift comparison, then the degree-zero
single-complex comparison shifted by r. Its only potentially nonzero term is F(M) in
degree -r. No finite presentation or boundedness hypothesis is imposed on M. -/
def integralRealizationShiftedModuleIso (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (r : ℤ) :
    (@DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) _ _
        (HasDerivedCategory.standard (ModuleCat.{u + 1} A)) 0 ⋙
        shiftFunctor (completedConstantDerived (ModuleCat.{u + 1} A)) r) ⋙
        integralConstantDerived T d ≅
      integralConstantModule T d ⋙
        (DerivedCategory.singleFunctor (pbcModules T (pbcAdicCompletion T d)) 0 ⋙
          shiftFunctor (DerivedCategory (pbcModules T (pbcAdicCompletion T d))) r) :=
  letI := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
  letI := (integralConstantModule_exact T d).1
  letI := (integralConstantModule_exact T d).2
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0)
      ((integralConstantModule T d).mapDerivedCategory.commShiftIso r) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((integralConstantModule T d).mapDerivedCategorySingleFunctor 0)
      (shiftFunctor (DerivedCategory (pbcModules T (pbcAdicCompletion T d))) r) ≪≫
    Functor.associator _ _ _

/-- Exactness and triangulated descent of the normalized completed realization.
The natural comparisons are `integralRealizationHomologyIso` and
`integralRealizationShiftedModuleIso`, with `integralRealizationFactors` on complexes.
Source: Stacks Tags 093J, 093M and 015F; Bhatt--Scholze, Propositions 6.6.11 and 6.8.11(3)
(blueprint: lem-weil-pbc-completed-realization-derived-cohomology).

Proof: `integralConstantModule_exact` already gives preservation of finite limits
and finite colimits for the normalized realization, and `integralConstantModule_additive`
gives additivity. Install those instances and the standard derived category of modules.
The realization is definitionally the exact functor's `mapDerivedCategory`, which is
triangulated. Its factorization is definitionally `mapDerivedCategoryFactors`, whose
hom is compatible with the canonical shift structures. The homology and shifted-module
comparisons above use the same exact-functor construction. -/
theorem integralConstantRealization_exact_derived (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (integralConstantModule T d).Additive ∧
      PreservesFiniteLimits (integralConstantModule T d) ∧
      PreservesFiniteColimits (integralConstantModule T d) ∧
      (integralConstantDerived T d).IsTriangulated ∧
      NatTrans.CommShift (integralRealizationFactors T d).hom ℤ := by
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
  let := (integralConstantModule_exact T d).1
  let := (integralConstantModule_exact T d).2
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · dsimp only [integralConstantDerived]
    infer_instance
  · dsimp only [integralRealizationFactors]
    infer_instance

end AlgebraicGeometry.Scheme
