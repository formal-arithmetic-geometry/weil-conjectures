/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived

import WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison
import Sheaf.CategoryTheory.StrictRoosComparison
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Sheaf.AlgebraicGeometry.ProEtaleContinuousCohomologyLimit
import Sheaf.CategoryTheory.RingedSiteModules

/-!
# Continuous etale cohomology

Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-prop-pe-continuous-cohomology-etale.md`; Bhatt--Scholze, Definition 5.6.1 and
Proposition 5.6.2 (blueprint: det-pe-continuous-cohomology-etale).

The continuous-sections complex is the termwise inverse limit of the section complexes.
Its right derived functor is specified by its universal property, without choosing a
resolution or a functorial cone in a triangulated category. Positive tower indices are
reindexed by `n + 1` throughout.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Apply continuous sections to a complex of strict towers of etale abelian sheaves.
In degree `q` this is `lim_n Γ(X, I_n^q) = Γ(X, lim_n I_n^q)`; limits of sheaves and
complexes are computed sectionwise and degreewise, respectively. This is a real functor
on strict complexes, prior to deriving it.
Source: Bhatt--Scholze, Definition 5.6.1; Stacks, Tag 0940
(blueprint: det-pe-continuous-cohomology-etale). -/
noncomputable def continuousEtaleSectionComplexes (X : Scheme.{u}) :
    CochainComplex (ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ ⥤
      CochainComplex AddCommGrpCat.{u + 1} ℤ :=
  HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
    (Functor.whiskeringRight ℕᵒᵖ
      (CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
      (CochainComplex AddCommGrpCat.{u + 1} ℤ)).obj
        ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
          (ComplexShape.up ℤ)) ⋙ lim

/-- The three isomorphisms identifying continuous etale cohomology. The functor `Rc`
and its unit are a total right derived functor of continuous sections, specified by
`IsRightDerivedFunctor`. The two middle objects are derived limits in the precise
Roos-triangle sense, with the original transitions, rather than unspecified cones.
Source: blueprint main-20261015, `sk-prop-pe-continuous-cohomology-etale.md`;
Bhatt--Scholze, Definition 5.6.1 and Proposition 5.6.2
(blueprint: det-pe-continuous-cohomology-etale).

Proof:
1. Realize towers as sheaves on the product of the small etale site with the ordered
positive integers (covers have constant index). Bounded-below injective resolutions
on this site give injective tower resolutions; exactness and evaluation are levelwise
(lem-weil-tower-category-levelwise-abelian, lem-sc-bounded-below-injective-resolution).
2. Levelwise sections have the exact left adjoint of levelwise constant sheaves, hence
preserve injectives (lem-sp-right-adjoint-preserves-injectives). Sections commute with
limits of sheaves. Thus continuous sections equal inverse limit of levelwise sections.
3. Evaluation has the exact finite-prefix left adjoint, so an injective tower resolution
is an injective resolution at every level. Apply lem-weil-pbc-right-derived-plus-injective
naturally in transitions to obtain a strict model for the derived section tower.
4. Applying continuous sections to this resolution and applying derived inverse limit
of its section tower give the same complex. The punctual integer-coefficient case of
lem-weil-pbc-ringed-strict-tower-homotopy-limit identifies it with a Roos derived limit.
Resolution comparison gives the right-derived universal property, also on unbounded
complexes by K-injective tower resolutions on the same small tower site.
5. Exact comparison inverse image transports the tower and its epimorphic transitions
(lem-pe-constant-left-module-inverse-image, with integer coefficients).
6. Resolve the pulled-back tower complex injectively on the pro-etale tower site. The
ordinary comparison unit followed by this resolution gives a strict map of section
towers. Each component is a quasi-isomorphism by sk-prop-sf-comparison with integer
coefficients and the injective computation of lem-weil-pbc-right-derived-plus-injective.
7. Derived inverse limit carries this strict quasi-isomorphism to an isomorphism.
By lem-weil-strict-roos-comparison and exact products of abelian groups the comparison
is represented by the map of strict Roos cones, so it uses the specified transitions.
8. Apply det-pe-continuous-cohomology-limit at the terminal pro-etale object: the pulled
back tower has epimorphic transitions. Its derived section limit is isomorphic to
derived sections of its ordinary limit. Uniqueness up to isomorphism of derived limits
(lem-weil-derived-limit-existence) supplies the final displayed isomorphism. -/
theorem continuousEtaleCohomology (X : Scheme.{u})
    [HasDerivedCategory.{w}
      (ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] :
    ∃ (_hproducts : HasCountableProducts (DerivedCategory.{u + 1} AddCommGrpCat.{u + 1}))
      (Rc : DerivedCategory.{w}
        (ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
          DerivedCategory.{u + 1} AddCommGrpCat.{u + 1})
      (η : continuousEtaleSectionComplexes X ⋙ DerivedCategory.Q ⟶
        DerivedCategory.Q ⋙ Rc),
      Rc.IsRightDerivedFunctor η
        (HomologicalComplex.quasiIso
          (ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ)) ∧
      ∀ (F : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
        (∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)) →
        ∃ (L₁ L₂ : DerivedCategory.{u + 1} AddCommGrpCat.{u + 1}),
          IsDerivedLimit
            (K := fun n : ℕ ↦
              (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctor.obj
                ((DerivedCategory.singleFunctor _ 0).obj (F.obj (op n))))
            (fun n : ℕ ↦
              (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctor.map
                ((DerivedCategory.singleFunctor _ 0).map
                  (F.map (homOfLE (Nat.le_succ n)).op))) L₁ ∧
          IsDerivedLimit
            (K := fun n : ℕ ↦
              (Sheaf.Γ (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).rightDerivedFunctor.obj
                ((DerivedCategory.singleFunctor _ 0).obj
                  ((comparisonUpperStar AddCommGrpCat.{u + 1} X).obj (F.obj (op n)))))
            (fun n : ℕ ↦
              (Sheaf.Γ (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).rightDerivedFunctor.map
                ((DerivedCategory.singleFunctor _ 0).map
                  ((comparisonUpperStar AddCommGrpCat.{u + 1} X).map
                    (F.map (homOfLE (Nat.le_succ n)).op)))) L₂ ∧
          Nonempty (Rc.obj ((DerivedCategory.singleFunctor _ 0).obj F) ≅ L₁) ∧
          Nonempty (L₁ ≅ L₂) ∧
          Nonempty (L₂ ≅
            (Sheaf.Γ (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).rightDerivedFunctor.obj
              ((DerivedCategory.singleFunctor _ 0).obj
                (limit (F ⋙ comparisonUpperStar AddCommGrpCat.{u + 1} X)))) := by
  sorry

end AlgebraicGeometry.ProEtale
