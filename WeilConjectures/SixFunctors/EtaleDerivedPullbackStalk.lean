/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import WeilConjectures.AlgebraicGeometry.PointedEtaleStalk
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Derived inverse image and geometric stalks

Source: Stacks Project, `etale-cohomology.tex`, Tag 03Q1, clauses (1) and (3),
extended termwise and localized at quasi-isomorphisms.
(blueprint: lem-sf-etale-derived-pullback-stalk)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

attribute [local instance] CategoryTheory.GrothendieckTopology.Point.sheafFiber_additive

/-- The exact inverse image followed by an exact geometric module stalk is canonically
isomorphic to the stalk at the image geometric point on the unbounded derived categories.
The equation says that on every representing complex the derived isomorphism is the
localization of the degreewise canonical inverse-image stalk comparison. Its components
are morphisms of `A`-modules, hence additive and `A`-linear; the complex isomorphism and
its naturality encode compatibility with differentials and all morphisms of complexes.

Source: Stacks Project, Tag 03Q1, `lemma-stalk-pullback` (1), (3); Tag 015F,
`lemma-right-derived-exact-functor`; Tag 04VG, `lemma-properties-left-localization`.
(blueprint: lem-sf-etale-derived-pullback-stalk)

Proof:
1. Use the coefficient-category-valued `upperStarCompSheafFiberIso` directly for
`ModuleCat A`. Its components are already linear maps, and its naturality applies
both to differentials and to components of maps of complexes.
2. Apply `mapHomologicalComplexCompIso` to obtain the canonical comparison between
termwise inverse image followed by termwise stalk and termwise image-point stalk.
3. Whisker the exact-derived factorization of inverse image by the derived stalk,
then compose with the stalk's exact-derived factorization. Whisker the chain
comparison by the localization functor. This constructs an isomorphism from the
localization followed by the two derived functors to the termwise image-point stalk
followed by localization. Exactness and additivity are the existing instances for
sheaf inverse image and point fibers.
4. Apply `Localization.liftNatIso` with this isomorphism and the canonical lifting
of the image-point stalk. Its component formula, followed by cancellation of the
image-point stalk factorization and its inverse, is exactly the equation below.
The construction is natural on the entire unbounded derived category. -/
theorem exists_etaleDerivedPullbackStalkIso
    (A : Type (u + 1)) [CommRing A] {U T : Scheme.{u}} (f : U ⟶ T)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ U) :
    ∃ α : (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory ⋙
        (pointSmallEtale v).sheafFiber.mapDerivedCategory ≅
          (pointSmallEtale (v ≫ f)).sheafFiber.mapDerivedCategory,
      ∀ C : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
        α.hom.app (_root_.DerivedCategory.Q.obj C) ≫
            (pointSmallEtale (v ≫ f)).sheafFiber.mapDerivedCategoryFactors.hom.app C =
          (pointSmallEtale v).sheafFiber.mapDerivedCategory.map
              ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryFactors.hom.app C) ≫
            (pointSmallEtale v).sheafFiber.mapDerivedCategoryFactors.hom.app
              (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj C) ≫
            _root_.DerivedCategory.Q.map
              ((Functor.mapHomologicalComplexCompIso
                (upperStarCompSheafFiberIso (ModuleCat.{u + 1} A) f v)
                (ComplexShape.up ℤ)).hom.app C) := by
  let P := upperStar (ModuleCat.{u + 1} A) f
  let S := (pointSmallEtale v).sheafFiber (A := ModuleCat.{u + 1} A)
  let R := (pointSmallEtale (v ≫ f)).sheafFiber (A := ModuleCat.{u + 1} A)
  let e : _root_.DerivedCategory.Q ⋙ (P.mapDerivedCategory ⋙ S.mapDerivedCategory) ≅
      R.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ _root_.DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight P.mapDerivedCategoryFactors S.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ S.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso
          (upperStarCompSheafFiberIso (ModuleCat.{u + 1} A) f v)
          (ComplexShape.up ℤ)) _root_.DerivedCategory.Q
  refine ⟨Localization.liftNatIso _root_.DerivedCategory.Q
    (HomologicalComplex.quasiIso
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (ComplexShape.up ℤ))
    _ _ (P.mapDerivedCategory ⋙ S.mapDerivedCategory) R.mapDerivedCategory e, ?_⟩
  intro C
  simp [Localization.liftNatIso_hom, Localization.liftNatTrans_app,
    Localization.Lifting.iso, e, P, S, R]

end AlgebraicGeometry.Etale
