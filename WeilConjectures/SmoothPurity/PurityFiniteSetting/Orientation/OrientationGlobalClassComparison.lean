/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineOrientationData
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.OrientationGlobalClassEvaluation

/-! # Evaluation of ordinary Ext classes after site comparison

Source: the finite etale-origin transport in the affine-line purity proof.
(blueprint: lem-pur-orientation-global-class-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport

namespace WeilConjectures.PurityFiniteSetting

/-- The degree-one Ext section morphism commutes with exact site comparison.
This is an equality of module morphisms before evaluation at any element. The
single-complex and bounded-below/unbounded comparisons are included explicitly.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
thm-pur-affine-line-orientation.proof.md, finite etale-origin transport;
Stacks, Tag 099W, comparison of cohomology.
Proof: apply the defining unit equation of right-derived base change to the constant
sheaf in degree zero. Its H0 is the degree-zero augmentation, giving the first
factor on the left. Naturality with the Ext morphism transports this equality to
its target shifted by one. The shift equation
for derived base change identifies H0 of the shifted target with H1. Finally the
exact-functor single-object comparison identifies the image Ext morphism with
mapExactFunctor, and rightDerivedFunctorPlusCompatibility identifies bounded-below
and unbounded evaluation. The resulting equality is precisely the displayed
square of section morphisms; evaluation at one is a separate elementary step.
(blueprint: lem-pur-orientation-global-class-comparison). -/
theorem orientation_global_class_comparison (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) (F : Sheaf T.smallEtaleTopology (Modules P))
    (c : Abelian.Ext (P.constantEtale T) F 1) :
    (finiteComparisonSectionUnit T P.Coefficient (Scheme.Etale.mk (𝟙 T))).app
        (P.constantEtale T) ≫
      Abelian.Ext.coordinateSectionMap (globalSectionsFunctor (Modules P) T)
        (c.mapExactFunctor (comparisonUpperStar (Modules P) T)) =
    Abelian.Ext.coordinateSectionMap
      (Etale.sectionsFunctor (ModuleCat.{u + 1} P.Coefficient) T) c ≫
      (finiteComparisonSectionHypercohomology T P.Coefficient
        (Scheme.Etale.mk (𝟙 T)) 1).app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
      (Sheaf.sectionHypercohomologyFunctor (Scheme.ProEt.topology T) (Modules P)
        (Scheme.ProEt.mk (𝟙 T)) 1).map
          (((comparisonUpperStar (Modules P) T).mapDerivedCategoryPlusSingleFunctor
            0).hom.app F) := by
  let L := comparisonUpperStar (Modules P) T
  let E := Etale.sectionsFunctor (ModuleCat.{u + 1} P.Coefficient) T
  let E' := globalSectionsFunctor (Modules P) T
  let τ : E ⟶ L ⋙ E' := (Functor.rightUnitor E).inv ≫
    finiteComparisonSectionUnit T P.Coefficient (Scheme.Etale.mk (𝟙 T))
  have hh := Abelian.Ext.orientationGlobalClassMap_exact_naturality L E E' τ
    (𝟙 (L.obj (P.constantEtale T))) (𝟙 (L.obj F)) c (c.mapExactFunctor L) (by simp)
  simpa [L, E, E', τ, Functor.orientationGlobalClassTransport,
    finiteComparisonSectionHypercohomology, finiteComparisonSection,
    Sheaf.sectionHypercohomologyFunctor, Etale.sectionsFunctor, globalSectionsFunctor,
    AlgebraicGeometry.ProEtale.sectionsFunctor, Scheme.Etale.mk, Scheme.ProEt.mk,
    Modules, Functor.map_comp, Category.assoc] using hh.symm

end WeilConjectures.PurityFiniteSetting
