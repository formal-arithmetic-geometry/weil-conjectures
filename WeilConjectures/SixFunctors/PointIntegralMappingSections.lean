/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralDualizingMappingTower

/-! # Point reconstruction for a variable constant-ring target tower

Source: prop-coef-integral-dualizing, second proof paragraph; Stacks 08J9 and 0941.
(blueprint: lem-coef-point-integral-mapping-sections).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped MonoidalClosed.FunctorCategory
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Point reconstruction compares internal Hom into an arbitrary constant-ring
sequence target with the closed Hom into its actual derived section tower.
The chosen small-Hom section model is accompanied by its actual comparison.
No reduction calculus, quotient target, or tensor unit occurs in this statement.

Source: prop-coef-integral-dualizing, second proof paragraph, scalar adjunction;
pointSectionsReconstruction and point_derived_hom_evaluation; Stacks 08J9, 0941.
(blueprint: lem-coef-point-integral-mapping-sections).

Proof: take the exact completed extension/point-sections adjunction. Its derived
counit is invertible on integral constructible inputs by point reconstruction.
Choose a flat-term K-flat complex P for the module input and one simultaneous
K-injective complex I for the target tower. Apply the explicit extension/sections
Hom-complex adjunction at every level: it sends a map to its value on 1 tensor p,
and its inverse sends b tensor p to b times the restricted value. These formulas
commute with all horizontal maps of I, and hence give a single isomorphism of
strict Hom complexes, not a lift from evaluated derived objects. The point Hom
comparison computes the left side; the closed tensor-Hom adjunction on module
towers computes the right side. The comparisons commute with chain maps in P
and I. Hom out of K-flat and into K-injective preserves the relevant
quasi-isomorphisms, so localization gives a bifunctorial comparison. Whisker its
input with the reconstruction counit, and change to the specified small-Hom
localization using its identity-on-complexes equivalence and the prescribed
section-model isomorphism e. Zero input and zero target give zero Hom complexes.
There is no boundedness condition on the target. -/
theorem point_integral_mapping_sections
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (Z : DerivedCategory (coefHomConstantModules l E (Spec (.of D.k))))
    (Y : integralDualizingSmallTower l E)
    (e : (coefHomConstantDerivedSections l E (Spec (.of D.k))).obj Z ≅
      (integralDualizingTowerEquivalence l E).functor.obj Y) :
    Nonempty ((sfIntegralConstructible l E (Spec (.of D.k))).ι.op ⋙
      (coefHomDerivedConstant l E (Spec (.of D.k))).op ⋙
      (Functor.curry.obj (coefHomConstantInternalHom l E (Spec (.of D.k)))).flip.obj Z ⋙
      coefHomConstantDerivedSections l E (Spec (.of D.k)) ≅
      ((sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙
        integralDualizingDerivedSections l E (Spec (.of D.k))).op ⋙
      (letI := HasDerivedCategory.ofIsGrothendieckAbelian (coefPairingModules l E)
       ((Functor.const ℕᵒᵖ : ModuleCat.{u + 1} (integralDualizingCoefficients l E) ⥤
         coefPairingModules l E).mapDerivedCategory).op ⋙
         MonoidalClosed.internalHom.flip.obj Y ⋙
           (integralDualizingTowerEquivalence l E).functor)) := by sorry

end WeilConjectures
