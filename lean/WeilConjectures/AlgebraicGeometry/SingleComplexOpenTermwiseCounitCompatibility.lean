/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenTensorRestrictionIso
import WeilConjectures.AlgebraicGeometry.OpenPinnedCounitHomotopyRestriction

/-! # Compatibility of open restriction with the pinned pullback counits

Source: Stacks Project, cohomology.tex, Tags 08HY, 08FE and 0D5S.
(blueprint: lem-pc-single-complex-open-counit-compatibility).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry
open SingleComplexBaseChange
set_option synthInstance.maxSize 2048

private theorem cancel_counit_factors
    {C : Type*} [Category C] {A B D E F G : C}
    (a : A ≅ B) (t : A ⟶ D) (e : D ⟶ E) (b : E ≅ F) (c : F ≅ G)
    (d : B ⟶ G) (h : t ≫ e ≫ b.hom ≫ c.hom = a.hom ≫ d) :
    a.inv ≫ t ≫ e = d ≫ c.inv ≫ b.inv := by
  have h' := congrArg (fun k => a.inv ≫ k ≫ c.inv ≫ b.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id, Category.id_comp, Category.comp_id] using h'

set_option maxHeartbeats 600000 in
-- Elaborating the exact restriction localization factors needs this budget.
/-- The derived open coefficient on an actual restricted complex is compatible
with ordinary tensor pullback and the pinned counits. This is an equality before
stalks and cohomology; it needs neither a base-change square nor K-flatness.

Proof: specialize `open_pinned_counit_homotopy_restriction` to the homotopy
quotient of P. Its source exact-restriction factor is the complex localization
factor: expand `mapDerivedCategoryFactorsh_hom_app` and cancel the identity
quotient comparison maps. Precompose the equation with the inverse of this
factor mapped by Lj*. Postcompose with the inverse localized homotopy tensor
restriction isomorphism, then with the inverse target exact-restriction factor.
Cancel the three pairs of inverse isomorphisms. The resulting target composite
is exactly `singleComplexOpenTensorRestrictionMap`; the source composite uses
the canonical inverse representative factor a. This works for every complex,
before stalks or cohomology, with no inversion of a pullback counit. Empty and
top opens and zero complexes use the same natural-transformation identities.

Source: Stacks Project, cohomology.tex, Tags 08HY, 08FE and 0D5S;
perfect.tex, Tag 0DJ9, first paragraph.
(blueprint: lem-pc-single-complex-open-counit-compatibility). -/
theorem singleComplexOpen_termwise_counit_compatibility
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ g')
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    letI : (schemeOpenRestriction X U).Additive := schemeOpenRestriction_additive X U
    letI : (schemeOpenRestriction X' U').Additive := schemeOpenRestriction_additive X' U'
    let K := DerivedCategory.Q.obj P
    let Q := ((schemeOpenRestriction X U).mapHomologicalComplex (.up ℤ)).obj P
    let a := (schemeOpenRestriction X U).mapDerivedCategoryFactors.symm.app P
    let θ := singleComplexRestrictedCoefficient g' K ((derivedPullback g').obj K) (𝟙 _)
      U U' j hj
    (derivedPullback j).map a.hom ≫ θ ≫
        (schemeOpenRestriction X' U').mapDerivedCategory.map
          ((counit g').app ((HomotopyCategory.quotient
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)).obj P)) =
      (counit j).app ((HomotopyCategory.quotient _ (.up ℤ)).obj Q) ≫
        singleComplexOpenTensorRestrictionMap g' U U' j hj P := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  have : ∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z),
      (Scheme.Modules.tensorPullback k).Additive := fun k => tensorPullbackAdditive k
  have h := open_pinned_counit_homotopy_restriction g' U U' j hj
    ((HomotopyCategory.quotient
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)).obj P)
  dsimp only [singleComplexOpenTensorRestrictionMap]
  have hf : (schemeOpenRestriction X U).mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)).obj P) =
      (schemeOpenRestriction X U).mapDerivedCategoryFactors.hom.app P := by
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    change (schemeOpenRestriction X U).mapDerivedCategory.map (𝟙 _) ≫
      (schemeOpenRestriction X U).mapDerivedCategoryFactors.hom.app P ≫
      𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) = _
    erw [(schemeOpenRestriction X U).mapDerivedCategory.map_id,
      DerivedCategory.Qh.map_id]
    simp only [Category.id_comp]
    exact Category.comp_id _
  rw [hf] at h
  have h' := cancel_counit_factors
    ((derivedPullback j).mapIso ((schemeOpenRestriction X U).mapDerivedCategoryFactors.app P))
    (singleComplexRestrictedCoefficient g' (DerivedCategory.Q.obj P)
      ((derivedPullback g').obj (DerivedCategory.Q.obj P)) (𝟙 _) U U' j hj)
    ((schemeOpenRestriction X' U').mapDerivedCategory.map
      ((counit g').app ((HomotopyCategory.quotient
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)).obj P)))
    ((schemeOpenRestriction X' U').mapDerivedCategoryFactorsh.app
      (((Scheme.Modules.tensorPullback g').mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)).obj P)))
    (DerivedCategory.Qh.mapIso
      ((openPinnedHomotopyTensorRestrictionIso g' U U' j hj).app
        ((HomotopyCategory.quotient
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)).obj P)))
    ((counit j).app ((HomotopyCategory.quotient _ (.up ℤ)).obj
      (((schemeOpenRestriction X U).mapHomologicalComplex (.up ℤ)).obj P)))
    (by
      change _ = _ at h
      exact h)
  simpa only [Functor.mapIso_inv, Iso.app_inv, Iso.symm_hom, Iso.app_hom] using h'

end AlgebraicGeometry
