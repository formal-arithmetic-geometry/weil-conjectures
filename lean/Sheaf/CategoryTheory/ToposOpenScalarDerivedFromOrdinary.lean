/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Sheaf.CategoryTheory.Sites.GrothendieckTopos
public import Sheaf.CategoryTheory.RingedSheafSliceAdjunction
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.CategoryTheory.RingedPresentationData
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.SixFunctors.OpenTensorNormalizationData
public import Mathlib.CategoryTheory.Subterminal

public import Sheaf.CategoryTheory.ToposOpenScalarBasic

/-! # Derived lift of ordinary open scalar balancing -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules.ToposOpenScalar
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (A : Sheaf J (Type u)) {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
  [HasDerivedCategory.{w}
    (ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients J R))]
  [HasDerivedCategory.{w}
    (ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients J S))]
  [HasDerivedCategory.{w} (ringedSiteModules.{u}
    (derivedChangeRingIndependentCoefficients (elementTopology A) (presentationElementRing R A)))]
  [HasDerivedCategory.{w} (ringedSiteModules.{u}
    (derivedChangeRingIndependentCoefficients (elementTopology A) (presentationElementRing S A)))]
  [(extension R A).Additive]
  [(extension S A).Additive]
  [(restriction R A).Additive]
  [(restriction S A).Additive]
  [PreservesFiniteLimits (extension R A)]
  [PreservesFiniteColimits (extension R A)]
  [PreservesFiniteLimits (extension S A)]
  [PreservesFiniteColimits (extension S A)]
  [PreservesFiniteLimits (restriction R A)]
  [PreservesFiniteColimits (restriction R A)]
  [PreservesFiniteLimits (restriction S A)]
  [PreservesFiniteColimits (restriction S A)]

/-- Lift ordinary extension/scalar balancing to the normalized derived open square.
Source: Stacks 0GL1 and 06YT, with the actual-unit refinement of Tag 0E8I
(blueprint: lem-pur-topos-open-scalar-derived-from-ordinary).

Proof: The supplied rho and tau are the ordinary coefficient comparisons with their
actual tensor-generator formulas. Take the right-adjoint
scalar restriction square and its normalized derived mate to construct lambda.
Resolve by flat-term K-flat complexes; inverse image preserves their K-flatness,
so the representative comparison proves lambda invertible. The supplied ordinary
balancing tau intertwines the extension units on tensor generators. Uniqueness in
the scalar adjunction and then in its normalized derived adjunction gives beta.
The cochain transpose formula gives both representative equations before imposing
K-flatness, hence in particular on the specified representatives. Finally,
the twofold mates identity applied to the scalar restriction square identifies the
open mate of beta inverse with lambda inverse. The unit formula for this mate gives
its adjunct equality; composing with restriction of beta gives the displayed
unit equality. All maps are induced by the actual adjunctions and their cochain
factorizations, so no freely chosen normalization is introduced. -/
theorem exists_toposOpenScalarDerivedFromOrdinary
    (ET : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} a)
    (EV : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} (sliceMap A a))
    (rho : ET.E ⋙ restriction S A ≅ restriction R A ⋙ EV.E)
    (hrho : (∀ (M : ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients J R))
        (U : Cᵒᵖ) (f : A.obj.obj U) (m : M.val.obj U) (s : S.obj.obj U),
        (rho.hom.app M).val.app (elementObj A U f) (tensorSection a ET M U m s) =
          tensorSection (sliceMap A a) EV
            ((restriction R A).obj M)
            (elementObj A U f) m s))
    (tau : extension R A ⋙ ET.E ≅ EV.E ⋙ extension S A)
    (htau : (∀ (M : ringedSiteModules.{u}
          (derivedChangeRingIndependentCoefficients (elementTopology A) (presentationElementRing
            R A)))
        (U : Cᵒᵖ) (f : A.obj.obj U) (m : M.val.obj (elementObj A U f)) (s : S.obj.obj U),
        (tau.hom.app M).val.app U
            (tensorSection a ET _ U
              (extensionSection R A M U f m) s) =
          extensionSection S A (EV.E.obj M) U f
            (tensorSection (sliceMap A a) EV M (elementObj A U f) m s))) :
    ∃ (lambda : ET.T ⋙ (restriction S A).mapDerivedCategory.{w, w} ≅
        (restriction R A).mapDerivedCategory.{w, w}
          ⋙ EV.T)
      (beta : (extension R A).mapDerivedCategory.{w, w} ⋙ ET.T ≅
        EV.T ⋙ (extension S A).mapDerivedCategory.{w, w}),
      (∀ (P : CochainComplex
          (ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients J R)) ℤ),
        CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
        (restriction S A).mapDerivedCategory.{w, w}.map
            (ET.ε.app P) ≫
          (restriction S A).mapDerivedCategoryFactors.{w, w}.hom.app ((ET.E.mapHomologicalComplex
            (.up ℤ)).obj P) ≫
          DerivedCategory.Q.{w}.map ((NatIso.mapHomologicalComplex rho (.up ℤ)).hom.app P) =
        lambda.hom.app (DerivedCategory.Q.{w}.obj P) ≫
          EV.T.map ((restriction R A).mapDerivedCategoryFactors.{w, w}.hom.app P) ≫
          EV.ε.app (((restriction R A).mapHomologicalComplex (.up ℤ)).obj P)) ∧
      (∀ (P : CochainComplex (ringedSiteModules.{u}
          (derivedChangeRingIndependentCoefficients (elementTopology A) (presentationElementRing
            R A))) ℤ),
        CochainComplex.IsKFlatIndependentCoefficients (R := presentationElementRing R A) P →
        ET.T.map ((extension R A).mapDerivedCategoryFactors.{w, w}.hom.app P) ≫
          ET.ε.app (((extension R A).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.{w}.map ((NatIso.mapHomologicalComplex tau (.up ℤ)).hom.app P) =
        beta.hom.app (DerivedCategory.Q.{w}.obj P) ≫
          (extension S A).mapDerivedCategory.{w, w}.map (EV.ε.app P) ≫
          (extension S A).mapDerivedCategoryFactors.{w, w}.hom.app ((EV.E.mapHomologicalComplex
            (.up ℤ)).obj P)) ∧
      (∀ M : DerivedCategory (ringedSiteModules.{u}
          (derivedChangeRingIndependentCoefficients (elementTopology A) (presentationElementRing
            R A))),
        EV.T.map ((OpenTensorNormalization.exactDerivedAdjunction.{u + 1, u, w}
          (normalizedAdjunction R A)).unit.app M) ≫
          lambda.inv.app ((extension R A).mapDerivedCategory.{w, w}.obj M) ≫
          (restriction S A).mapDerivedCategory.{w, w}.map (beta.hom.app M) =
        (OpenTensorNormalization.exactDerivedAdjunction.{u + 1, u, w}
        (normalizedAdjunction S A)).unit.app
          (EV.T.obj M)) := by
  sorry

end SheafOfModules.ToposOpenScalar
