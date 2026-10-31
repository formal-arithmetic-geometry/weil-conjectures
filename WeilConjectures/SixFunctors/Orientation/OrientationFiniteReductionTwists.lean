/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Orientation.OrientationCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateSiteDescent
import all WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
import WeilConjectures.SmoothPurity.Supporting.SignedTwistFirstReduction
import all WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageScalarComparison

/-! Canonical finite quotient and realization of the completed root lines.
Source: def-coefficient-twists-detailed
(blueprint: def-sf-orientation-finite-reduction-comparisons). -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures

/-- The finite positive root line in its single-complex model.
Source: finite coefficient convention
(blueprint: def-sf-orientation-finite-reduction-comparisons). -/
def sfOrientationFiniteComplex
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (m d : ℕ) :=
  (HomologicalComplex.single _ (.up ℤ) (-2 * (d : ℤ))).obj
    (finiteCoefficientTwist l E X m (d : ℤ))

/-- The scalar-adjunction transpose of a quotient map on a shifted root line.
Exact restriction, its single-complex comparison and its derived factors are
used literally. Source: coefficient reduction comparison
(blueprint: def-sf-orientation-finite-reduction-comparisons). -/
def sfOrientationFiniteQuotientTranspose
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (m d : ℕ)
    (q : integralTwistLine l E X (d : ℤ) ⟶
      (scalarReductionRestriction l E X m).obj (finiteCoefficientTwist l E X m (d : ℤ))) :=
  letI := (scalarReductionRestriction_exact l E X m).1
  letI := (scalarReductionRestriction_exact l E X m).2
  let F := scalarReductionRestriction l E X m
  DerivedCategory.Q.map
    ((HomologicalComplex.single _ (.up ℤ) (-2 * (d : ℤ))).map q) ≫
    (DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ)
        (-2 * (d : ℤ))).app (finiteCoefficientTwist l E X m (d : ℤ)))).inv ≫
    (F.mapDerivedCategoryFactors.app (sfOrientationFiniteComplex l E X m d)).inv

section SingleAdjunction

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  (F : A ⥤ B) (R : B ⥤ A) [F.Additive] [R.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  (a : F ⊣ R) (L : DerivedCategory A ⥤ DerivedCategory B)
  (b : L ⊣ R.mapDerivedCategory)

omit [HasDerivedCategory A] [HasDerivedCategory B]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R] in
private theorem single_unit_comp (M : A) (N : B) (k : ℤ) (e : F.obj M ⟶ N) :
    (a.mapHomologicalComplex (.up ℤ)).unit.app
        ((HomologicalComplex.single A (.up ℤ) k).obj M) ≫
      (R.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) k).hom.app M ≫
          (HomologicalComplex.single B (.up ℤ) k).map e) =
    (HomologicalComplex.single A (.up ℤ) k).map (a.homEquiv _ _ e) ≫
      (HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) k).inv.app N := by
  apply HomologicalComplex.from_single_hom_ext
  change a.unit.app (((HomologicalComplex.single A (.up ℤ) k).obj M).X k) ≫
      R.map (((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) k).hom.app M).f k ≫
        ((HomologicalComplex.single B (.up ℤ) k).map e).f k) =
    ((HomologicalComplex.single A (.up ℤ) k).map (a.homEquiv _ _ e)).f k ≫
      ((HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) k).inv.app N).f k
  simp only [HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    HomologicalComplex.single_map_f_self, Adjunction.homEquiv_unit,
    Category.assoc, Iso.inv_hom_id_assoc, Functor.map_comp, HomologicalComplex.comp_f]
  simpa only [Functor.id_map, Functor.comp_map, Category.assoc] using
    congrArg (fun f ↦ f ≫ R.map e ≫
      R.map (HomologicalComplex.singleObjXSelf (.up ℤ) k N).inv)
      (a.unit.naturality (HomologicalComplex.singleObjXSelf (.up ℤ) k M).hom).symm

private theorem exact_factor_on_quotient (K : CochainComplex B ℤ) :
    R.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K) =
      R.mapDerivedCategoryFactors.hom.app K := by
  rw [R.mapDerivedCategoryFactorsh_hom_app]
  change R.mapDerivedCategory.map (𝟙 _) ≫ _ ≫ 𝟙 _ ≫
    DerivedCategory.Qh.map (𝟙 _) = _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

private theorem unit_compatibility_from_homotopy
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex A ℤ)
    (h : b.unit.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      R.mapDerivedCategory.map (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      R.mapDerivedCategoryFactorsh.hom.app
        ((F.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
      DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) :
    b.unit.app (DerivedCategory.Q.obj P) ≫
      R.mapDerivedCategory.map (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      R.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P) := by
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient] at h
  erw [exact_factor_on_quotient R ((F.mapHomologicalComplex (.up ℤ)).obj P)] at h
  exact h

private theorem single_derived_transpose (M : A) (N : B) (k : ℤ)
    (c : L.obj (DerivedCategory.Q.obj
      ((HomologicalComplex.single A (.up ℤ) k).obj M)) ⟶
        DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj
          ((HomologicalComplex.single A (.up ℤ) k).obj M)))
    (hc : b.unit.app (DerivedCategory.Q.obj
        ((HomologicalComplex.single A (.up ℤ) k).obj M)) ≫
      R.mapDerivedCategory.map c ≫ R.mapDerivedCategoryFactors.hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj
          ((HomologicalComplex.single A (.up ℤ) k).obj M)) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app
        ((HomologicalComplex.single A (.up ℤ) k).obj M)))
    (e : F.obj M ⟶ N) :
    b.homEquiv _ _ (c ≫ DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) k).hom.app M ≫
        (HomologicalComplex.single B (.up ℤ) k).map e)) =
      DerivedCategory.Q.map ((HomologicalComplex.single A (.up ℤ) k).map
        (a.homEquiv _ _ e)) ≫
      (DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) k).app N)).inv ≫
      (R.mapDerivedCategoryFactors.app
        ((HomologicalComplex.single B (.up ℤ) k).obj N)).inv := by
  apply (cancel_mono (R.mapDerivedCategoryFactors.hom.app
    ((HomologicalComplex.single B (.up ℤ) k).obj N))).1
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  simp only [Category.assoc, Functor.mapIso_inv, Iso.app_inv,
    Iso.inv_hom_id_app]
  rw [R.mapDerivedCategoryFactors_hom_naturality]
  rw [← Category.assoc, ← Category.assoc]
  rw [show (b.unit.app _ ≫ R.mapDerivedCategory.map c) ≫ _ = _ from
    (Category.assoc _ _ _).trans hc]
  rw [← DerivedCategory.Q.map_comp]
  rw [single_unit_comp]
  rw [DerivedCategory.Q.map_comp]
  exact congrArg (fun f ↦ DerivedCategory.Q.map
    ((HomologicalComplex.single A (.up ℤ) k).map (a.homEquiv _ _ e)) ≫ f)
    (Category.comp_id (DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) k).inv.app N))).symm

end SingleAdjunction

section ReductionProof

attribute [local irreducible] HasDerivedCategory.standard
  scalarReductionExistence scalarReductionDerivedExistence scalarReductionExtension
  completedIntegralCoefficientSheafUnrestricted SheafOfModules.monoidalCategory
attribute [local implicit_reducible] completedIntegralCommRingSheafUnrestricted
set_option synthInstance.maxSize 4096

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (m : ℕ)

private def finiteFirstComparison :
    SheafOfModules.changeOfRingsOfUniverses.{u, u+1, u+1, u+1}
      (completedIntegralCommRingProjectionUnrestricted l E X m)
        (purTwistIntegralModule X l E) ≅ purTwistFiniteOne X l E m :=
  (signedTwistFirstReduction l E X m).choose

private theorem finiteFirstComparison_unit (W : X.ProEtᵒᵖ)
    (x : (purTwistIntegralOne X l E).val.obj W) :
    (finiteFirstComparison l E X m).hom.val.app W
      (SheafOfModules.scalarExtensionSection
        (completedIntegralCommRingProjectionUnrestricted l E X m)
        (purTwistIntegralModule X l E) W 1 x) =
      SheafOfModules.scalarExtensionSection (purTwistIntegralQuotient X l E m)
        (purTwistIntegralOne X l E) W 1 x :=
  (signedTwistFirstReduction l E X m).choose_spec W x

private def finitePowerComparison (d : ℕ) :
    SheafOfModules.changeOfRingsOfUniverses.{u, u+1, u+1, u+1}
      (completedIntegralCommRingProjectionUnrestricted l E X m)
        (integralTwistLine l E X (d : ℤ)) ≅ finiteCoefficientTwist l E X m (d : ℤ) :=
  SheafOfModules.positiveComparison
    (completedIntegralCommRingProjectionUnrestricted l E X m)
    (purTwistIntegralModule X l E) (purTwistFiniteOne X l E m)
    (finiteFirstComparison l E X m) d

private def finiteOrdinaryComparison (d : ℕ) :
    (scalarReductionExtension l E X m).obj (integralTwistLine l E X (d : ℤ)) ≅
      finiteCoefficientTwist l E X m (d : ℤ) :=
  (Adjunction.leftAdjointUniq
    (scalarReductionExtension_adjunction l E X m).choose
    (PurScalar.tensorAdjunction.{u+1, u+1, u}
      (completedIntegralCommRingProjectionUnrestricted l E X m))).app
      (integralTwistLine l E X (d : ℤ)) ≪≫ finitePowerComparison l E X m d

private def finiteQuotient (d : ℕ) :
    integralTwistLine l E X (d : ℤ) ⟶
      (scalarReductionRestriction l E X m).obj (finiteCoefficientTwist l E X m (d : ℤ)) :=
  ((scalarReductionExtension_adjunction l E X m).choose.homEquiv _ _)
    (finiteOrdinaryComparison l E X m d).hom

private theorem finiteQuotient_apply (d : ℕ) (W : X.ProEtᵒᵖ)
    (x : (integralTwistLine l E X (d : ℤ)).val.obj W) :
    (finiteQuotient l E X m d).val.app W x =
      (finitePowerComparison l E X m d).hom.val.app W
        (SheafOfModules.scalarExtensionSection
          (completedIntegralCommRingProjectionUnrestricted l E X m)
          (integralTwistLine l E X (d : ℤ)) W 1 x) := by
  unfold finiteQuotient
  rw [Adjunction.homEquiv_unit]
  let p := completedIntegralCommRingProjectionUnrestricted l E X m
  let M := integralTwistLine l E X (d : ℤ)
  let a := (scalarReductionExtension_adjunction l E X m).choose
  let b := PurScalar.tensorAdjunction.{u+1, u+1, u} p
  let e := (Adjunction.leftAdjointUniq a b).app M
  have hu := congrArg (fun f ↦ f.val.app W x)
    (Adjunction.unit_leftAdjointUniq_hom_app a b M)
  change e.hom.val.app W ((a.unit.app M).val.app W x) =
    (b.unit.app M).val.app W x at hu
  have hb : (b.unit.app M).val.app W x =
      SheafOfModules.scalarExtensionSection p M W 1 x := by
    unfold b PurScalar.tensorAdjunction
    rfl
  change (finitePowerComparison l E X m d).hom.val.app W
    (e.hom.val.app W ((a.unit.app M).val.app W x)) = _
  exact congrArg ((finitePowerComparison l E X m d).hom.val.app W) (hu.trans hb)

private theorem finiteQuotient_zero (W : X.ProEtᵒᵖ)
    (a : (completedIntegralCommRingSheafUnrestricted l E X).obj.obj W) :
    (finiteQuotient l E X m 0).val.app W a =
      (completedIntegralCommRingProjectionUnrestricted l E X m).hom.app W a := by
  rw [finiteQuotient_apply]
  change (SheafOfModules.scalarExtensionUnitIso
    (completedIntegralCommRingProjectionUnrestricted l E X m)).hom.val.app W _ = _
  exact (SheafOfModules.scalarExtensionUnitIso_tmul.{u+1, u, u+1}
    (completedIntegralCommRingProjectionUnrestricted l E X m) W 1 a).trans
      (one_mul (((completedIntegralCommRingProjectionUnrestricted l E X m).hom.app W).hom a))

private theorem finiteQuotient_one (W : X.ProEtᵒᵖ)
    (x : (purTwistIntegralOne X l E).val.obj W) :
    (finiteQuotient l E X m 1).val.app W x =
      SheafOfModules.scalarExtensionSection (purTwistIntegralQuotient X l E m)
        (purTwistIntegralOne X l E) W 1 x := by
  rw [finiteQuotient_apply]
  exact finiteFirstComparison_unit l E X m W x

private theorem finiteQuotient_tensor (d : ℕ) (W : X.ProEtᵒᵖ)
    (x : (integralTwistLine l E X ((d + 1 : ℕ) : ℤ)).val.obj W)
    (y : (purTwistIntegralModule X l E).val.obj W) :
    (finiteQuotient l E X m (d + 2)).val.app W
      (SheafOfModules.siteSheafTensorTmul
        (A := completedIntegralCommRingSheafUnrestricted l E X)
        (integralTwistLine l E X ((d + 1 : ℕ) : ℤ))
        (purTwistIntegralModule X l E) W x y) =
      SheafOfModules.siteSheafTensorTmul
        (A := integralCoefficientCommRingSheaf l E X m)
        (finiteCoefficientTwist l E X m ((d + 1 : ℕ) : ℤ))
        (finiteCoefficientTwist l E X m (1 : ℤ)) W
        ((finiteQuotient l E X m (d + 1)).val.app W x)
        ((finiteQuotient l E X m 1).val.app W y) := by
  simp only [finiteQuotient_apply]
  exact SheafOfModules.positiveComparison_tmul
    (completedIntegralCommRingProjectionUnrestricted l E X m)
    (purTwistIntegralModule X l E) (purTwistFiniteOne X l E m)
    (finiteFirstComparison l E X m) d W 1 x y

variable [∀ x : X, Invertible (l : X.residueField x)]

set_option maxHeartbeats 1600000 in
-- Elaborating the unit identity compares the fixed, large coefficient categories.
private theorem finiteDerivedCounit_unit (d : ℕ) :
    let F := scalarReductionExtension l E X m
    let R := scalarReductionRestriction l E X m
    letI := scalarReductionExtensionAdditive l E X m
    letI := (scalarReductionRestriction_exact l E X m).1
    letI := (scalarReductionRestriction_exact l E X m).2
    let P := sfOrientationIntegralComplex l E X d
    (derivedScalarExtensionRestrictionAdjunction l E X m).choose.unit.app
        (DerivedCategory.Q.obj P) ≫
      (scalarReductionDerivedRestriction l E X m).map
        ((scalarReductionCounit l E X m).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      R.mapDerivedCategoryFactors.hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        (((scalarReductionExtension_adjunction l E X m).choose.mapHomologicalComplex
          (.up ℤ)).unit.app P) := by
  let F := scalarReductionExtension l E X m
  let R := scalarReductionRestriction l E X m
  let := scalarReductionExtensionAdditive l E X m
  let := (scalarReductionRestriction_exact l E X m).1
  let := (scalarReductionRestriction_exact l E X m).2
  let P := sfOrientationIntegralComplex l E X d
  exact unit_compatibility_from_homotopy F R
    (scalarReductionExtension_adjunction l E X m).choose
    (scalarReductionDerivedExtension l E X m)
    (derivedScalarExtensionRestrictionAdjunction l E X m).choose
    (scalarReductionCounit l E X m) P
    ((derivedScalarExtensionRestrictionAdjunction l E X m).choose_spec P
      (sfOrientationIntegralComplex_good l E X d).1)

private def finiteDerivedComparison (d : ℕ) :
    (scalarReductionDerivedExtension l E X m).obj
      (DerivedCategory.Q.obj (sfOrientationIntegralComplex l E X d)) ≅
        DerivedCategory.Q.obj (sfOrientationFiniteComplex l E X m d) := by
  let F := scalarReductionExtension l E X m
  let := scalarReductionExtensionAdditive l E X m
  let P := sfOrientationIntegralComplex l E X d
  haveI hc : IsIso ((scalarReductionCounit l E X m).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
    (scalarReductionDerivedExistence l E X m).choose_spec.choose_spec.2.2 P
      (sfOrientationIntegralComplex_good l E X d).1
  exact asIso ((scalarReductionCounit l E X m).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ)
        (-2 * (d : ℤ))).app (integralTwistLine l E X (d : ℤ))) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.single _ (.up ℤ) (-2 * (d : ℤ))).mapIso
        (finiteOrdinaryComparison l E X m d))

private theorem finiteDerivedComparison_transpose (d : ℕ) :
    ((derivedScalarExtensionRestrictionAdjunction l E X m).choose.homEquiv _ _)
      (finiteDerivedComparison l E X m d).hom =
      sfOrientationFiniteQuotientTranspose l E X m d (finiteQuotient l E X m d) := by
  let := scalarReductionExtensionAdditive l E X m
  let := (scalarReductionRestriction_exact l E X m).1
  let := (scalarReductionRestriction_exact l E X m).2
  have h := single_derived_transpose
    (scalarReductionExtension l E X m) (scalarReductionRestriction l E X m)
    (scalarReductionExtension_adjunction l E X m).choose
    (scalarReductionDerivedExtension l E X m)
    (derivedScalarExtensionRestrictionAdjunction l E X m).choose
    (integralTwistLine l E X (d : ℤ)) (finiteCoefficientTwist l E X m (d : ℤ))
    (-2 * (d : ℤ)) ((scalarReductionCounit l E X m).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj (sfOrientationIntegralComplex l E X d)))
    (finiteDerivedCounit_unit l E X m d)
    (finiteOrdinaryComparison l E X m d).hom
  simpa only [finiteDerivedComparison, Iso.trans_hom, Functor.mapIso_hom,
    asIso_hom, DerivedCategory.Q.map_comp, Iso.app_hom,
    finiteQuotient, sfOrientationFiniteQuotientTranspose, sfOrientationIntegralComplex,
    sfOrientationFiniteComplex, scalarReductionDerivedRestriction,
    FrobeniusCoefficientTwists.positiveLine, integralTwistLine, coefficientTwistLine,
    coefficientTwistPower, Category.assoc] using h

end ReductionProof

/-- The normalized derived quotient of every shifted positive root power.
The auxiliary ordinary arrows are specified by their coefficient, first-root,
and tensor formulas; they are not extra input or freely chosen data.
Source: finite reduction convention (blueprint: def-sf-orientation-finite-reduction-comparisons).
Proof: the ordinary arrows are the transposes of the comparisons
`signedTwistFirstReduction` (first root) extended by `positiveComparison` (positive
powers); the chosen scalar extension is compared with the explicit tensor functor by
uniqueness of left adjoints, which preserves units. This gives the coefficient
projection at zero, the scalar-extension unit at one and the tensor formula above.
The shifted integral line is K-flat, so the scalar-reduction counit on it is
invertible; followed by the functor/single comparison and the single complex of the
ordinary power comparison it is the derived isomorphism, whose transpose is
`sfOrientationFiniteQuotientTranspose` by the K-flat unit compatibility of the
derived adjunction. Uniqueness: two normalized ordinary families agree at zero and
one sectionwise, hence at every power by two-step induction and tensor hom-ext; two
derived families then agree by injectivity of the adjunction Hom equivalence. -/
theorem sfOrientationFiniteReduction_existsUnique
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (m : ℕ) :
    ∃! t : ∀ d : ℕ, (scalarReductionDerivedExtension l E X m).obj
      (DerivedCategory.Q.obj (sfOrientationIntegralComplex l E X d)) ≅
        DerivedCategory.Q.obj (sfOrientationFiniteComplex l E X m d),
      ∃ q : ∀ d : ℕ, integralTwistLine l E X (d : ℤ) ⟶
        (scalarReductionRestriction l E X m).obj (finiteCoefficientTwist l E X m (d : ℤ)),
        (∀ (W : X.ProEtᵒᵖ)
          (a : (completedIntegralCommRingSheafUnrestricted l E X).obj.obj W),
          (q 0).val.app W a =
            (completedIntegralCommRingProjectionUnrestricted l E X m).hom.app W a) ∧
        (∀ (W : X.ProEtᵒᵖ) (x : (purTwistIntegralOne X l E).val.obj W),
          (q 1).val.app W x =
            (((PresheafOfModules.sheafificationAdjunction
              (𝟙 (integralCoefficientSheaf l E X m).obj)).unit.app
                (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u+1, u+1, u+1}
                  (purTwistIntegralQuotient X l E m) (purTwistIntegralOne X l E))).app W)
              ((1 : (integralCoefficientCommRingSheaf l E X m).obj.obj W)
                ⊗ₜ[_, ((purTwistIntegralQuotient X l E m).hom.app W).hom] x)) ∧
        (∀ (d : ℕ) (W : X.ProEtᵒᵖ)
          (x : (integralTwistLine l E X ((d + 1 : ℕ) : ℤ)).val.obj W)
          (y : (purTwistIntegralModule X l E).val.obj W),
          (q (d + 2)).val.app W
            (SheafOfModules.siteSheafTensorTmul
              (A := completedIntegralCommRingSheafUnrestricted l E X)
              (integralTwistLine l E X ((d + 1 : ℕ) : ℤ))
              (purTwistIntegralModule X l E) W x y) =
          SheafOfModules.siteSheafTensorTmul
            (A := integralCoefficientCommRingSheaf l E X m)
            (finiteCoefficientTwist l E X m ((d + 1 : ℕ) : ℤ))
            (finiteCoefficientTwist l E X m (1 : ℤ)) W
            ((q (d + 1)).val.app W x) ((q 1).val.app W y)) ∧
        ∀ d : ℕ,
          ((derivedScalarExtensionRestrictionAdjunction l E X m).choose.homEquiv _ _)
            (t d).hom =
          sfOrientationFiniteQuotientTranspose l E X m d (q d) := by
  let q := finiteQuotient l E X m
  let t := finiteDerivedComparison l E X m
  have hq0 := finiteQuotient_zero l E X m
  have hq1 := finiteQuotient_one l E X m
  have hqt := finiteQuotient_tensor l E X m
  refine ⟨t, ⟨q, hq0, hq1, hqt, finiteDerivedComparison_transpose l E X m⟩, ?_⟩
  intro t' ht'
  obtain ⟨q', hq0', hq1', hqt', hdt'⟩ := ht'
  have hfirst : q' 1 = q 1 := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (hq1' W x).trans (hq1 W x).symm
  have hqq : q' = q := by
    funext d
    induction d using Nat.twoStepInduction with
    | zero =>
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro W
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      exact (hq0' W a).trans (hq0 W a).symm
    | one => exact hfirst
    | more d _ ih =>
      apply SheafOfModules.scalarTensor_hom_ext
        (R := completedIntegralCommRingSheafUnrestricted l E X) _ _
      intro W x y
      calc
        _ = _ := hqt' d W x y
        _ = _ := by rw [ih, hfirst]
        _ = _ := (hqt d W x y).symm
  subst q'
  funext d
  apply Iso.ext
  let adj := (derivedScalarExtensionRestrictionAdjunction l E X m).choose
  apply (adj.homEquiv _ _).injective
  exact (hdt' d).trans (finiteDerivedComparison_transpose l E X m d).symm

/-- The actual finite reduction, selected by its unique root-quotient transpose.
Source: coefficient convention (blueprint: def-sf-orientation-finite-reduction-comparisons). -/
def sfOrientationFiniteReduction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (m d : ℕ) :=
  (sfOrientationFiniteReduction_existsUnique l E X m).exists.choose d

/-- Use the published positive-quotient finiteness witness.
Source: coefficient conventions (blueprint: def-sf-orientation-finite-reduction-comparisons). -/
instance sfOrientationQuotientFinite
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (m : ℕ) :
    Finite (Padic.coefficientExtensionRing l E (m + 1)) :=
  Padic.finite_coefficientExtensionRing l E (m + 1) (Nat.succ_le_succ (Nat.zero_le m))


end WeilConjectures
