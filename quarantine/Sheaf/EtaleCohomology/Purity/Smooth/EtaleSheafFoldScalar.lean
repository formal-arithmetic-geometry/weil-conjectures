/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import Sheaf.EtaleCohomology.Purity.Smooth.EtaleCompactificationSheafScalarMap
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.Homology.Additive
import Sheaf.EtaleCohomology.Purity.Smooth.EtaleScalarSectionNormalization
import all Sheaf.EtaleCohomology.Purity.Smooth.EtaleProjectionSectionNormalization
import all Sheaf.SixFunctors.EtaleOpenTensor
import all Sheaf.Paper.EtaleProEtaleScalarMate

/-! # The étale sum fold counit and ordinary scalar extension

Source: Stacks Project, etale-cohomology.tex, Tags 03S3 and 03S4,
equation-j-p-shriek and exercise-jshriek-direct; sites-modules.tex, Tags 03EL and 0GMW
(blueprint: lem-sp-etale-sheaf-fold-scalar).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The scalar-extended fold followed by the scalar unit comparison on the source.
This is the right side of the ordinary fold/scalar square, as a natural transformation.
Source: Stacks, Tags 03S3 and 03EK (blueprint: lem-sp-etale-sheaf-fold-scalar). -/
def etaleScalarExtendedFold
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] :
    (upperStar (ModuleCat.{u + 1} A) e ⋙
        etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance) ⋙
        ProEtale.etaleSheafExtendScalars φ V ⟶ ProEtale.etaleSheafExtendScalars φ V :=
  Functor.whiskerRight
      (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance).counit
      (ProEtale.etaleSheafExtendScalars φ V) ≫
    (Functor.leftUnitor (ProEtale.etaleSheafExtendScalars φ V)).hom

/-- The left side: rho, sum extension of scalar/pullback reassociation, then the B-fold.
All association maps are the ordinary functor associators; no derived functor occurs.
Source: Stacks, Tags 03S3 and 03EL (blueprint: lem-sp-etale-sheaf-fold-scalar). -/
def etaleScalarReassociatedFold
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V) [Etale e]
    (ρ : etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance ⋙
        ProEtale.etaleSheafExtendScalars φ V ⟶
      ProEtale.etaleSheafExtendScalars φ U ⋙
        etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance) :
    (upperStar (ModuleCat.{u + 1} A) e ⋙
        etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance) ⋙
        ProEtale.etaleSheafExtendScalars φ V ⟶ ProEtale.etaleSheafExtendScalars φ V :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) e) ρ ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (scalarSheafPullbackIso φ e).inv
      (etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (ProEtale.etaleSheafExtendScalars φ V)
      (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) e inferInstance).counit ≫
    (Functor.rightUnitor (ProEtale.etaleSheafExtendScalars φ V)).hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical sheaf adjunction is the summand-family bijection, and its counit is fold.
The restriction comparison writes a section of inverse image as a section over the
same underlying test scheme. The second formula therefore says i_s(x) maps to x.
Source: Stacks, Tags 03S3 and 03S4, equation-j-p-shriek and exercise-jshriek-direct
(blueprint: lem-sp-etale-sheaf-fold-scalar).

Proof:
1. Transport the existing sum adjunction's homEquiv through the inverse-image
restriction isomorphism and evaluate on a local section. The proved private
projection_sum_unit in EtaleProjectionSectionNormalization expands the sum unit
as the left Kan-extension unit followed by sheafification, giving the first formula.
2. Apply that formula to the counit. The right triangle identity reduces its
transpose to the identity. The same module's proved etaleLiftSection_iso identifies
the lifted section with the inverse restriction comparison, whose inverse/hom
identity gives the fold formula. -/
theorem etaleSheafSumFold (R : Type (u + 1)) [CommRing R]
    {U V : Scheme.{u}} (e : U ⟶ V)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] :
    (∀ (H : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} R))
      (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} R))
      (k : (etaleLowerShriek (ModuleCat.{u + 1} R) e inferInstance).obj H ⟶ F)
      (W : U.Etale) (x : H.obj.obj (op W)),
      ((upperStarIsoLocalizationRestriction
          (ModuleCat.{u + 1} R) e inferInstance).hom.app F).hom.app (op W)
            (((etaleLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} R) e inferInstance).homEquiv H F k).hom.app (op W) x) =
        k.hom.app (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))
          (etaleSumSection R e H W x)) ∧
    (∀ (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} R)) (W : U.Etale)
      (x : F.obj.obj
        (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))),
      ((etaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} R) e inferInstance).counit.app F).hom.app
          (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))
          (etaleSumSection R e _ W (etaleLiftSection R e F W x)) = x) := by
  have h (H : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} R))
      (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} R))
      (k : (etaleLowerShriek (ModuleCat.{u + 1} R) e inferInstance).obj H ⟶ F)
      (W : U.Etale) (x : H.obj.obj (op W)) := by
    have hk : (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) e
        inferInstance).homEquiv H F k ≫
        (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} R) e
          inferInstance).hom.app F =
        (etaleLowerShriekAdjunction (ModuleCat.{u + 1} R) e inferInstance).homEquiv H F k := by
      simp only [etaleLowerShriekUpperStarAdjunction,
        Adjunction.homEquiv_ofNatIsoRight_apply, Iso.symm_hom, Category.assoc,
        Iso.inv_hom_id_app, Category.comp_id, etaleLowerShriekAdjunction]
      rfl
    have hkW := congrArg (fun f ↦ f.hom.app (op W) x) hk
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      ModuleCat.comp_apply] at hkW
    rw [Adjunction.homEquiv_apply] at hkW
    change _ = k.hom.app _
      (((etaleLowerShriekAdjunction (ModuleCat.{u + 1} R) e inferInstance).unit.app H).hom.app
        (op W) x) at hkW
    rw [projection_sum_unit] at hkW
    exact hkW
  refine ⟨h, ?_⟩
  intro F W x
  have hf := h _ F
    ((etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) e inferInstance).counit.app F)
    W (etaleLiftSection R e F W x)
  rw [Adjunction.right_triangle_components] at hf
  simp only [ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, ModuleCat.id_apply] at hf
  change _ = ((etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) e
    inferInstance).counit.app F).hom.app _ (etaleSumSection R e _ W
      (etaleLiftSection R e F W x)) at hf
  rw [← hf]
  have hl := congrArg (fun f ↦ f x) (etaleLiftSection_iso R e F W)
  change _ = etaleLiftSection R e F W x at hl
  rw [← hl]
  exact congrArg (fun f ↦ f.hom.app (op W) x)
    ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} R) e
      inferInstance).inv_hom_id_app F)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem foldScalarGeometricComparison_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] :
    etaleScalarReassociatedFold φ e (etaleSumScalarIso φ e).hom =
      etaleScalarExtendedFold φ e := by
  let a := etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance
  let b := etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) e inferInstance
  let x := ProEtale.etaleSheafExtendScalarsAdjunction φ V
  let z := ProEtale.etaleSheafExtendScalarsAdjunction φ U
  let q := (upperStarRestrictScalarsIsoSheaf φ e).symm
  let α := (mateEquiv x z).symm (TwoSquare.mk _ _ _ _ q.inv)
  have hm : ((mateEquiv a b).symm α).natTrans =
      (etaleSumScalarIso φ e).inv := scalarOpenInverseMate a b x z q
  apply NatTrans.ext
  funext F
  have h := mateEquiv_counit_symm a b α F
  change _ = ((mateEquiv a b).symm α).natTrans.app _ ≫ _ at h
  rw [hm] at h
  have hr : α.natTrans = (scalarSheafPullbackIso φ e).inv := ordinary_reverse_eq φ e
  change (etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance).map
    (α.natTrans.app F) ≫ b.counit.app
      ((ProEtale.etaleSheafExtendScalars φ V).obj F) = _ at h
  rw [hr] at h
  have hh := congrArg (fun t ↦ (etaleSumScalarIso φ e).hom.app
    ((upperStar (ModuleCat.{u + 1} A) e).obj F) ≫ t) h
  dsimp only [etaleScalarReassociatedFold, etaleScalarExtendedFold,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Functor.rightUnitor_hom_app]
  simp only [Category.id_comp]
  erw [Category.comp_id, Category.comp_id]
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using hh


/-- The canonical ordinary scalar comparison has the local tensor formula and commutes
with the fold counit, naturally and B-linearly, also on unbounded cochain complexes.
The existing scalar/pullback comparison is used in its inverse direction, a_F^0.
Source: Stacks, Tags 03S3, 03S4, 03EL, 0GMW and 010V
(blueprint: lem-sp-etale-sheaf-fold-scalar).

Proof:
1. Construct etaleSumScalarIso by uniqueness of left adjoints for the two composite
sum/scalar adjunctions, with the specified restriction/scalar comparison on the
right adjoints. Use etaleSumScalarIso_tensorSections for its two local formulas.
2. The proved generic scalarOpenInverseMate identifies its inverse with the iterated
inverse mate of that right-adjoint comparison. The proved ordinary_reverse_eq
identifies the first mate with scalarSheafPullbackIso.inv.
3. Apply mateEquiv_counit_symm to the sum adjunctions and precompose with the hom
of etaleSumScalarIso. Cancel hom/inv and expand associators and unitors: this is
the equality of etaleScalarReassociatedFold and etaleScalarExtendedFold.
4. Choose rho to be the constructed isomorphism's hom, combine its local formulas
with this counit equality, and apply mapHomologicalComplex to that equality and
evaluate at P. No totalization or boundedness hypothesis is used. -/
theorem etaleSheafFoldScalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] :
    ∃ ρ : etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance ⋙
          ProEtale.etaleSheafExtendScalars φ V ⟶
        ProEtale.etaleSheafExtendScalars φ U ⋙
          etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance,
      (∀ (H : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : U.Etale)
        (x : H.obj.obj (op W))
        (b : (scalarCoefficientSheaf φ V).obj.obj
          (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))),
        (ρ.app H).hom.app
            (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))
            (compactificationScalarTensorSection φ _
              ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)
              (etaleSumSection A e H W x) b) =
          etaleSumSection B e ((ProEtale.etaleSheafExtendScalars φ U).obj H) W
            (compactificationScalarTensorSection φ H W x
              ((compactificationCoefficientPullbackIso φ e).hom.hom.app (op W)
                (etaleLiftSection A e (scalarCoefficientSheaf φ V) W b)))) ∧
      (∀ (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : U.Etale)
        (x : F.obj.obj
          (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)))
        (b : (scalarCoefficientSheaf φ V).obj.obj
          (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))),
        ((scalarSheafPullbackIso φ e).inv.app F).hom.app (op W)
            (compactificationScalarTensorSection φ _ W (etaleLiftSection A e F W x)
              ((compactificationCoefficientPullbackIso φ e).hom.hom.app (op W)
                (etaleLiftSection A e (scalarCoefficientSheaf φ V) W b))) =
          etaleLiftSection B e ((ProEtale.etaleSheafExtendScalars φ V).obj F) W
            (compactificationScalarTensorSection φ F
              ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W) x b)) ∧
      etaleScalarReassociatedFold φ e ρ = etaleScalarExtendedFold φ e ∧
      (∀ P : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
        (NatTrans.mapHomologicalComplex (etaleScalarReassociatedFold φ e ρ) (.up ℤ)).app P =
          (NatTrans.mapHomologicalComplex (etaleScalarExtendedFold φ e) (.up ℤ)).app P) := by
  have hlocal := etaleSumScalarIso_tensorSections φ e
  have hfold := foldScalarGeometricComparison_counit φ e
  refine ⟨(etaleSumScalarIso φ e).hom, hlocal.1, hlocal.2, hfold, ?_⟩
  intro P
  exact congrArg (fun τ ↦ (NatTrans.mapHomologicalComplex τ (.up ℤ)).app P) hfold

end AlgebraicGeometry.Etale
