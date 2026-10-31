/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefTowerTraceRectification
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.CategoryTheory.ConstantRingModuleSheaves
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.CategoryTheory.CoefficientRestrictionSectionEvaluationAcyclic
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective

/-! # Sections acyclicity after restriction to constant integral scalars -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private instance (priority := 10000) traceSiteSmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _

private instance (priority := 10000) traceAbSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} X

private instance (priority := 10000) traceAbLocallyBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} X

private instance (priority := 10000) traceRingSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) RingCat.{u + 1} :=
  hasSheafifyEssentiallySmallSite _ _

private instance (priority := 10000) traceCommRingSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) CommRingCat.{u + 1} :=
  integralCoefficientRingSheafify.{u, u} X

private instance (priority := 10000) traceForgetSheafification (X : Scheme.{u}) :
    (ProEt.topology X).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) where
  le := by
    intro P Q f hf
    have : Presheaf.IsLocallyInjective (ProEt.topology X) f := hf.isLocallyInjective
    have : Presheaf.IsLocallySurjective (ProEt.topology X) f := hf.isLocallySurjective
    apply ((ProEt.topology X).W_iff_isLocallyBijective _).mpr
    constructor
    · exact ⟨fun x y h ↦ Presheaf.equalizerSieve_mem (ProEt.topology X) f x y h⟩
    · exact ⟨fun x ↦ Presheaf.imageSieve_mem (ProEt.topology X) f x⟩

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

private theorem constantScalar_unit (U : X.ProEtᵒᵖ) (a : coefTraceRing l E) :
    ((constantCommuteCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app
        (CommRingCat.of (coefTraceRing l E))).hom.app U
      ((toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (coefTraceRing l E)))).app U a) =
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (coefTraceRing l E)))).app U a := by
  let J := ProEt.topology X
  let R := coefTraceRing l E
  have hc := toSheafify_naturality J
    (Functor.constComp X.ProEtᵒᵖ (CommRingCat.of R)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv
  change ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of R)) ≫
    sheafifyMap J (Functor.constComp X.ProEtᵒᵖ (CommRingCat.of R)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv ≫
    (sheafifyComposeIso J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of R))).hom).app U) a = _
  erw [← Category.assoc, ← hc, Category.assoc, sheafComposeIso_hom_fac]
  rfl

private def constantScalarMap :
    (constantSheaf (ProEt.topology X) RingCat.{u + 1}).obj
      (RingCat.of (coefTraceRing l E)) ⟶ completedIntegralCoefficientSheafUnrestricted l E X :=
  (constantCommuteCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app
      (CommRingCat.of (coefTraceRing l E)) ≫ integralConstantToCompletionOfUniverses l E X

private def constantScalarComparison :
    SheafOfModules.restrictScalars (constantScalarMap l E X) ⋙
      constantRingModuleRestriction (ProEt.topology X) (coefTraceRing l E) ≅
        coefTraceConstantScalars l E X := by
  let J := ProEt.topology X
  let R := coefTraceRing l E
  let b := integralConstantToCompletionOfUniverses l E X
  let T := op (ProEt.mk (𝟙 X))
  let ht : IsInitial T := (MorphismProperty.Over.mkIdTerminal _ _).op
  let F := SheafOfModules.restrictScalars (constantScalarMap l E X) ⋙
    constantRingModuleRestriction J R
  let G := coefTraceConstantScalars l E X
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · refine ObjectProperty.isoMk _ (NatIso.ofComponents (fun U ↦
      LinearEquiv.toModuleIso
        (show (F.obj M).obj.obj U ≃ₗ[R] (G.obj M).obj.obj U from
        { toFun := fun x ↦ x
          invFun := fun x ↦ x
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          map_add' := fun _ _ ↦ rfl
          map_smul' := ?_ })) ?_)
    · intro a x
      let : Module ((completedIntegralCoefficientSheafUnrestricted l E X).obj.obj U)
          ((F.obj M).obj.obj U) := (M.val.obj U).isModule
      change (b.hom.app U).hom
        (((constantCommuteCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app
          (CommRingCat.of R)).hom.app U
            ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of R))).app U a)) • x =
        ((completedIntegralCoefficientSheafUnrestricted l E X).obj.map (ht.to U)).hom
          (coefTraceScalar l E X a) • x
      rw [constantScalar_unit l E X]
      congr 1
      let η : (Functor.const X.ProEtᵒᵖ).obj (RingCat.of R) ⟶
          (integralConstantRingOfUniverses l E X).obj :=
        Functor.whiskerRight
          (toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of R)))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
      have hb := congrArg (fun k ↦ k.hom ((η.app T).hom a))
        (b.hom.naturality (ht.to U))
      have hu := congrArg (fun k ↦ k.hom a) (η.naturality (ht.to U))
      dsimp only [Functor.const_obj_map, Category.id_comp] at hu
      change (b.hom.app U).hom ((η.app U).hom a) = _
      exact (congrArg (fun y ↦ (b.hom.app U).hom y) hu).trans hb
    · intro U V f
      ext x
      rfl
  · intro M N f
    ext U x
    rfl

private theorem constantScalar_sections_quasiIso
    (I : CochainComplex (scalarReductionSource l E X) ℤ) [I.IsKInjective]
    (K : CochainComplex (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (coefTraceRing l E))) ℤ) [K.IsKInjective]
    (j : ((coefTraceConstantScalars l E X).mapHomologicalComplex (.up ℤ)).obj I ⟶ K)
    [QuasiIso j] :
    QuasiIso ((((sheafSections (ProEt.topology X)
      (ModuleCat.{u + 1} (coefTraceRing l E))).obj
        (op (ProEt.mk (𝟙 X)))).mapHomologicalComplex (.up ℤ)).map j) := by
  let J := ProEt.topology X
  let R := coefTraceRing l E
  let B := (constantSheaf J RingCat.{u + 1}).obj (RingCat.of R)
  let D := completedIntegralCoefficientSheafUnrestricted l E X
  let b := constantScalarMap l E X
  let r := SheafOfModules.restrictScalars b
  let f := coefTraceConstantScalars l E X
  obtain ⟨e, hf, ha, hi, he⟩ := (constant_ring_module_sheaves J R).1
  have : e.functor.Additive := ha
  have : e.inverse.Additive := hi
  have : f.Additive := inferInstanceAs (coefTraceConstantScalars l E X).Additive
  let T := op (ProEt.mk (𝟙 X))
  let ev := sheafToPresheaf J AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation _ _).obj T
  let A := SheafOfModules.toSheaf B ⋙ ev
  let V := forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}
  let H := sheafCompose J V ⋙ ev
  let α : r ≅ f ⋙ e.inverse :=
    r.rightUnitor.symm ≪≫ Functor.isoWhiskerLeft r e.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (Functor.isoWhiskerLeft r (eqToIso hf) ≪≫ constantScalarComparison l E X)
          e.inverse
  let αc := (NatIso.mapHomologicalComplex α (.up ℤ)).app I
  let K' := (e.inverse.mapHomologicalComplex (.up ℤ)).obj K
  let j' : (r.mapHomologicalComplex (.up ℤ)).obj I ⟶ K' :=
    αc.hom ≫ (e.inverse.mapHomologicalComplex (.up ℤ)).map j
  have : CochainComplex.IsKInjective K' := inferInstance
  have : QuasiIso j' := by dsimp only [j']; infer_instance
  have hB (U : X.ProEtᵒᵖ) (a b : B.obj.obj U) : a * b = b * a := by
    let c := (constantCommuteCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app (CommRingCat.of R)
    apply (ConcreteCategory.bijective_of_isIso (c.inv.hom.app U)).1
    change (c.inv.hom.app U).hom (a * b) = (c.inv.hom.app U).hom (b * a)
    rw [map_mul, map_mul]
    exact mul_comm (show ((constantSheaf J CommRingCat.{u + 1}).obj
      (CommRingCat.of R)).obj.obj U from (c.inv.hom.app U).hom a) _
  have hD (U : X.ProEtᵒᵖ) (a b : D.obj.obj U) : a * b = b * a :=
    completedIntegralCoefficient_mul_commUnrestricted l E X U a b
  have hq : QuasiIso ((A.mapHomologicalComplex (.up ℤ)).map j') :=
    SheafOfModules.coefficientRestrictionSectionsEvaluation_quasiIso.{u + 1, u, u}
      B D hB hD b I K' j' (ProEt.mk (𝟙 X))
  have hq' : QuasiIso ((A.mapHomologicalComplex (.up ℤ)).map
      ((e.inverse.mapHomologicalComplex (.up ℤ)).map j)) := by
    dsimp only [j'] at hq
    rw [Functor.map_comp] at hq
    exact quasiIso_of_comp_left ((A.mapHomologicalComplex (.up ℤ)).map αc.hom) _
  let δ : e.inverse ⋙ A ≅ H := eqToIso (by
    dsimp only [A, H]
    rw [← Functor.assoc, he])
  have hH : QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map j) :=
    (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoOfNatIso (NatIso.mapHomologicalComplex δ (.up ℤ)) (Arrow.mk j))).mp hq'
  let : PreservesColimitsOfSize.{0, 0} V :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, 0, 0} (R := R)
  let : PreservesFiniteColimits V := PreservesColimitsOfSize.preservesFiniteColimits V
  apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ V).mp
  exact hH

/-- Completed-coefficient K-injective towers are acyclic for integral point sections
following restriction to constant scalars.

Source: Stacks Project, Cohomology on Sites, Tag 0D6E, and Tags 03DI, 03DJ;
blueprint prop-coef-integral-dualizing, proof paragraph 2, scalar-section square.
(blueprint: lem-coef-completed-tower-sections-acyclic).

Proof: evaluation of a K-injective completed-module tower at each n is K-injective,
since evaluation has an exact left adjoint. View constant R-module sheaves as
modules over the sheafification of the constant ring. Under this exact equivalence,
coefTraceConstantScalars is restriction along the actual constant-to-completion
map: naturality of that map identifies its action on every section with restriction
along the map from the terminal object used in coefTraceConstantScalars. For a
K-injective resolution of the restricted complex, scalar-restriction acyclicity
on the slice over the terminal object says the map on sections is a quasi-isomorphism.
The exact equivalence preserves K-injectives, so this applies to each evaluated
resolution of the tower. Sections of the resolution are therefore a quasi-isomorphism
at every level, and hence in the category of integral-module towers. Naturality of
the right-derived unit, and its invertibility on the resolving K-injective tower,
then imply invertibility on the original restricted tower. This retains the given
constant integral scalar action and all tower transitions. No flatness of a quotient
map or boundedness is needed; zero complexes and empty schemes cause no exception. -/
theorem coefCompletedTowerSections_acyclic
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E X) ℤ) [I.IsKInjective] :
    IsIso ((coefTraceSections l E X).rightDerivedFunctorUnitQ
      ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
        (coefTraceConstantScalars l E X)).mapHomologicalComplex (.up ℤ)).obj I)) := by
  let F := (Functor.whiskeringRight ℕᵒᵖ _ _).obj (coefTraceConstantScalars l E X)
  let G := coefTraceSections l E X
  let L := (F.mapHomologicalComplex (.up ℤ)).obj I
  obtain ⟨K, hK, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective L
  have := hj
  have hsec : QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map j) := by
    apply (HomologicalComplex.quasiIso_iff_evaluation _).mpr
    intro n
    have : CochainComplex.IsKInjective (I.asFunctor.obj n) :=
      tower_evaluation_isKInjective _ I n
    have : CochainComplex.IsKInjective (K.asFunctor.obj n) :=
      tower_evaluation_isKInjective _ K n
    let jn := (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map j).app n
    have : QuasiIso jn :=
      inferInstanceAs (QuasiIso
        ((((CategoryTheory.evaluation ℕᵒᵖ _).obj n).mapHomologicalComplex (.up ℤ)).map j))
    exact constantScalar_sections_quasiIso l E X (I.asFunctor.obj n)
      (K.asFunctor.obj n) jn
  have hunit : IsIso (G.rightDerivedFunctorUnitQ K) := by
    rw [G.rightDerivedFunctorUnitQ_eq]
    infer_instance
  have : IsIso (G.rightDerivedFunctorUnitQ L ≫
      G.rightDerivedFunctor.map (DerivedCategory.Q.map j)) := by
    rw [← G.rightDerivedFunctorUnitQ_naturality j]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (G.rightDerivedFunctor.map (DerivedCategory.Q.map j))

end WeilConjectures
