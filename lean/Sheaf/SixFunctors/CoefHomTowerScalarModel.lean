/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q64
-/
module

public import Sheaf.Paper.CoefficientRingedSequenceSite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Algebra.Homology.ScalarInternalHomAdjunction
public import Sheaf.CategoryTheory.SystemRingedSequenceSite
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.Paper.ConstantSequenceModuleEquivalenceOfUniverses
public import Mathlib.Algebra.Homology.Functor
import Sheaf.Paper.ConstantSequenceModuleEquivalence
import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.Algebra.Homology.HomComplexGlobalCochains
import Sheaf.Algebra.Homology.KInjectiveHomComplexOfUniverses
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap

/-! # The Hom-tower representative and scalar-adjunction comparison

Source: blueprint `prop-coef-integral-dualizing`, proof paragraph 2;
Stacks Project, Tags 06YS, 0A95, 0A96, 07A6, 08J9 and 0941
(blueprint: lem-coef-hom-tower-scalar-model).

All sections retain the integral action and the strict tower index. The natural-number
index n denotes exponent n+1. Site and coefficient universes remain independent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u c v r d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open SheafOfModules
namespace WeilConjectures

/-- The canonical localization comparison: first use the actual replacement unit,
then the inverse factorization isomorphism of the defined derived Hom functor.
Source: Stacks 0A95 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomInternalComparison
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{d} (scalarModules J R)]
    (P I : CochainComplex (scalarModules J R) ℤ) :
    DerivedCategory.Q.obj (homComplex (R := R) P I) ⟶
      (derivedInternalHomOfUniverses.{c, v, r, d} J R).obj
        (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I) :=
  letI := (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
    J R).1
  DerivedCategory.Q.map
    (((homComplexFunctor (R := R)).obj (op P)).map
      ((CochainComplex.toKInjectiveResolution.{max c v r} _).app I)) ≫
    (coefficientHomResolutionIso.{r, c, v, d} J R P I).inv

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The constant completed ring on the same vertical sequence site.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
abbrev coefHomConstantRing :=
  systemSequenceRing.{t + 1, t, max u (t + 1)} (J := Scheme.ProEt.topology W)
    ((Functor.const ℕᵒᵖ).obj
    (completedIntegralCommRingSheafUnrestricted l E W))

/-- Constant-ring sequence modules; this is the recorded ringed-site module category.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
abbrev coefHomConstantModules :=
  scalarModules (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefHomConstantRing l E W)

/-- The standard localization of constant-ring sequence modules.
Source: Stacks 05RU, 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
instance coefHomConstantHasDerived : HasDerivedCategory (coefHomConstantModules l E W) :=
  HasDerivedCategory.standard _

/-- The coefficient-preserving category of strict R-module towers.
The lift only puts the coefficients in the universe of the site.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
abbrev coefHomPointModules :=
  ℕᵒᵖ ⥤ ModuleCat.{max u (t + 1)}
    (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))

/-- The ordinary derived category of strict point towers.
Source: Stacks 05RU, 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
instance coefHomPointHasDerived : HasDerivedCategory (coefHomPointModules.{t, u} l E) :=
  HasDerivedCategory.standard _

/-- The ordinary derived category of one point coefficient module.
Source: Stacks 05RU (blueprint: lem-coef-hom-tower-scalar-model). -/
instance coefHomFinitePointHasDerived :
    HasDerivedCategory (ModuleCat.{max u (t + 1)}
      (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))) :=
  HasDerivedCategory.standard _

/-- The actual constant integral action at the terminal pro-etale object.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomScalar : ULift.{t + 1} (Padic.coefficientExtensionIntegers l E) →+*
    (completedIntegralCoefficientSheafUnrestricted l E W).obj.obj
      (op (Scheme.ProEt.mk (𝟙 W))) :=
  (((integralConstantToCompletionOfUniverses l E W).hom.app
    (op (Scheme.ProEt.mk (𝟙 W)))).hom).comp
      (((forget₂ CommRingCat RingCat).map
        ((toSheafify (Scheme.ProEt.topology W)
          ((Functor.const W.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app
              (op (Scheme.ProEt.mk (𝟙 W))))).hom)

/-- Actual ordinary sections, retaining the R-module action.
Source: Stacks 08JA (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomSections : scalarReductionSource l E W ⥤
    ModuleCat.{max u (t + 1)} (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)) :=
  SheafOfModules.evaluation _ (op (Scheme.ProEt.mk (𝟙 W))) ⋙
    ModuleCat.restrictScalars (coefHomScalar l E W)

/-- Sections are additive because evaluation and restriction preserve addition.
Source: Stacks 08JA (blueprint: lem-coef-hom-tower-scalar-model). -/
instance coefHomSectionsAdditive : (coefHomSections l E W).Additive where
  map_add := rfl

/-- Sections on ordinary completed-module towers; there is no inverse limit.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomTowerSections :
    (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ coefHomPointModules.{t, u} l E :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (coefHomSections l E W)

/-- Additivity of sections on towers is componentwise.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
instance coefHomTowerSectionsAdditive : (coefHomTowerSections l E W).Additive :=
  inferInstanceAs ((Functor.whiskeringRight ℕᵒᵖ _ _).obj _).Additive

/-- The recorded simultaneous K-injectives on constant-ring towers.
Source: Stacks 079P (blueprint: lem-coef-hom-tower-scalar-model). -/
instance coefHomTowersKInjective :
    Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ scalarReductionSource l E W) :=
  coefficientConstantTowers_haveKInjectives.{t, u} l E W

/-- Derived tower sections: the target is D(Tow(Mod R)), before inverse limit.
Source: Stacks 079P, 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomDerivedTowerSections : coefficientSequenceRestrictedDerived l E W ⥤
    DerivedCategory (coefHomPointModules.{t, u} l E) :=
  (coefHomTowerSections l E W).rightDerivedFunctor

/-- Exact point-tower evaluation, with the same integral scalar action.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomPointEvaluation (n : ℕ) :
    DerivedCategory (coefHomPointModules.{t, u} l E) ⥤
      DerivedCategory (ModuleCat.{max u (t + 1)}
        (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))) :=
  ((evaluation ℕᵒᵖ _).obj (op n)).mapDerivedCategory

/-- The recorded section-preserving constant-sequence equivalence, in the full size.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomEquivalence : coefHomConstantModules l E W ≌
    (ℕᵒᵖ ⥤ scalarReductionSource l E W) :=
  ConstantCompletion.independentConstantSequenceEquivalence.{t + 1, t, u}
    (completedIntegralCommRingSheafUnrestricted l E W)

/-- Additivity of the section-preserving equivalence.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
instance coefHomEquivalenceAdditive : (coefHomEquivalence l E W).functor.Additive :=
  (ConstantCompletion.independentConstantSequenceEquivalence_additive.{t + 1, t, u}
    (completedIntegralCommRingSheafUnrestricted l E W)).1

/-- Additivity of the inverse section-preserving equivalence.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
instance coefHomEquivalenceInverseAdditive : (coefHomEquivalence l E W).inverse.Additive :=
  (ConstantCompletion.independentConstantSequenceEquivalence_additive.{t + 1, t, u}
    (completedIntegralCommRingSheafUnrestricted l E W)).2

/-- Actual constant towers, realized on the constant-ring sequence site.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomConstant : scalarReductionSource l E W ⥤ coefHomConstantModules l E W :=
  Functor.const ℕᵒᵖ ⋙ (coefHomEquivalence l E W).inverse

/-- Constant towers preserve addition of maps.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model).
Proof: the constant diagram adds maps componentwise, and the inverse of the recorded
additive section-preserving equivalence preserves their sum. -/
theorem coefHomConstant_additive : (coefHomConstant l E W).Additive := by
  have : (Functor.const ℕᵒᵖ : scalarReductionSource l E W ⥤ _).Additive :=
    ⟨fun {_ _} _ _ ↦ rfl⟩
  exact inferInstanceAs (Functor.const ℕᵒᵖ ⋙ (coefHomEquivalence l E W).inverse).Additive

/-- The additive witness for actual constant towers.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
instance coefHomConstantAdditive : (coefHomConstant l E W).Additive :=
  coefHomConstant_additive l E W

/-- Exactness of constant towers follows from pointwise kernels and cokernels.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model).
Proof: the constant-tower functor preserves kernels and cokernels componentwise,
and the recorded equivalence preserves all limits and colimits. -/
theorem coefHomConstant_exact : PreservesFiniteLimits (coefHomConstant l E W) ∧
    PreservesFiniteColimits (coefHomConstant l E W) := by
  change PreservesFiniteLimits (Functor.const ℕᵒᵖ ⋙ _) ∧
    PreservesFiniteColimits (Functor.const ℕᵒᵖ ⋙ _)
  exact ⟨inferInstance, inferInstance⟩

/-- Finite-limit preservation of the actual constant-tower functor.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
instance coefHomConstantLimits : PreservesFiniteLimits (coefHomConstant l E W) :=
  (coefHomConstant_exact l E W).1

/-- Finite-colimit preservation of the actual constant-tower functor.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
instance coefHomConstantColimits : PreservesFiniteColimits (coefHomConstant l E W) :=
  (coefHomConstant_exact l E W).2

/-- The exact derived constant-tower functor.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomDerivedConstant : DerivedCategory (scalarReductionSource l E W) ⥤
    DerivedCategory (coefHomConstantModules l E W) :=
  (coefHomConstant l E W).mapDerivedCategory

/-- The actual completion projections commute with every sequence-site restriction.
Source: Stacks 03CO, 0941 (blueprint: lem-coef-hom-tower-scalar-model).
Proof: vertical naturality is naturality of each completion projection; horizontal
naturality is the limit-cone identity for the actual quotient transitions. Every
arrow in the product site factors as a horizontal arrow and a vertical arrow. -/
theorem coefHomScalar_naturality {X Y : (ℕ × W.ProEt)ᵒᵖ} (f : X ⟶ Y) :
    (coefHomConstantRing l E W).obj.map f ≫
        (completedIntegralCommRingProjectionUnrestricted l E W Y.unop.1).hom.app
          (op Y.unop.2) =
      (completedIntegralCommRingProjectionUnrestricted l E W X.unop.1).hom.app
          (op X.unop.2) ≫ (coefficientSequenceCommRingSheaf l E W).obj.map f := by
  let π : (Functor.const ℕᵒᵖ).obj (completedIntegralCommRingSheafUnrestricted l E W) ⟶
      coefficientSequenceCommRingSystem l E W :=
    NatTrans.ofOpSequence (completedIntegralCommRingProjectionUnrestricted l E W)
      (fun n ↦ by
        simp only [Functor.const_obj_map, coefficientSequenceCommRingSystem,
          Functor.ofOpSequence_map_homOfLE_succ]
        apply (sheafCompose (Scheme.ProEt.topology W)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map_injective
        rw [Functor.map_comp]
        have h := limit.w (integralCoefficientSheafSystem l E W) (homOfLE n.le_succ).op
        simp only [integralCoefficientSheafSystem,
          Functor.ofOpSequence_map_homOfLE_succ] at h
        exact h.symm)
  exact (Functor.whiskerLeft (prodOpEquiv (C := ℕ) (D := W.ProEt)).functor
    (Functor.uncurry.map (Functor.whiskerRight π
      (sheafToPresheaf (Scheme.ProEt.topology W) CommRingCat)))).naturality f

/-- The sequence-site ring map is precisely the completion projection on each slice.
Source: Stacks 03CO, 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomScalarMap : coefHomConstantRing l E W ⟶ coefficientSequenceCommRingSheaf l E W :=
  ⟨{ app := fun X ↦
        (completedIntegralCommRingProjectionUnrestricted l E W X.unop.1).hom.app
          (op X.unop.2)
     naturality := fun _ _ f ↦ coefHomScalar_naturality l E W f }⟩

/-- Ordinary restriction along precisely the sequence completion-projection map.
Source: Stacks 07A6 (blueprint: lem-coef-hom-tower-scalar-model). -/
abbrev coefHomOrdinaryRestriction : coefficientSequenceModules l E W ⥤
    coefHomConstantModules l E W :=
  scalarRestriction.{t + 1, t, max u (t + 1)} (coefHomScalarMap l E W)

/-- Exact sequence-site scalar restriction and its ordinary localization.
Source: Stacks 07A6 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomDerivedRestriction : coefficientSequenceDerived l E W ⥤
    DerivedCategory (coefHomConstantModules l E W) :=
  scalarDerivedRestriction (coefHomScalarMap l E W)

/-- Ordinary sections on the constant-ring sequence site, realized as literal towers.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomConstantSections : coefHomConstantModules l E W ⥤
    coefHomPointModules.{t, u} l E :=
  (coefHomEquivalence l E W).functor ⋙ coefHomTowerSections l E W

/-- Sections preserve addition before deriving.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
instance coefHomConstantSectionsAdditive : (coefHomConstantSections l E W).Additive :=
  inferInstanceAs (_ ⋙ _).Additive

/-- Constant-ring sequence modules have the same simultaneous resolutions as towers.
Source: Stacks 079P (blueprint: lem-coef-hom-tower-scalar-model). -/
instance coefHomConstantKInjectives :
    Abelian.HasKInjectiveResolutions (coefHomConstantModules l E W) :=
  letI := (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t + 1, t, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefHomConstantRing l E W)).1
  inferInstance

/-- Total derived sections on the constant-ring sequence site, without inverse limit.
Source: Stacks 079P, 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomConstantDerivedSections : DerivedCategory (coefHomConstantModules l E W) ⥤
    DerivedCategory (coefHomPointModules.{t, u} l E) :=
  (coefHomConstantSections l E W).rightDerivedFunctor

/-- The recorded RHom on the constant-ring sequence site.
Source: Stacks 0A95 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomConstantInternalHom :=
  derivedInternalHomOfUniverses.{t + 1, t, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W)) (coefHomConstantRing l E W)

/-- The canonical derived Hom tower, before applying an inverse limit.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomTower :
    (DerivedCategory (scalarReductionSource l E W))ᵒᵖ ×
      coefficientSequenceDerived l E W ⥤ DerivedCategory (coefHomPointModules.{t, u} l E) :=
  ((coefHomDerivedConstant l E W).op.prod (coefHomDerivedRestriction l E W)) ⋙
    coefHomConstantInternalHom l E W ⋙ coefHomConstantDerivedSections l E W

/-- Reassembling a strict tower of complexes satisfies the complex identities.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model).
Proof: evaluate each equation at n. Shape and square-zero become the corresponding
axioms of the complex F(n); extensionality of natural transformations finishes. -/
theorem coefHomReassemble_axioms
    (F : ℕᵒᵖ ⥤ CochainComplex
      (ModuleCat.{max u (t + 1)} (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))) ℤ) :
    (∀ i j : ℤ, ¬ (ComplexShape.up ℤ).Rel i j →
      Functor.whiskerLeft F (HomologicalComplex.dNatTrans _ (.up ℤ) i j) = 0) ∧
    (∀ i j k : ℤ,
      Functor.whiskerLeft F (HomologicalComplex.dNatTrans _ (.up ℤ) i j) ≫
        Functor.whiskerLeft F (HomologicalComplex.dNatTrans _ (.up ℤ) j k) = 0) := by
  constructor
  · intro i j hij
    apply NatTrans.ext
    funext n
    exact (F.obj n).shape i j hij
  · intro i j k
    apply NatTrans.ext
    funext n
    exact (F.obj n).d_comp_d i j k

/-- The actual signed global Hom complex at every level, with postcomposition transitions.
Source: Stacks 0A8Z, 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomStrictComplex
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
    CochainComplex (coefHomPointModules.{t, u} l E) ℤ :=
  { X := fun i ↦ (I.asFunctor ⋙
      (homComplexFunctor (R := completedIntegralCommRingSheafUnrestricted l E W)).obj
        (op P) ⋙ (coefHomSections l E W).mapHomologicalComplex (.up ℤ)) ⋙
          HomologicalComplex.eval _ (.up ℤ) i
    d := fun i j ↦ Functor.whiskerLeft (I.asFunctor ⋙
      (homComplexFunctor (R := completedIntegralCommRingSheafUnrestricted l E W)).obj
        (op P) ⋙ (coefHomSections l E W).mapHomologicalComplex (.up ℤ))
          (HomologicalComplex.dNatTrans _ (.up ℤ) i j)
    shape := (coefHomReassemble_axioms l E _).1
    d_comp_d' := fun i j k _ _ ↦ (coefHomReassemble_axioms l E _).2 i j k }

/-- The actual quotient rings on the one-point sequence topos, at exponent n+1.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomPointQuotientRing : ℕᵒᵖ ⥤ RingCat.{max u (t + 1)} :=
  Functor.ofOpSequence (X := fun n ↦
    RingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))
    (fun n ↦ RingCat.ofHom
      ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
        ((Padic.coefficientExtensionTransition l E (n + 1)).comp
          (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom)))

/-- The ordinary module category on the one-point quotient sequence topos.
The topology on ℕ is the trivial one, so its module sheaves are module presheaves.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
abbrev coefHomQuotientPointModules :=
  PresheafOfModules.{max u (t + 1)} (coefHomPointQuotientRing.{t, u} l E)

/-- Standard localization of quotient-semilinear point towers.
Source: Stacks 05RU (blueprint: lem-coef-hom-tower-scalar-model). -/
instance coefHomQuotientPointHasDerived :
    HasDerivedCategory (coefHomQuotientPointModules.{t, u} l E) :=
  HasDerivedCategory.standard _

/-- The constant ring on the one-point sequence site.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomPointConstantRing : ℕᵒᵖ ⥤ RingCat.{max u (t + 1)} :=
  (Functor.const ℕᵒᵖ).obj (RingCat.of
    (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)))

/-- The actual quotient maps from integral scalars on the point sequence.
Source: Stacks 07A6, 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomPointScalarComponent (n : ℕ) :
    (coefHomPointConstantRing.{t, u} l E).obj (op n) ⟶
      (coefHomPointQuotientRing.{t, u} l E).obj (op n) :=
  RingCat.ofHom ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
    ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
      (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom))

/-- The point quotient maps are compatible with every transition.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model).
Proof: quotient induction proves compatibility for a consecutive arrow, since both
composites are the quotient map at exponent n+1. Every arrow is a composite of
consecutive arrows, so functoriality gives compatibility in general. -/
theorem coefHomPointScalar_naturality {m n : ℕᵒᵖ} (f : m ⟶ n) :
    (coefHomPointConstantRing.{t, u} l E).map f ≫ coefHomPointScalarComponent l E n.unop =
      coefHomPointScalarComponent l E m.unop ≫
        (coefHomPointQuotientRing.{t, u} l E).map f := by
  have hstep (k : ℕ) :
      (coefHomPointConstantRing.{t, u} l E).map (homOfLE (Nat.le_succ k)).op ≫
          coefHomPointScalarComponent l E k =
        coefHomPointScalarComponent l E (k + 1) ≫
          (coefHomPointQuotientRing.{t, u} l E).map (homOfLE (Nat.le_succ k)).op := by
    simp only [coefHomPointConstantRing, Functor.const_obj_map,
      coefHomPointQuotientRing, Functor.ofOpSequence_map_homOfLE_succ]
    ext x
    rfl
  exact (NatTrans.ofOpSequence (coefHomPointScalarComponent.{t, u} l E) hstep).naturality f

/-- The scalar map rho_0, with actual quotient components.
Source: Stacks 07A6 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomPointScalarMap :
    coefHomPointConstantRing.{t, u} l E ⟶ coefHomPointQuotientRing.{t, u} l E where
  app n := coefHomPointScalarComponent l E n.unop
  naturality _ _ f := coefHomPointScalar_naturality l E f

/-- A module presheaf over the constant point ring is literally an R-module tower.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomPointConstantToTower :
    PresheafOfModules.{max u (t + 1)} (coefHomPointConstantRing.{t, u} l E) ⥤
      coefHomPointModules.{t, u} l E where
  obj M :=
    { obj n := M.obj n
      map f := ModuleCat.ofHom
        { toFun := M.map f
          map_add' := map_add _
          map_smul' := fun r x ↦ M.map_smul f r x }
      map_id n := by ext x; exact ConcreteCategory.congr_hom (M.map_id n) x
      map_comp f g := by ext x; exact M.map_comp_apply f g x }
  map f :=
    { app n := f.app n
      naturality := fun _ _ g ↦ by ext x; exact PresheafOfModules.naturality_apply f g x }
  map_id M := rfl
  map_comp f g := rfl

/-- Integral restriction on quotient-semilinear point towers.
Source: Stacks 07A6 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomPointRestriction : coefHomQuotientPointModules.{t, u} l E ⥤
    coefHomPointModules.{t, u} l E :=
  PresheafOfModules.restrictScalars (coefHomPointScalarMap.{t, u} l E) ⋙
    coefHomPointConstantToTower l E

/-- Integral restriction is additive and exact on point towers.
Source: Stacks 07A6, 0941 (blueprint: lem-coef-hom-tower-scalar-model).
Proof: both actions are related by the actual quotient homomorphisms, and restriction
keeps all underlying abelian groups and maps. Kernels and cokernels in these diagram
module categories are computed on components, so their underlying groups are unchanged. -/
theorem coefHomPointRestriction_exact : (coefHomPointRestriction.{t, u} l E).Additive ∧
    PreservesFiniteLimits (coefHomPointRestriction.{t, u} l E) ∧
    PreservesFiniteColimits (coefHomPointRestriction.{t, u} l E) := by
  refine ⟨⟨?_⟩, ?_, ⟨?_⟩⟩
  · intro M N f g
    rfl
  · apply preservesFiniteLimits_of_evaluation
    intro n
    change PreservesFiniteLimits
      (PresheafOfModules.evaluation (coefHomPointQuotientRing.{t, u} l E) n ⋙
        ModuleCat.restrictScalars (coefHomPointScalarComponent l E n.unop).hom)
    let U := forget₂
      (ModuleCat.{max u (t + 1)}
        (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))) AddCommGrpCat
    have : PreservesFiniteLimits
        ((PresheafOfModules.evaluation (coefHomPointQuotientRing.{t, u} l E) n ⋙
          ModuleCat.restrictScalars (coefHomPointScalarComponent l E n.unop).hom) ⋙ U) :=
      inferInstanceAs (PreservesFiniteLimits
        (PresheafOfModules.evaluation (coefHomPointQuotientRing.{t, u} l E) n ⋙
          forget₂ (ModuleCat _) AddCommGrpCat))
    exact preservesFiniteLimits_of_reflects_of_preserves _ U
  · intro J _ _
    apply preservesColimitsOfShape_of_evaluation
    intro n
    change PreservesColimitsOfShape J
      (PresheafOfModules.evaluation (coefHomPointQuotientRing.{t, u} l E) n ⋙
        ModuleCat.restrictScalars (coefHomPointScalarComponent l E n.unop).hom)
    infer_instance

/-- Additivity of the actual point restriction.
Source: Stacks 07A6 (blueprint: lem-coef-hom-tower-scalar-model). -/
instance coefHomPointRestrictionAdditive : (coefHomPointRestriction.{t, u} l E).Additive :=
  (coefHomPointRestriction_exact l E).1

/-- Left exactness of the actual point restriction.
Source: Stacks 07A6 (blueprint: lem-coef-hom-tower-scalar-model). -/
instance coefHomPointRestrictionLimits :
    PreservesFiniteLimits (coefHomPointRestriction.{t, u} l E) :=
  (coefHomPointRestriction_exact l E).2.1

/-- Right exactness of the actual point restriction.
Source: Stacks 07A6 (blueprint: lem-coef-hom-tower-scalar-model). -/
instance coefHomPointRestrictionColimits :
    PreservesFiniteColimits (coefHomPointRestriction.{t, u} l E) :=
  (coefHomPointRestriction_exact l E).2.2

/-- Exact localization of rho_0 restriction.
Source: Stacks 07A6 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomPointDerivedRestriction :
    DerivedCategory (coefHomQuotientPointModules.{t, u} l E) ⥤
      DerivedCategory (coefHomPointModules.{t, u} l E) :=
  (coefHomPointRestriction l E).mapDerivedCategory

/-- The terminal-object section functor on the underlying sequence site.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomSectionIndex : ℕ ⥤ ℕ × W.ProEt where
  obj n := (n, Scheme.ProEt.mk (𝟙 W))
  map f := Prod.mkHom f (𝟙 _)
  map_id _n := rfl
  map_comp _f _g := rfl

/-- Constant quotient coefficients map to their actual global sections by sheafification.
Source: Stacks 03DA, 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomQuotientSectionScalarComponent (n : ℕ) :
    (coefHomPointQuotientRing.{t, u} l E).obj (op n) ⟶
      (forget₂ CommRingCat RingCat).obj
        ((coefficientSequenceCommRingSheaf l E W).obj.obj
          (op (n, Scheme.ProEt.mk (𝟙 W)))) :=
  (forget₂ CommRingCat RingCat).map
    ((toSheafify (Scheme.ProEt.topology W)
      ((Functor.const W.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app
          (op (Scheme.ProEt.mk (𝟙 W))))

/-- Global constant quotient sections respect all sequence transitions.
Source: Stacks 03DA, 0941 (blueprint: lem-coef-hom-tower-scalar-model).
Proof: naturality of the sheafification unit gives the equation for a consecutive
quotient map; the identity and composition laws give it for every sequence arrow. -/
theorem coefHomQuotientSectionScalar_naturality {m n : ℕᵒᵖ} (f : m ⟶ n) :
    (coefHomPointQuotientRing.{t, u} l E).map f ≫
        coefHomQuotientSectionScalarComponent l E W n.unop =
      coefHomQuotientSectionScalarComponent l E W m.unop ≫
        (forget₂ CommRingCat RingCat).map
          ((coefficientSequenceCommRingSheaf l E W).obj.map
            ((coefHomSectionIndex W).op.map f)) := by
  have hstep (k : ℕ) :
      (coefHomPointQuotientRing.{t, u} l E).map (homOfLE (Nat.le_succ k)).op ≫
          coefHomQuotientSectionScalarComponent l E W k =
        coefHomQuotientSectionScalarComponent l E W (k + 1) ≫
          (forget₂ CommRingCat RingCat).map
            ((coefficientSequenceCommRingSheaf l E W).obj.map
              ((coefHomSectionIndex W).op.map (homOfLE (Nat.le_succ k)).op)) := by
    let q : CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (k + 2))) ⟶
        CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (k + 1))) :=
      CommRingCat.ofHom ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
        ((Padic.coefficientExtensionTransition l E (k + 1)).comp
          (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom))
    have hq := toSheafify_naturality (Scheme.ProEt.topology W)
      ((Functor.const W.ProEtᵒᵖ).map q)
    have hqa := congrArg (fun z ↦
      (forget₂ CommRingCat RingCat).map (z.app (op (Scheme.ProEt.mk (𝟙 W))))) hq
    simp only [NatTrans.comp_app, Functor.map_comp, Functor.const_map_app] at hqa
    change (forget₂ CommRingCat RingCat).map q ≫ _ = _ at hqa
    simp only [coefHomPointQuotientRing, Functor.ofOpSequence_map_homOfLE_succ]
    change (forget₂ CommRingCat RingCat).map q ≫ _ = _
    convert hqa using 1
    · rfl
    · rfl
    · change _ ≫ (forget₂ CommRingCat RingCat).map
        (((coefficientSequenceCommRingSystem l E W).map
            (homOfLE (Nat.le_succ k)).op).hom.app
              (op (Scheme.ProEt.mk (𝟙 W))) ≫
          ((coefficientSequenceCommRingSystem l E W).obj (op k)).obj.map
            (𝟙 (op (Scheme.ProEt.mk (𝟙 W))))) = _
      dsimp only [coefHomQuotientSectionScalarComponent]
      simp only [CategoryTheory.Functor.map_id, Category.comp_id]
      simp only [coefficientSequenceCommRingSystem,
        Functor.ofOpSequence_map_homOfLE_succ]
      rfl
  exact (NatTrans.ofOpSequence
    (F := coefHomPointQuotientRing.{t, u} l E)
    (G := (coefHomSectionIndex W).op ⋙
      (coefficientSequenceCommRingSheaf l E W).obj ⋙ forget₂ CommRingCat RingCat)
    (coefHomQuotientSectionScalarComponent.{t, u} l E W) hstep).naturality f

/-- The structural ring map for quotient-linear global sections.
Source: Stacks 03DA, 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomQuotientSectionScalar : coefHomPointQuotientRing.{t, u} l E ⟶
    (coefHomSectionIndex W).op ⋙
      (coefficientSequenceCommRingSheaf l E W).obj ⋙ forget₂ CommRingCat RingCat where
  app n := coefHomQuotientSectionScalarComponent l E W n.unop
  naturality _ _ f := coefHomQuotientSectionScalar_naturality l E W f

/-- Actual quotient-linear sections, retaining the whole semilinear point tower.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomQuotientSections : coefficientSequenceModules l E W ⥤
    coefHomQuotientPointModules.{t, u} l E :=
  SheafOfModules.forget _ ⋙ PresheafOfModules.pushforward
    (coefHomQuotientSectionScalar l E W)

/-- Additivity of the actual quotient-linear sections.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model).
Proof: evaluation on every component and scalar restriction preserve sums of maps. -/
theorem coefHomQuotientSections_additive : (coefHomQuotientSections l E W).Additive := by
  constructor
  intro M N f g
  rfl

/-- The additive structure on quotient-linear sections.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
instance coefHomQuotientSectionsAdditive : (coefHomQuotientSections l E W).Additive :=
  coefHomQuotientSections_additive l E W

/-- The sequence ringed site admits simultaneous K-injective resolutions.
Source: Stacks 079P (blueprint: lem-coef-hom-tower-scalar-model). -/
instance coefHomQuotientKInjectives :
    Abelian.HasKInjectiveResolutions (coefficientSequenceModules l E W) :=
  letI := (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t + 1, t, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)).1
  inferInstance

/-- Total quotient-linear sections, without inverse limit.
Source: Stacks 079P, 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomQuotientDerivedSections : coefficientSequenceDerived l E W ⥤
    DerivedCategory (coefHomQuotientPointModules.{t, u} l E) :=
  (coefHomQuotientSections l E W).rightDerivedFunctor

/-- The quotient-linear derived section complex followed by exact integral restriction.
Source: Stacks 07A6, 0D6E (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomRestrictedQuotientSections : coefficientSequenceDerived l E W ⥤
    DerivedCategory (coefHomPointModules.{t, u} l E) :=
  coefHomQuotientDerivedSections l E W ⋙ coefHomPointDerivedRestriction l E

/-- The actual quotient-scalar Hom tower, whose target retains the integral action.
Source: Stacks 07A6, 08J9 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomScalarTower
    (S : ScalarHomModels.{t + 1, t, u, max (t + 2) (u + 1)}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))) :
    (DerivedCategory (scalarReductionSource l E W))ᵒᵖ ×
      coefficientSequenceDerived l E W ⥤ DerivedCategory (coefHomPointModules.{t, u} l E) :=
  (((coefHomDerivedConstant l E W ⋙
      (S.scalar (coefHomScalarMap l E W)).derived).op).prod (𝟭 _)) ⋙
    coefficientSequenceInternalHom l E W ⋙ coefHomRestrictedQuotientSections l E W

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The actual ordinary-section square commutes by identity on underlying sections.
Source: Stacks 07A6, 0941 (blueprint: lem-coef-hom-tower-scalar-model).
Proof: both composites evaluate M at (n,W); their integral scalar action is the
completion projection followed by the constant integral map. The limit-cone
identity says this is exactly the finite quotient of that constant map. The
section-preserving sequence equivalence retains all section objects and maps,
so identity on each section defines the required isomorphism, uniquely. -/
theorem coefHomOrdinaryFactorization_exists :
    ∃! γ : coefHomQuotientSections l E W ⋙ coefHomPointRestriction l E ≅
        coefHomOrdinaryRestriction l E W ⋙ coefHomConstantSections l E W,
      ∀ (M : coefficientSequenceModules l E W) (n : ℕ)
        (x : (((coefHomQuotientSections l E W ⋙ coefHomPointRestriction l E).obj M).obj
          (op n))), HEq (((γ.hom.app M).app (op n)) x) x := by
  sorry

/-- The uniquely section-normalized ordinary square.
Source: Stacks 07A6, 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomOrdinaryFactorization :
    coefHomQuotientSections l E W ⋙ coefHomPointRestriction l E ≅
      coefHomOrdinaryRestriction l E W ⋙ coefHomConstantSections l E W :=
  (coefHomOrdinaryFactorization_exists l E W).choose

/-- The same identity section square on actual complexes, with all composition transports.
Source: Stacks 07A6, 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomFactorizationComplexIso (L : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    ((coefHomPointRestriction l E).mapHomologicalComplex (.up ℤ)).obj
        (((coefHomQuotientSections l E W).mapHomologicalComplex (.up ℤ)).obj L) ≅
      ((coefHomConstantSections l E W).mapHomologicalComplex (.up ℤ)).obj
        (((coefHomOrdinaryRestriction l E W).mapHomologicalComplex (.up ℤ)).obj L) :=
  (NatIso.mapHomologicalComplex (coefHomOrdinaryFactorization l E W) (.up ℤ)).app L

/-- The universal-comparison equation that fixes the derived section square.
Source: Stacks 0D6E (blueprint: lem-coef-hom-tower-scalar-model). -/
def CoefHomDerivedFactorizationNormalization
    (κ : coefHomRestrictedQuotientSections l E W ≅
      coefHomDerivedRestriction l E W ⋙ coefHomConstantDerivedSections l E W) : Prop :=
  ∀ L : CochainComplex (coefficientSequenceModules l E W) ℤ,
    (coefHomPointRestriction l E).mapDerivedCategoryFactors.inv.app
        (((coefHomQuotientSections l E W).mapHomologicalComplex (.up ℤ)).obj L) ≫
      (coefHomPointDerivedRestriction l E).map
        (coefficientRightDerivedComparison (coefHomQuotientSections l E W) L) ≫
      κ.hom.app (DerivedCategory.Q.obj L) =
    DerivedCategory.Q.map (coefHomFactorizationComplexIso l E W L).hom ≫
      coefficientRightDerivedComparison (coefHomConstantSections l E W)
        (((coefHomOrdinaryRestriction l E W).mapHomologicalComplex (.up ℤ)).obj
          L) ≫
      (coefHomConstantDerivedSections l E W).map
        ((coefHomOrdinaryRestriction l E W).mapDerivedCategoryFactors.inv.app L)

/-- The canonical derived composition comparison, fixed by its universal units.
Source: Stacks 0D6E (blueprint: lem-coef-hom-tower-scalar-model).
Proof: the ordinary square is the identity on sections. Derive it in two ways.
Exact restriction at the point commutes with right derivation; on the site,
the normalized ringed-topos derived-pushforward composition theorem applies.
Its acyclicity statement compares the section direct images of the two resolutions;
it does not require scalar restriction to preserve K-injectives. The universal
units give the displayed equality on every complex. The right-derived universal
property determines the comparison uniquely;
the K-injective calculation proves it is invertible. -/
theorem coefHomDerivedFactorization_exists :
    ∃! κ : coefHomRestrictedQuotientSections l E W ≅
        coefHomDerivedRestriction l E W ⋙ coefHomConstantDerivedSections l E W,
      CoefHomDerivedFactorizationNormalization l E W κ := by
  sorry

/-- The derived square uniquely normalized by its universal comparison on complexes.
Source: Stacks 0D6E (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomDerivedFactorization :
    coefHomRestrictedQuotientSections l E W ≅
      coefHomDerivedRestriction l E W ⋙ coefHomConstantDerivedSections l E W :=
  (coefHomDerivedFactorization_exists l E W).choose

/-- Derived global sections with integral coefficients and their actual scalar action.
Source: Stacks 08JA (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomDerivedSections : DerivedCategory (scalarReductionSource l E W) ⥤
    DerivedCategory (ModuleCat.{max u (t + 1)}
      (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))) :=
  letI := (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t + 1, t, u}
    (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W)).1
  (coefHomSections l E W).rightDerivedFunctor

/-- The finite restricted global Hom, as a whole object of D(R).
Source: Stacks 08JA (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomFiniteIntegral (n : ℕ) :
    (DerivedCategory (scalarReductionSource l E W))ᵒᵖ ×
      coefficientSequenceDerived l E W ⥤
        DerivedCategory (ModuleCat.{max u (t + 1)}
          (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))) :=
  ((𝟭 _).prod (coefficientSequenceDerivedEvaluation l E W n ⋙
    coefficientFiniteDerivedRestriction l E W n)) ⋙
      coefficientIntegralInternalHom l E W ⋙ coefHomDerivedSections l E W

/-- Finite quotient-linear Hom followed by scalar restriction and integral sections.
The ringed-topos composition comparison identifies this with restricted
quotient-linear derived sections, as a whole integral-coefficient complex.
Source: Stacks 07A6, 08JA (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomFiniteQuotient
    (S : ScalarHomModels.{t + 1, t, u, max (t + 2) (u + 1)} (Scheme.ProEt.topology W))
    (n : ℕ) :
    (DerivedCategory (scalarReductionSource l E W))ᵒᵖ ×
      coefficientSequenceDerived l E W ⥤
        DerivedCategory (ModuleCat.{max u (t + 1)}
          (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))) :=
  (((S.scalar (completedIntegralCommRingProjectionUnrestricted l E W n)).derived.op).prod
    (coefficientSequenceDerivedEvaluation l E W n)) ⋙
      coefficientFiniteInternalHom l E W n ⋙ coefficientFiniteDerivedRestriction l E W n ⋙
        coefHomDerivedSections l E W

/-- The finite scalar extension is the recorded K_n construction, by the unique
unit-compatible comparison of left adjoints to the same actual restriction functor.
Source: Stacks 06YY, 07A6 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomFiniteExtensionIso
    (F : ScalarHomModels.{t + 1, t, u, max (t + 2) (u + 1)} (Scheme.ProEt.topology W))
    (n : ℕ) :
    (F.scalar (completedIntegralCommRingProjectionUnrestricted l E W n)).derived ≅
      coefficientFiniteDerivedExtension l E W n :=
  Adjunction.leftAdjointUniq
    (F.scalar (completedIntegralCommRingProjectionUnrestricted l E W n)).adjunction
    (coefficientFiniteAdjunction l E W n)

/-- The constant-ring sequence complex of a simultaneous tower resolution.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomSequenceComplex
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
    CochainComplex (coefHomConstantModules l E W) ℤ :=
  ((coefHomEquivalence l E W).inverse.mapHomologicalComplex (.up ℤ)).obj I

/-- The actual sheaf Hom complex on the constant-ring sequence site.
Source: Stacks 0A8X, 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomSequenceHomComplex
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
    CochainComplex (coefHomConstantModules l E W) ℤ :=
  homComplex (R := coefHomConstantRing l E W)
    (((coefHomConstant l E W).mapHomologicalComplex (.up ℤ)).obj P)
    (coefHomSequenceComplex l E W I)

/-- Actual un-derived sections of the sequence-site sheaf Hom complex.
Source: Stacks 0A8Z, 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomSequenceSectionComplex
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
    CochainComplex (coefHomPointModules.{t, u} l E) ℤ :=
  ((coefHomConstantSections l E W).mapHomologicalComplex (.up ℤ)).obj
    (coefHomSequenceHomComplex l E W P I)

/-- Componentwise normalization of the slice identification. At (n,U), restrict the
slice morphism to the same terminal index n; its earlier components are forced by
postcomposition with the transitions. The product index p is retained in every degree.
Source: Stacks 04TT, 0A8X, 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def CoefHomSliceNormalization
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (ε : coefHomSequenceSectionComplex l E W P I ≅ coefHomStrictComplex l E W P I) : Prop :=
  ∀ (i p : ℤ) (n : ℕ) (U : W.ProEt)
    (f : U ⟶ Scheme.ProEt.mk (𝟙 W))
    (x : ((coefHomSequenceSectionComplex l E W P I).X i).obj (op n)),
    HEq
      ((((coefficientHomComponent.{u, t + 1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)
        P (I.asFunctor.obj (op n)) i p (p + i) rfl).val.app
          (op (Scheme.ProEt.mk (𝟙 W))))
        (((ε.hom.f i).app (op n)) x)).app (op (Over.mk f)))
      ((((coefficientHomComponent.{u, t + 1, t}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefHomConstantRing l E W)
        (((coefHomConstant l E W).mapHomologicalComplex (.up ℤ)).obj P)
        (coefHomSequenceComplex l E W I) i p (p + i) rfl).val.app
          (op (n, Scheme.ProEt.mk (𝟙 W)))) x).app
            (op (Over.mk (Prod.mkHom (𝟙 n) f))))

/-- The slice Hom identification, including the actual differentials and transitions.
Source: Stacks 04TT, 0A8X, 0A8Z, 0941
(blueprint: lem-coef-hom-tower-scalar-model).
Proof: on the sequence slice ending at (n,U), a map out of a constant source is
determined by its component at n; all earlier components are postcompositions with
the target transitions. Restriction to the terminal index and this reconstruction
are inverse. Apply this in each factor of the degree-r product. The differential
on both sides is d_I f - (-1)^r f d_P, so the factorwise identification is a chain
isomorphism. Vertical restriction commutes with the formula, and horizontal
restriction is precisely postcomposition. Apply global sections retaining scalars. -/
theorem coefHomSequenceSections_iso
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
    ∃! ε : coefHomSequenceSectionComplex l E W P I ≅ coefHomStrictComplex l E W P I,
      CoefHomSliceNormalization l E W P I ε := by
  sorry

/-- The uniquely slice-normalized complex isomorphism.
Source: Stacks 04TT, 0A8X (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomSequenceSectionsIso
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
    coefHomSequenceSectionComplex l E W P I ≅ coefHomStrictComplex l E W P I :=
  (coefHomSequenceSections_iso l E W P I).choose

/-- The canonical representative map: the universal sections comparison followed by
sections of the replacement-normalized internal Hom comparison, transported by eP,eI.
Source: Stacks 0A95, 0A96 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomRepresentativeMap
    (K : DerivedCategory (scalarReductionSource l E W))
    (N : coefficientSequenceDerived l E W)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ K)
    (eI : DerivedCategory.Q.obj (coefHomSequenceComplex l E W I) ≅
      (coefHomDerivedRestriction l E W).obj N) :
    DerivedCategory.Q.obj (coefHomSequenceSectionComplex l E W P I) ⟶
      (coefHomTower l E W).obj (op K, N) :=
  coefficientRightDerivedComparison (coefHomConstantSections l E W)
      (coefHomSequenceHomComplex l E W P I) ≫
    (coefHomConstantDerivedSections l E W).map
      (coefHomInternalComparison.{t + 1, t, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology W)) (coefHomConstantRing l E W)
        (((coefHomConstant l E W).mapHomologicalComplex (.up ℤ)).obj P)
        (coefHomSequenceComplex l E W I) ≫
      (coefHomConstantInternalHom l E W).map
        (Prod.mkHom
          (((coefHomDerivedConstant l E W).map eP.inv ≫
            (coefHomConstant l E W).mapDerivedCategoryFactors.hom.app P).op)
          eI.hom))

/-- The actual Hom representative computes the canonical derived Hom tower.
Source: Stacks 0A95, 0A96, 0941
(blueprint: lem-coef-hom-tower-scalar-model).
Proof: the constant complex of P is K-flat with flat terms by the levelwise tensor
and exactness tests. The constant-ring sequence equivalence carries the simultaneous
K-injective tower I to a K-injective sequence-site complex; evaluation also keeps
each I_n K-injective. The recorded derived-Hom comparison identifies the localization
of Hom(const P,I) with RHom(V,rho_*N). K-flat into K-injective Hom is K-injective,
so its un-derived section complex computes the total right derived sections.
The slice isomorphism identifies it with the signed strict global Hom tower.
Transport along eP and eI. This works for every choice of those representatives,
including unbounded ones, since Hom preserves the requisite quasi-isomorphisms. -/
theorem coefHomTower_representative
    (K : DerivedCategory (scalarReductionSource l E W))
    (N : coefficientSequenceDerived l E W)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (_hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E W) P)
    (_hflat : ∀ i : ℤ,
      IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
        (J := Scheme.ProEt.topology W)
        (R := completedIntegralCommRingSheafUnrestricted l E W) (P.X i))
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) [I.IsKInjective]
    (eP : DerivedCategory.Q.obj P ≅ K)
    (eI : DerivedCategory.Q.obj (coefHomSequenceComplex l E W I) ≅
      (coefHomDerivedRestriction l E W).obj N) :
    (coefHomSequenceHomComplex l E W P I).IsKInjective ∧
      (∃ η : DerivedCategory.Q.obj (coefHomStrictComplex l E W P I) ≅
          (coefHomTower l E W).obj (op K, N),
        η.hom = DerivedCategory.Q.map (coefHomSequenceSectionsIso l E W P I).inv ≫
          coefHomRepresentativeMap l E W K N P I eP eI) ∧
      (∃ θ : DerivedCategory.Q.obj (coefHomSequenceSectionComplex l E W P I) ≅
          (coefHomTower l E W).obj (op K, N),
        θ.hom = coefHomRepresentativeMap l E W K N P I eP eI) := by
  sorry

/-- The exact nth level of the constructed constant-ring equivalence.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomLevel (n : ℕ) : coefHomConstantModules l E W ⥤ scalarReductionSource l E W :=
  (coefHomEquivalence l E W).functor ⋙ (evaluation ℕᵒᵖ _).obj (op n)

/-- Level evaluation preserves addition through the constructed equivalence.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
instance coefHomLevelAdditive (n : ℕ) : (coefHomLevel l E W n).Additive :=
  inferInstanceAs (_ ⋙ _).Additive

/-- Exactness of the constructed level functor.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model).
Proof: the equivalence preserves all limits and colimits. Tower evaluation computes
kernels and cokernels pointwise, so the composite preserves finite limits and colimits. -/
theorem coefHomLevel_exact (n : ℕ) :
    PreservesFiniteLimits (coefHomLevel l E W n) ∧
      PreservesFiniteColimits (coefHomLevel l E W n) := by
  change PreservesFiniteLimits (_ ⋙ (evaluation ℕᵒᵖ _).obj (op n)) ∧
    PreservesFiniteColimits (_ ⋙ (evaluation ℕᵒᵖ _).obj (op n))
  exact ⟨inferInstance, inferInstance⟩

/-- The finite-limit witness for level evaluation.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
instance coefHomLevelLimits (n : ℕ) : PreservesFiniteLimits (coefHomLevel l E W n) :=
  (coefHomLevel_exact l E W n).1

/-- The finite-colimit witness for level evaluation.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
instance coefHomLevelColimits (n : ℕ) : PreservesFiniteColimits (coefHomLevel l E W n) :=
  (coefHomLevel_exact l E W n).2

/-- The ordinary restricted evaluation is fixed by identity on every section.
Source: Stacks 07A6, 0941 (blueprint: lem-coef-hom-tower-scalar-model).
Proof: both paths evaluate the quotient module at (n,U), then restrict along
R_W(U) to A_n(U). The constructed equivalence keeps those actual sections;
identity maps are linear, natural and uniquely determined by this formula. -/
theorem coefHomLevelRestriction_exists (n : ℕ) :
    ∃! δ : coefHomOrdinaryRestriction l E W ⋙ coefHomLevel l E W n ≅
        coefficientSequenceEvaluation l E W n ⋙ scalarReductionRestriction l E W n,
      ∀ (M : coefficientSequenceModules l E W) (U : W.ProEtᵒᵖ)
        (x : ((coefHomOrdinaryRestriction l E W ⋙ coefHomLevel l E W n).obj M).val.obj U),
        HEq ((δ.hom.app M).val.app U x) x := by
  sorry

/-- Section-normalized ordinary restricted evaluation.
Source: Stacks 07A6, 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomLevelRestriction (n : ℕ) :
    coefHomOrdinaryRestriction l E W ⋙ coefHomLevel l E W n ≅
      coefficientSequenceEvaluation l E W n ⋙ scalarReductionRestriction l E W n :=
  (coefHomLevelRestriction_exists l E W n).choose

/-- Exact localization of the section-normalized restricted evaluation square.
Source: Stacks 07A6, 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomDerivedLevelRestriction (n : ℕ) :
    coefHomDerivedRestriction l E W ⋙ (coefHomLevel l E W n).mapDerivedCategory ≅
      coefficientSequenceDerivedEvaluation l E W n ⋙ coefficientFiniteDerivedRestriction l E W n :=
  (Functor.mapDerivedCategoryCompIso (coefHomOrdinaryRestriction l E W)
    (coefHomLevel l E W n)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (coefHomLevelRestriction l E W n) ≪≫
    Functor.mapDerivedCategoryCompIso (coefficientSequenceEvaluation l E W n)
      (scalarReductionRestriction l E W n)

/-- Applying the explicit inverse and then evaluating returns I_n, by the counit.
Source: Stacks 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomLevelComplexIso
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) (n : ℕ) :
    ((coefHomLevel l E W n).mapHomologicalComplex (.up ℤ)).obj
      (coefHomSequenceComplex l E W I) ≅ I.asFunctor.obj (op n) :=
  (((evaluation ℕᵒᵖ _).obj (op n)).mapHomologicalComplex (.up ℤ)).mapIso
    ((NatIso.mapHomologicalComplex (coefHomEquivalence l E W).counitIso (.up ℤ)).app I)

/-- The actual finite representative of restricted N_n, transported by its scalar square.
Source: Stacks 07A6, 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomFiniteTargetMap
    (N : coefficientSequenceDerived l E W)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (eI : DerivedCategory.Q.obj (coefHomSequenceComplex l E W I) ≅
      (coefHomDerivedRestriction l E W).obj N) (n : ℕ) :
    DerivedCategory.Q.obj (I.asFunctor.obj (op n)) ⟶
      (coefficientFiniteDerivedRestriction l E W n).obj
        ((coefficientSequenceDerivedEvaluation l E W n).obj N) :=
  DerivedCategory.Q.map (coefHomLevelComplexIso l E W I n).inv ≫
    (coefHomLevel l E W n).mapDerivedCategoryFactors.inv.app
      (coefHomSequenceComplex l E W I) ≫
    (coefHomLevel l E W n).mapDerivedCategory.map eI.hom ≫
    (coefHomDerivedLevelRestriction l E W n).hom.app N

/-- The finite representative map uses the same replacement-normalized internal Hom
and the actual universal sections comparison, with eP and the restricted eI.
Source: Stacks 0A95, 0A96 (blueprint: lem-coef-hom-tower-scalar-model). -/
def coefHomFiniteRepresentativeMap
    (K : DerivedCategory (scalarReductionSource l E W))
    (N : coefficientSequenceDerived l E W)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ K)
    (eI : DerivedCategory.Q.obj (coefHomSequenceComplex l E W I) ≅
      (coefHomDerivedRestriction l E W).obj N) (n : ℕ) :
    DerivedCategory.Q.obj (((coefHomSections l E W).mapHomologicalComplex (.up ℤ)).obj
      (homComplex (R := completedIntegralCommRingSheafUnrestricted l E W)
        P (I.asFunctor.obj (op n)))) ⟶ (coefHomFiniteIntegral l E W n).obj (op K, N) :=
  letI := (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t + 1, t, u}
    (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W)).1
  coefficientRightDerivedComparison (coefHomSections l E W)
      (homComplex (R := completedIntegralCommRingSheafUnrestricted l E W)
        P (I.asFunctor.obj (op n))) ≫
    (coefHomDerivedSections l E W).map
      (coefHomInternalComparison.{t + 1, t, u} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) P (I.asFunctor.obj (op n)) ≫
      (coefficientIntegralInternalHom l E W).map
        (Prod.mkHom eP.inv.op (coefHomFiniteTargetMap l E W N I eI n)))

/-- Finite evaluation is normalized on all resolving complexes by the actual signed
Hom tower and the finite representative map. Evaluation of that strict complex is
literally the finite Hom section complex, including its differential.
Source: Stacks 0A95, 0A96, 0941 (blueprint: lem-coef-hom-tower-scalar-model). -/
def CoefHomEvaluationNormalization (n : ℕ)
    (γ : coefHomTower l E W ⋙ coefHomPointEvaluation l E n ≅
      coefHomFiniteIntegral l E W n) : Prop :=
  ∀ (K : DerivedCategory (scalarReductionSource l E W))
    (N : coefficientSequenceDerived l E W)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (_hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E W) P)
    (_hflat : ∀ i : ℤ,
      IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
        (J := Scheme.ProEt.topology W)
        (R := completedIntegralCommRingSheafUnrestricted l E W) (P.X i))
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) [I.IsKInjective]
    (eP : DerivedCategory.Q.obj P ≅ K)
    (eI : DerivedCategory.Q.obj (coefHomSequenceComplex l E W I) ≅
      (coefHomDerivedRestriction l E W).obj N),
    (coefHomPointEvaluation l E n).map
        (DerivedCategory.Q.map (coefHomSequenceSectionsIso l E W P I).inv ≫
          coefHomRepresentativeMap l E W K N P I eP eI) ≫ γ.hom.app (op K, N) =
      ((evaluation ℕᵒᵖ _).obj (op n)).mapDerivedCategoryFactors.hom.app
        (coefHomStrictComplex l E W P I) ≫
      coefHomFiniteRepresentativeMap l E W K N P I eP eI n

/-- Full Hom-tower/scalar-adjunction comparison, natural in both derived arguments.
Source: blueprint prop-coef-integral-dualizing, proof paragraph 2; Stacks 06YS,
0A95, 0A96, 07A6, 08J9, 0D6E and 0941
(blueprint: lem-coef-hom-tower-scalar-model).
Proof:
1. Use the exact constant-ring sequence equivalence and simultaneous K-injective
resolutions of towers; evaluation gives K-injective finite components.
2. Constant flat-term K-flat P stays K-flat by testing tensor acyclicity on levels.
3. The sequence slice ending at n identifies Hom(const P,I) with Hom(P,I_n),
with the actual signed differential and postcomposition transitions.
4. Hom from K-flat into K-injective is K-injective, so its ordinary global-section
tower computes derived sections and gives coefHomTower_representative.
5. Apply the recorded scalar internal-Hom adjunction on the sequence site. Its
comparison has exactly the representing bijections and restricted evaluation
normalization displayed below; no coefficient-map flatness is used.
6. The actual ordinary-section square g_R rho_W = rho_0 g_Q and the normalized
derived-pushforward composition comparison identify the two derived towers.
7. Exact evaluation gives the finite integral RHom complexes, retaining R scalars.
8. Apply the same normalized scalar internal-Hom adjunction at each completion
projection. Derived change of rings on P gives K_n; its unit is p mapped to p tensor 1.
9. All comparisons commute with precomposition and postcomposition and invert
quasi-isomorphisms, so they descend naturally in both derived variables. -/
theorem coefHomTowerScalarModel
    (S : ScalarHomModels.{t + 1, t, u, max (t + 2) (u + 1)}
      (coefficientSequenceTopology (Scheme.ProEt.topology W)))
    (μ : ∀ {R T : Sheaf (coefficientSequenceTopology (Scheme.ProEt.topology W))
        CommRingCat.{max u (t + 1)}} (a : R ⟶ T),
      ScalarHomTensorComparison.{t + 1, t, u, max (t + 2) (u + 1)} S a)
    (A : ScalarInternalHomAdjunction.{t + 1, t, u, max (t + 2) (u + 1)} S μ)
    (F : ScalarHomModels.{t + 1, t, u, max (t + 2) (u + 1)} (Scheme.ProEt.topology W))
    (ν : ∀ {R T : Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}}
      (a : R ⟶ T), ScalarHomTensorComparison.{t + 1, t, u, max (t + 2) (u + 1)} F a)
    (B : ScalarInternalHomAdjunction.{t + 1, t, u, max (t + 2) (u + 1)} F ν) :
    ∃ (α : coefHomTower l E W ≅ coefHomScalarTower l E W S),
      (∀ (K : DerivedCategory (scalarReductionSource l E W))
        (N : coefficientSequenceDerived l E W),
        α.inv.app (op K, N) =
          (coefHomDerivedFactorization l E W).hom.app
            ((coefficientSequenceInternalHom l E W).obj
              (op ((S.scalar (coefHomScalarMap l E W)).derived.obj
                ((coefHomDerivedConstant l E W).obj K)), N)) ≫
          (coefHomConstantDerivedSections l E W).map
            ((A.iso (coefHomScalarMap l E W)).hom.app
              (op ((coefHomDerivedConstant l E W).obj K), N))) ∧
      (∀ n : ℕ, ∃ γ : coefHomTower l E W ⋙ coefHomPointEvaluation l E n ≅
          coefHomFiniteIntegral l E W n, CoefHomEvaluationNormalization l E W n γ) ∧
      (∀ n : ℕ, ∃ β : coefHomFiniteIntegral l E W n ≅
          coefHomFiniteQuotient l E W F n,
        ∀ (K : DerivedCategory (scalarReductionSource l E W))
          (N : coefficientSequenceDerived l E W),
          β.inv.app (op K, N) = (coefHomDerivedSections l E W).map
            ((B.iso (completedIntegralCommRingProjectionUnrestricted l E W n)).hom.app
              (op K, (coefficientSequenceDerivedEvaluation l E W n).obj N))) ∧
      (∀ (K : DerivedCategory (scalarReductionSource l E W))
        (N : coefficientSequenceDerived l E W)
        (T : DerivedCategory (coefHomConstantModules l E W))
        (f : T ⟶ (scalarHomSource S (coefHomScalarMap l E W)).obj
          (op ((coefHomDerivedConstant l E W).obj K), N)),
        scalarHomBijection S (coefHomScalarMap l E W) (μ (coefHomScalarMap l E W))
          T ((coefHomDerivedConstant l E W).obj K) N f =
            f ≫ (A.iso (coefHomScalarMap l E W)).hom.app
              (op ((coefHomDerivedConstant l E W).obj K), N)) ∧
      (∀ (K : DerivedCategory (scalarReductionSource l E W))
        (N : coefficientSequenceDerived l E W),
        ((S.closed (coefHomConstantRing l E W)).transpose _
          ((coefHomDerivedConstant l E W).obj K)
          ((coefHomDerivedRestriction l E W).obj N)).symm
          ((A.iso (coefHomScalarMap l E W)).hom.app
            (op ((coefHomDerivedConstant l E W).obj K), N)) =
          scalarHomRestrictedEvaluation S (coefHomScalarMap l E W)
            (μ (coefHomScalarMap l E W)) ((coefHomDerivedConstant l E W).obj K) N) ∧
      (∀ (n : ℕ) (K : DerivedCategory (scalarReductionSource l E W))
        (N : coefficientSequenceDerived l E W),
        ((F.closed (completedIntegralCommRingSheafUnrestricted l E W)).transpose _ K
          ((coefficientFiniteDerivedRestriction l E W n).obj
            ((coefficientSequenceDerivedEvaluation l E W n).obj N))).symm
          ((B.iso (completedIntegralCommRingProjectionUnrestricted l E W n)).hom.app
            (op K, (coefficientSequenceDerivedEvaluation l E W n).obj N)) =
          scalarHomRestrictedEvaluation F (completedIntegralCommRingProjectionUnrestricted l E W n)
            (ν (completedIntegralCommRingProjectionUnrestricted l E W n)) K
              ((coefficientSequenceDerivedEvaluation l E W n).obj N)) := by
  sorry

end WeilConjectures
