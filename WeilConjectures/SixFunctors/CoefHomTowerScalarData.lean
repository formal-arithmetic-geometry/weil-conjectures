/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import WeilConjectures.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.ScalarInternalHomAdjunction
public import WeilConjectures.CategoryTheory.SystemRingedSequenceSite
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.ConstantSequenceModuleEquivalenceOfUniverses
public import Mathlib.Algebra.Homology.Functor

/-! # Concrete coefficient rings, restrictions and Hom towers

Source: blueprint `prop-coef-integral-dualizing`, proof paragraph 2;
Stacks Project, Tags 06YS, 0A95, 0A96, 07A6, 08J9 and 0941
(blueprint: def-coef-hom-tower-scalar-data).

All sections retain the integral action and the strict tower index. The natural-number
index n denotes exponent n+1. Site and coefficient universes remain independent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u c v r d w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open SheafOfModules
namespace WeilConjectures

/-- The canonical localization comparison: first use the actual replacement unit,
then the inverse factorization isomorphism of the defined derived Hom functor.
Source: Stacks 0A95 (blueprint: def-coef-hom-tower-scalar-data). -/
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
Source: Stacks 0941 (blueprint: def-coef-hom-tower-scalar-data). -/
abbrev coefHomConstantRing :=
  systemSequenceRing.{t + 1, t, max u (t + 1)} (J := Scheme.ProEt.topology W)
    ((Functor.const ℕᵒᵖ).obj
    (completedIntegralCommRingSheafUnrestricted l E W))

/-- Constant-ring sequence modules; this is the recorded ringed-site module category.
Source: Stacks 0941 (blueprint: def-coef-hom-tower-scalar-data). -/
abbrev coefHomConstantModules :=
  scalarModules (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefHomConstantRing l E W)

/-- The standard localization of constant-ring sequence modules.
Source: Stacks 05RU, 0941 (blueprint: def-coef-hom-tower-scalar-data). -/
instance coefHomConstantHasDerived : HasDerivedCategory (coefHomConstantModules l E W) :=
  HasDerivedCategory.standard _

/-- The coefficient-preserving category of strict R-module towers.
The lift only puts the coefficients in the universe of the site.
Source: Stacks 0941 (blueprint: def-coef-hom-tower-scalar-data). -/
abbrev coefHomPointModules :=
  ℕᵒᵖ ⥤ ModuleCat.{max u (t + 1)}
    (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))

/-- The ordinary derived category of strict point towers.
Source: Stacks 05RU, 0941 (blueprint: def-coef-hom-tower-scalar-data). -/
instance coefHomPointHasDerived : HasDerivedCategory (coefHomPointModules.{t, u} l E) :=
  HasDerivedCategory.standard _

/-- The ordinary derived category of one point coefficient module.
Source: Stacks 05RU (blueprint: def-coef-hom-tower-scalar-data). -/
instance coefHomFinitePointHasDerived :
    HasDerivedCategory (ModuleCat.{max u (t + 1)}
      (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))) :=
  HasDerivedCategory.standard _

/-- The actual constant integral action at the terminal pro-etale object.
Source: blueprint proof paragraph 2 (blueprint: def-coef-hom-tower-scalar-data). -/
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
Source: Stacks 08JA (blueprint: def-coef-hom-tower-scalar-data). -/
def coefHomSections : scalarReductionSource l E W ⥤
    ModuleCat.{max u (t + 1)} (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)) :=
  SheafOfModules.evaluation _ (op (Scheme.ProEt.mk (𝟙 W))) ⋙
    ModuleCat.restrictScalars (coefHomScalar l E W)

/-- Sections are additive because evaluation and restriction preserve addition.
Source: Stacks 08JA (blueprint: def-coef-hom-tower-scalar-data). -/
instance coefHomSectionsAdditive : (coefHomSections l E W).Additive where
  map_add := rfl

/-- Sections on ordinary completed-module towers; there is no inverse limit.
Source: Stacks 0941 (blueprint: def-coef-hom-tower-scalar-data). -/
def coefHomTowerSections :
    (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ coefHomPointModules.{t, u} l E :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (coefHomSections l E W)

/-- Additivity of sections on towers is componentwise.
Source: Stacks 0941 (blueprint: def-coef-hom-tower-scalar-data). -/
instance coefHomTowerSectionsAdditive : (coefHomTowerSections l E W).Additive :=
  inferInstanceAs ((Functor.whiskeringRight ℕᵒᵖ _ _).obj _).Additive

/-- The recorded simultaneous K-injectives on constant-ring towers.
Source: Stacks 079P (blueprint: def-coef-hom-tower-scalar-data). -/
instance coefHomTowersKInjective :
    Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ scalarReductionSource l E W) :=
  coefficientConstantTowers_haveKInjectives.{t, u} l E W

/-- Derived tower sections: the target is D(Tow(Mod R)), before inverse limit.
Source: Stacks 079P, 0941 (blueprint: def-coef-hom-tower-scalar-data). -/
def coefHomDerivedTowerSections : coefficientSequenceRestrictedDerived l E W ⥤
    DerivedCategory (coefHomPointModules.{t, u} l E) :=
  (coefHomTowerSections l E W).rightDerivedFunctor

/-- Exact point-tower evaluation, with the same integral scalar action.
Source: Stacks 0941 (blueprint: def-coef-hom-tower-scalar-data). -/
def coefHomPointEvaluation (n : ℕ) :
    DerivedCategory (coefHomPointModules.{t, u} l E) ⥤
      DerivedCategory (ModuleCat.{max u (t + 1)}
        (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))) :=
  ((evaluation ℕᵒᵖ _).obj (op n)).mapDerivedCategory

/-- The recorded section-preserving constant-sequence equivalence, in the full size.
Source: Stacks 0941 (blueprint: def-coef-hom-tower-scalar-data). -/
def coefHomEquivalence : coefHomConstantModules l E W ≌
    (ℕᵒᵖ ⥤ scalarReductionSource l E W) :=
  ConstantCompletion.independentConstantSequenceEquivalence.{t + 1, t, u}
    (completedIntegralCommRingSheafUnrestricted l E W)

/-- Additivity of the section-preserving equivalence.
Source: Stacks 0941 (blueprint: def-coef-hom-tower-scalar-data). -/
instance coefHomEquivalenceAdditive : (coefHomEquivalence l E W).functor.Additive :=
  (ConstantCompletion.independentConstantSequenceEquivalence_additive.{t + 1, t, u}
    (completedIntegralCommRingSheafUnrestricted l E W)).1

/-- Additivity of the inverse section-preserving equivalence.
Source: Stacks 0941 (blueprint: def-coef-hom-tower-scalar-data). -/
instance coefHomEquivalenceInverseAdditive : (coefHomEquivalence l E W).inverse.Additive :=
  (ConstantCompletion.independentConstantSequenceEquivalence_additive.{t + 1, t, u}
    (completedIntegralCommRingSheafUnrestricted l E W)).2

/-- Actual constant towers, realized on the constant-ring sequence site.
Source: Stacks 0941 (blueprint: def-coef-hom-tower-scalar-data). -/
def coefHomConstant : scalarReductionSource l E W ⥤ coefHomConstantModules l E W :=
  Functor.const ℕᵒᵖ ⋙ (coefHomEquivalence l E W).inverse

/-- Constant towers preserve addition of maps.
Source: Stacks 0941 (blueprint: def-coef-hom-tower-scalar-data).
Proof: the constant diagram adds maps componentwise, and the inverse of the recorded
additive section-preserving equivalence preserves their sum. -/
theorem coefHomConstant_additive : (coefHomConstant l E W).Additive where
  map_add {_ _} f g := (coefHomEquivalence l E W).inverse.map_add
    (f := (Functor.const ℕᵒᵖ).map f) (g := (Functor.const ℕᵒᵖ).map g)

/-- The additive witness for actual constant towers.
Source: Stacks 0941 (blueprint: def-coef-hom-tower-scalar-data). -/
instance coefHomConstantAdditive : (coefHomConstant l E W).Additive :=
  coefHomConstant_additive l E W

/-- Exactness of constant towers follows from pointwise kernels and cokernels.
Source: Stacks 0941 (blueprint: def-coef-hom-tower-scalar-data).
Proof: the constant-tower functor preserves kernels and cokernels componentwise,
and the recorded equivalence preserves all limits and colimits. -/
theorem coefHomConstant_exact : PreservesFiniteLimits (coefHomConstant l E W) ∧
    PreservesFiniteColimits (coefHomConstant l E W) := by
  change PreservesFiniteLimits
      ((Functor.const ℕᵒᵖ : scalarReductionSource l E W ⥤ _) ⋙
        (coefHomEquivalence l E W).inverse) ∧
    PreservesFiniteColimits
      ((Functor.const ℕᵒᵖ : scalarReductionSource l E W ⥤ _) ⋙
        (coefHomEquivalence l E W).inverse)
  exact ⟨inferInstance, inferInstance⟩

/-- Finite-limit preservation of the actual constant-tower functor.
Source: Stacks 0941 (blueprint: def-coef-hom-tower-scalar-data). -/
instance coefHomConstantLimits : PreservesFiniteLimits (coefHomConstant l E W) :=
  (coefHomConstant_exact l E W).1

/-- Finite-colimit preservation of the actual constant-tower functor.
Source: Stacks 0941 (blueprint: def-coef-hom-tower-scalar-data). -/
instance coefHomConstantColimits : PreservesFiniteColimits (coefHomConstant l E W) :=
  (coefHomConstant_exact l E W).2

/-- The exact derived constant-tower functor.
Source: Stacks 0941 (blueprint: def-coef-hom-tower-scalar-data). -/
def coefHomDerivedConstant : DerivedCategory (scalarReductionSource l E W) ⥤
    DerivedCategory (coefHomConstantModules l E W) :=
  (coefHomConstant l E W).mapDerivedCategory

/-- The actual completion projections commute with every sequence-site restriction.
Source: Stacks 03CO, 0941 (blueprint: def-coef-hom-tower-scalar-data).
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
Source: Stacks 03CO, 0941 (blueprint: def-coef-hom-tower-scalar-data). -/
def coefHomScalarMap : coefHomConstantRing l E W ⟶ coefficientSequenceCommRingSheaf l E W :=
  ⟨{ app := fun X ↦
        (completedIntegralCommRingProjectionUnrestricted l E W X.unop.1).hom.app
          (op X.unop.2)
     naturality := fun _ _ f ↦ coefHomScalar_naturality l E W f }⟩

/-- Ordinary restriction along precisely the sequence completion-projection map.
Source: Stacks 07A6 (blueprint: def-coef-hom-tower-scalar-data). -/
abbrev coefHomOrdinaryRestriction : coefficientSequenceModules l E W ⥤
    coefHomConstantModules l E W :=
  scalarRestriction.{t + 1, t, max u (t + 1)} (coefHomScalarMap l E W)

/-- Exact sequence-site scalar restriction and its ordinary localization.
Source: Stacks 07A6 (blueprint: def-coef-hom-tower-scalar-data). -/
def coefHomDerivedRestriction : coefficientSequenceDerived l E W ⥤
    DerivedCategory (coefHomConstantModules l E W) :=
  scalarDerivedRestriction (coefHomScalarMap l E W)

/-- Ordinary sections on the constant-ring sequence site, realized as literal towers.
Source: Stacks 0941 (blueprint: def-coef-hom-tower-scalar-data). -/
def coefHomConstantSections : coefHomConstantModules l E W ⥤
    coefHomPointModules.{t, u} l E :=
  (coefHomEquivalence l E W).functor ⋙ coefHomTowerSections l E W

/-- Sections preserve addition before deriving.
Source: Stacks 0941 (blueprint: def-coef-hom-tower-scalar-data). -/
instance coefHomConstantSectionsAdditive : (coefHomConstantSections l E W).Additive where
  map_add {_ _} f g := congrArg
    (fun α ↦ (coefHomTowerSections l E W).map α)
    ((coefHomEquivalence l E W).functor.map_add (f := f) (g := g))

/-- Constant-ring sequence modules have the same simultaneous resolutions as towers.
Source: Stacks 079P (blueprint: def-coef-hom-tower-scalar-data). -/
instance coefHomConstantKInjectives :
    Abelian.HasKInjectiveResolutions (coefHomConstantModules l E W) :=
  letI := (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t + 1, t, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefHomConstantRing l E W)).1
  inferInstance

/-- Total derived sections on the constant-ring sequence site, without inverse limit.
Source: Stacks 079P, 0941 (blueprint: def-coef-hom-tower-scalar-data). -/
def coefHomConstantDerivedSections : DerivedCategory (coefHomConstantModules l E W) ⥤
    DerivedCategory (coefHomPointModules.{t, u} l E) :=
  (coefHomConstantSections l E W).rightDerivedFunctor

/-- The recorded RHom on the constant-ring sequence site.
Source: Stacks 0A95 (blueprint: def-coef-hom-tower-scalar-data). -/
def coefHomConstantInternalHom :=
  derivedInternalHomOfUniverses.{t + 1, t, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W)) (coefHomConstantRing l E W)

/-- The canonical derived Hom tower, before applying an inverse limit.
Source: blueprint proof paragraph 2 (blueprint: def-coef-hom-tower-scalar-data). -/
def coefHomTower :
    (DerivedCategory (scalarReductionSource l E W))ᵒᵖ ×
      coefficientSequenceDerived l E W ⥤ DerivedCategory (coefHomPointModules.{t, u} l E) :=
  ((coefHomDerivedConstant l E W).op.prod (coefHomDerivedRestriction l E W)) ⋙
    coefHomConstantInternalHom l E W ⋙ coefHomConstantDerivedSections l E W

/-- Reassembling a strict tower of complexes satisfies the complex identities.
Source: Stacks 0941 (blueprint: def-coef-hom-tower-scalar-data).
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
Source: Stacks 0A8Z, 0941 (blueprint: def-coef-hom-tower-scalar-data). -/
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
Source: Stacks 0941 (blueprint: def-coef-hom-tower-scalar-data). -/
def coefHomPointQuotientRing : ℕᵒᵖ ⥤ RingCat.{max u (t + 1)} :=
  Functor.ofOpSequence (X := fun n ↦
    RingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))
    (fun n ↦ RingCat.ofHom
      ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
        ((Padic.coefficientExtensionTransition l E (n + 1)).comp
          (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom)))

/-- The ordinary module category on the one-point quotient sequence topos.
The topology on ℕ is the trivial one, so its module sheaves are module presheaves.
Source: Stacks 0941 (blueprint: def-coef-hom-tower-scalar-data). -/
abbrev coefHomQuotientPointModules :=
  PresheafOfModules.{max u (t + 1)} (coefHomPointQuotientRing.{t, u} l E)

/-- Standard localization of quotient-semilinear point towers.
Source: Stacks 05RU (blueprint: def-coef-hom-tower-scalar-data). -/
instance coefHomQuotientPointHasDerived :
    HasDerivedCategory (coefHomQuotientPointModules.{t, u} l E) :=
  HasDerivedCategory.standard _

/-- The constant ring on the one-point sequence site.
Source: Stacks 0941 (blueprint: def-coef-hom-tower-scalar-data). -/
def coefHomPointConstantRing : ℕᵒᵖ ⥤ RingCat.{max u (t + 1)} :=
  (Functor.const ℕᵒᵖ).obj (RingCat.of
    (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)))

/-- The actual quotient maps from integral scalars on the point sequence.
Source: Stacks 07A6, 0941 (blueprint: def-coef-hom-tower-scalar-data). -/
def coefHomPointScalarComponent (n : ℕ) :
    (coefHomPointConstantRing.{t, u} l E).obj (op n) ⟶
      (coefHomPointQuotientRing.{t, u} l E).obj (op n) :=
  RingCat.ofHom ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
    ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
      (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom))

/-- The point quotient maps are compatible with every transition.
Source: Stacks 0941 (blueprint: def-coef-hom-tower-scalar-data).
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
Source: Stacks 07A6 (blueprint: def-coef-hom-tower-scalar-data). -/
def coefHomPointScalarMap :
    coefHomPointConstantRing.{t, u} l E ⟶ coefHomPointQuotientRing.{t, u} l E where
  app n := coefHomPointScalarComponent l E n.unop
  naturality _ _ f := coefHomPointScalar_naturality l E f

/-- A module presheaf over the constant point ring is literally an R-module tower.
Source: Stacks 0941 (blueprint: def-coef-hom-tower-scalar-data). -/
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
Source: Stacks 07A6 (blueprint: def-coef-hom-tower-scalar-data). -/
def coefHomPointRestriction : coefHomQuotientPointModules.{t, u} l E ⥤
    coefHomPointModules.{t, u} l E :=
  PresheafOfModules.restrictScalars (coefHomPointScalarMap.{t, u} l E) ⋙
    coefHomPointConstantToTower l E

private theorem evaluationRestrictionLimits {R : Type r} [Ring R]
    (F : ℕᵒᵖ ⥤ RingCat.{r}) (n : ℕᵒᵖ) (a : R →+* F.obj n) :
    PreservesFiniteLimits
      (PresheafOfModules.evaluation.{r} F n ⋙ ModuleCat.restrictScalars.{r} a) := by
  let U := forget₂ (ModuleCat.{r} R) AddCommGrpCat
  have : PreservesFiniteLimits
      ((PresheafOfModules.evaluation.{r} F n ⋙ ModuleCat.restrictScalars.{r} a) ⋙ U) := by
    change PreservesFiniteLimits
      (PresheafOfModules.evaluation.{r} F n ⋙
        forget₂ (ModuleCat.{r} _) AddCommGrpCat)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ U

/-- Integral restriction is additive and exact on point towers.
Source: Stacks 07A6, 0941 (blueprint: def-coef-hom-tower-scalar-data).
Proof: both actions are related by the actual quotient homomorphisms, and restriction
keeps all underlying abelian groups and maps. Kernels and cokernels in these diagram
module categories are computed on components, so their underlying groups are unchanged. -/
theorem coefHomPointRestriction_exact : (coefHomPointRestriction.{t, u} l E).Additive ∧
    PreservesFiniteLimits (coefHomPointRestriction.{t, u} l E) ∧
    PreservesFiniteColimits (coefHomPointRestriction.{t, u} l E) := by
  constructor
  · exact ⟨fun {_ _} _ _ ↦ rfl⟩
  constructor
  · apply preservesFiniteLimits_of_evaluation
    intro n
    change PreservesFiniteLimits
      (PresheafOfModules.evaluation (coefHomPointQuotientRing.{t, u} l E) n ⋙
        ModuleCat.restrictScalars (coefHomPointScalarComponent l E n.unop).hom)
    exact evaluationRestrictionLimits _ n
      (coefHomPointScalarComponent l E n.unop).hom
  · exact ⟨fun J _ _ ↦ by
      apply preservesColimitsOfShape_of_evaluation
      intro n
      change PreservesColimitsOfShape J
        (PresheafOfModules.evaluation (coefHomPointQuotientRing.{t, u} l E) n ⋙
          ModuleCat.restrictScalars (coefHomPointScalarComponent l E n.unop).hom)
      infer_instance⟩

/-- Additivity of the actual point restriction.
Source: Stacks 07A6 (blueprint: def-coef-hom-tower-scalar-data). -/
instance coefHomPointRestrictionAdditive : (coefHomPointRestriction.{t, u} l E).Additive :=
  (coefHomPointRestriction_exact l E).1

/-- Left exactness of the actual point restriction.
Source: Stacks 07A6 (blueprint: def-coef-hom-tower-scalar-data). -/
instance coefHomPointRestrictionLimits :
    PreservesFiniteLimits (coefHomPointRestriction.{t, u} l E) :=
  (coefHomPointRestriction_exact l E).2.1

/-- Right exactness of the actual point restriction.
Source: Stacks 07A6 (blueprint: def-coef-hom-tower-scalar-data). -/
instance coefHomPointRestrictionColimits :
    PreservesFiniteColimits (coefHomPointRestriction.{t, u} l E) :=
  (coefHomPointRestriction_exact l E).2.2

/-- Exact localization of rho_0 restriction.
Source: Stacks 07A6 (blueprint: def-coef-hom-tower-scalar-data). -/
def coefHomPointDerivedRestriction :
    DerivedCategory (coefHomQuotientPointModules.{t, u} l E) ⥤
      DerivedCategory (coefHomPointModules.{t, u} l E) :=
  (coefHomPointRestriction l E).mapDerivedCategory

/-- The terminal-object section functor on the underlying sequence site.
Source: Stacks 0941 (blueprint: def-coef-hom-tower-scalar-data). -/
def coefHomSectionIndex : ℕ ⥤ ℕ × W.ProEt where
  obj n := (n, Scheme.ProEt.mk (𝟙 W))
  map f := Prod.mkHom f (𝟙 _)
  map_id _n := rfl
  map_comp _f _g := rfl

/-- Constant quotient coefficients map to their actual global sections by sheafification.
Source: Stacks 03DA, 0941 (blueprint: def-coef-hom-tower-scalar-data). -/
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
Source: Stacks 03DA, 0941 (blueprint: def-coef-hom-tower-scalar-data).
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
Source: Stacks 03DA, 0941 (blueprint: def-coef-hom-tower-scalar-data). -/
def coefHomQuotientSectionScalar : coefHomPointQuotientRing.{t, u} l E ⟶
    (coefHomSectionIndex W).op ⋙
      (coefficientSequenceCommRingSheaf l E W).obj ⋙ forget₂ CommRingCat RingCat where
  app n := coefHomQuotientSectionScalarComponent l E W n.unop
  naturality _ _ f := coefHomQuotientSectionScalar_naturality l E W f

/-- Actual quotient-linear sections, retaining the whole semilinear point tower.
Source: Stacks 0941 (blueprint: def-coef-hom-tower-scalar-data). -/
def coefHomQuotientSections : coefficientSequenceModules l E W ⥤
    coefHomQuotientPointModules.{t, u} l E :=
  SheafOfModules.forget _ ⋙ PresheafOfModules.pushforward
    (coefHomQuotientSectionScalar l E W)

/-- Additivity of the actual quotient-linear sections.
Source: Stacks 0941 (blueprint: def-coef-hom-tower-scalar-data).
Proof: evaluation on every component and scalar restriction preserve sums of maps. -/
theorem coefHomQuotientSections_additive : (coefHomQuotientSections l E W).Additive := by
  constructor
  intro M N f g
  rfl

/-- The additive structure on quotient-linear sections.
Source: Stacks 0941 (blueprint: def-coef-hom-tower-scalar-data). -/
instance coefHomQuotientSectionsAdditive : (coefHomQuotientSections l E W).Additive :=
  coefHomQuotientSections_additive l E W

/-- The sequence ringed site admits simultaneous K-injective resolutions.
Source: Stacks 079P (blueprint: def-coef-hom-tower-scalar-data). -/
instance coefHomQuotientKInjectives :
    Abelian.HasKInjectiveResolutions (coefficientSequenceModules l E W) :=
  letI := (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t + 1, t, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)).1
  inferInstance

/-- Total quotient-linear sections, without inverse limit.
Source: Stacks 079P, 0941 (blueprint: def-coef-hom-tower-scalar-data). -/
def coefHomQuotientDerivedSections : coefficientSequenceDerived l E W ⥤
    DerivedCategory (coefHomQuotientPointModules.{t, u} l E) :=
  (coefHomQuotientSections l E W).rightDerivedFunctor

/-- The quotient-linear derived section complex followed by exact integral restriction.
Source: Stacks 07A6, 0D6E (blueprint: def-coef-hom-tower-scalar-data). -/
def coefHomRestrictedQuotientSections : coefficientSequenceDerived l E W ⥤
    DerivedCategory (coefHomPointModules.{t, u} l E) :=
  coefHomQuotientDerivedSections l E W ⋙ coefHomPointDerivedRestriction l E

/-- The actual quotient-scalar Hom tower, whose target retains the integral action.
Source: Stacks 07A6, 08J9 (blueprint: def-coef-hom-tower-scalar-data). -/
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

end WeilConjectures
