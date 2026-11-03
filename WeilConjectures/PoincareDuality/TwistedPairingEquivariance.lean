/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedPoincareDualityConventions.PoincareDualityConventionsCondensed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.SitePerfectComplex
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import Mathlib.Data.Finset.Max
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointModuleComparison
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralGluing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocallyClosedGeneratorTensorIntersection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenFiltrationSuccessor
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.ConstructibleSheaf.Devissage
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralCriterion
public import WeilConjectures.AlgebraicGeometry.FiniteCondensedCtfEquivalence
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteScalarConstantModels
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicConstantLocalModelTor
public import Mathlib.RingTheory.Finiteness.Projective
public import WeilConjectures.AlgebraicGeometry.EtaleLocallyConstantPerfectComplex
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartOrderedRefinement
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.EtaleDomainPullbackCalculus
public import WeilConjectures.AlgebraicGeometry.EtaleLisseCtfPerfectLocalModel
public import WeilConjectures.AlgebraicGeometry.RefinementPreservesFiniteLisse
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.Refinement
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.SixFunctors.OpenClosed.Complex
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingPullbackFixed
public import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
public import WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartGeneration
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import WeilConjectures.PoincareDuality.DegreeOfPairing
public import WeilConjectures.AlgebraicGeometry.GroupScheme.FiniteWeilOperationData
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.WeilObject.Sheaf.StalkUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence

/-! # Frobenius invariance of the condensed twisted Poincare pairing

Source: latest blueprint part-duality-trace-formula/sec-lefschetz-verdier/sec-frobenius/
sec-purity-duality-and-frobenius/sk-thm-frobenius/
thm-pod-equivariance-of-the-twisted-pairing.md, and proof Steps 1--3.
(blueprint: thm-pod-equivariance-of-the-twisted-pairing).

The pairing uses its published exact terminal-section coordinates. The global
operators below use the same restriction, exchange and Weil maps in those coordinates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
attribute [local implicit_reducible] CategoryTheory.Aut
attribute [local implicit_reducible]
  AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPullback
attribute [local implicit_reducible]
  AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [local instance 10000] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [local instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian

universe u v w u₁ v₁
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj

namespace WeilConjectures.PoincareDuality

variable (P : CondensedPoincareDualityConventions.{u}) (c : PoincareCoefficient)

/-- The geometric Frobenius isomorphism on the fixed geometric fibre.
Source: fixed setting (blueprint: thm-pod-equivariance-of-the-twisted-pairing). -/
abbrev pairingGeometricFrobenius : P.X ≅ P.X :=
  P.datum.geometricFrobenius P.X₀

/-- The canonical restriction at the point in exact terminal-section coordinates.
The two outer maps are the canonical exact/right-derived comparisons; the middle
map is the published restriction along Spec(gamma), including coefficient transport.
Source: proof Step 1, point realization
(blueprint: thm-pod-equivariance-of-the-twisted-pairing). -/
def pairingPointInsertion :
    letI : IsAlgClosed P.datum.k := IsAlgClosure.isAlgClosed P.datum.k₀
    let Λ := (P.presentation c).obj P.ell
    let S := CohomologyTransport.sections Λ P.s
    S.mapDerivedCategory ≅
      moduleObjectDerivedPullback Λ (CondensedFrobeniusTransport.pointFrobenius P.datum).hom ⋙
        S.mapDerivedCategory :=
  letI : IsAlgClosed P.datum.k := IsAlgClosure.isAlgClosed P.datum.k₀
  let Λ := (P.presentation c).obj P.ell
  let S := CohomologyTransport.sections Λ P.s
  S.rightDerivedFunctorIsoMapDerivedCategory.symm ≪≫
    CohomologyTransport.insertion Λ
      (CondensedFrobeniusTransport.pointFrobenius P.datum).hom ≪≫
    Functor.isoWhiskerLeft _ S.rightDerivedFunctorIsoMapDerivedCategory

/-- Sections of the native point restriction, exchange, and specified Weil map.
This is the ordinary or compact Frobenius composite before requiring its datum to
be invertible. Source: proof Step 1
(blueprint: thm-pod-equivariance-of-the-twisted-pairing). -/
def pairingNativeOperator {A : Type u} {B : Type w} {E : Type u₁}
    [Category.{v} A] [Category.{v} B] [Category.{v₁} E]
    {PX : A ⥤ A} {PY : B ⥤ B} (S : B ⥤ E) (rho : 𝟭 B ≅ PY)
    (F : A ⥤ B) (ex : F ⋙ PY ⟶ PX ⋙ F) {M : A} (phi : PX.obj M ⟶ M) :
    End (S.obj (F.obj M)) :=
  S.map (rho.hom.app (F.obj M) ≫ ex.app M ≫ F.map phi)

omit P c in
private theorem pairingNativeOperator_exactDatum
    {A : Type u} {B : Type w} {E : Type u₁}
    [Category.{v} A] [Category.{v} B] [Category.{v₁} E]
    {PX QX : A ⥤ A} {PY : B ⥤ B} (S : B ⥤ E) (rho : 𝟭 B ≅ PY)
    (F : A ⥤ B) (ex : F ⋙ PY ⟶ PX ⋙ F) (e : PX ≅ QX)
    {M : A} (phi : QX.obj M ≅ M) :
    pairingNativeOperator S rho F ex (e.hom.app M ≫ phi.hom) =
      finiteWeilPointOperator S rho F ex (e.app M ≪≫ phi) := by
  rfl

/-- The contragredient and root-normalized Tate datum in the native pullback
coordinates of the operation theorem, transported to the exact strict action.
Source: def-pod-dual-tate-datum and the native operation comparison
(blueprint: thm-pod-equivariance-of-the-twisted-pairing). -/
def pairingTwistedDualDatum (K : P.strictWeil c)
    (_hK : IsPerfectOnCoefficientSite ((P.presentation c).obj P.ell) P.X K.carrier.obj) :
    let Λ := (P.presentation c).bundled.{u} P.ell
    let T := smoothTraceCoefficientLine P.ell Λ (P.presentation c) (Iso.refl _) P.X
      P.dimension
    (StrictWeilCondensed.action Λ.X (pairingGeometricFrobenius P)).obj
        (P.coefficientDual c K.carrier ⊗ T) ≅ P.coefficientDual c K.carrier ⊗ T := by
  let Λ := (P.presentation c).bundled.{u} P.ell
  let g := pairingGeometricFrobenius P
  letI : ∀ x : P.X, Invertible (P.ell : P.X.residueField x) := fun x ↦ by
    apply IsUnit.invertible
    simpa using (primeUnit P.datum P.ell P.different).map
      (P.structureMap.residueFieldAlgebraMap x)
  let phi := finiteWeilStrictDatum Λ.X g K
  let dual := finiteWeilHomDatum Λ.X g phi (leftDerivedUpperStarUnitIso Λ.X g.hom)
  let tate := finiteWeilTraceLineDatum P.ell (P.presentation c) Λ (Iso.refl _) g
    P.dimension
  exact (leftDerivedUpperStarIsoMapDerivedCategory Λ.X g.hom).symm.app _ ≪≫
    finiteWeilTensorDatum Λ.X g.hom dual tate

private theorem pairingPointInsertion_hom
    (N : P.ambient c P.s) :
    let : IsAlgClosed P.datum.k := IsAlgClosure.isAlgClosed P.datum.k₀
    (pairingPointInsertion P c).hom.app N =
      (CohomologyTransport.sections ((P.presentation c).obj P.ell) P.s).mapDerivedCategory.map
        ((finiteWeilPointRestriction P.datum ((P.presentation c).obj P.ell)).hom.app N) := by
  let : IsAlgClosed P.datum.k := IsAlgClosure.isAlgClosed P.datum.k₀
  let S := CohomologyTransport.sections ((P.presentation c).obj P.ell) P.s
  let e := S.rightDerivedFunctorIsoMapDerivedCategory
  let rho := finiteWeilPointRestriction P.datum ((P.presentation c).obj P.ell)
  simp only [pairingPointInsertion, CohomologyTransport.insertion, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_inv_app, Category.id_comp, Category.assoc]
  change e.inv.app N ≫ S.rightDerivedFunctor.map (rho.hom.app N) ≫
    e.hom.app _ = S.mapDerivedCategory.map (rho.hom.app N)
  rw [e.hom.naturality, Iso.inv_hom_id_app_assoc]

-- Naturality in the two tensor arguments.
@[reassoc] private theorem tensorShift_naturality {R : Type (u + 1)} [CommRing R]
    {P Q : DerivedCategory (ModuleCat.{u + 1} R)} (f : P ⟶ P) (g : Q ⟶ Q) (a b : ℤ) :
    ((shiftFunctor _ a).map f ⊗ₘ (shiftFunctor _ b).map g) ≫
        (DerivedCategory.shiftTensorShiftIso _ P Q a b).hom =
      (DerivedCategory.shiftTensorShiftIso _ P Q a b).hom ≫
        (shiftFunctor _ (a + b)).map (f ⊗ₘ g) := by
  let c₁ := (((curriedTensor (DerivedCategory (ModuleCat.{u + 1} R))).flip.obj
    (Q⟦b⟧)).commShiftIso a).hom
  let c₂ := (((curriedTensor (DerivedCategory (ModuleCat.{u + 1} R))).obj P).commShiftIso b).hom
  have hf : (shiftFunctor _ a).map f ▷ Q⟦b⟧ ≫ c₁.app P =
      c₁.app P ≫ (shiftFunctor _ a).map (f ▷ Q⟦b⟧) := c₁.naturality f
  have hg : (P ◁ (shiftFunctor _ b).map g) ≫ c₂.app Q =
      c₂.app Q ≫ (shiftFunctor _ b).map (P ◁ g) := c₂.naturality g
  have hf₂ : (f ▷ Q⟦b⟧) ≫ c₂.app Q =
      c₂.app Q ≫ (shiftFunctor _ b).map (f ▷ Q) :=
    (NatTrans.shift_app_comm
      ((curriedTensor (DerivedCategory (ModuleCat.{u + 1} R))).map f) b Q).symm
  have hg₁ : (P⟦a⟧ ◁ (shiftFunctor _ b).map g) ≫ c₁.app P =
      c₁.app P ≫ (shiftFunctor _ a).map (P ◁ (shiftFunctor _ b).map g) :=
    (NatTrans.shift_app_comm
      ((curriedTensor (DerivedCategory (ModuleCat.{u + 1} R))).flip.map
        ((shiftFunctor _ b).map g)) a P).symm
  have hfg : (f ▷ Q⟦b⟧) ≫ (P ◁ (shiftFunctor _ b).map g) ≫ c₂.app Q =
      c₂.app Q ≫ (shiftFunctor _ b).map (f ⊗ₘ g) := by
    rw [hg, ← Category.assoc, hf₂, Category.assoc, ← Functor.map_comp]
    rfl
  simp only [DerivedCategory.shiftTensorShiftIso, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  change ((shiftFunctor _ a).map f ⊗ₘ (shiftFunctor _ b).map g) ≫
    c₁.app P ≫ (shiftFunctor _ a).map (c₂.app Q) ≫ _ =
    c₁.app P ≫ (shiftFunctor _ a).map (c₂.app Q) ≫ _
  rw [MonoidalCategory.tensorHom_def, Category.assoc, reassoc_of% hg₁,
    reassoc_of% hf, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, hfg,
    Functor.map_comp, Category.assoc]
  erw [(shiftFunctorAdd' (DerivedCategory (ModuleCat.{u + 1} R)) b a
    (a + b) (add_comm b a)).inv.naturality]

private theorem identificationDegreeValue_naturality
    {R : Type (u + 1)} [CommRing R]
    {P Q : DerivedCategory (ModuleCat.{u + 1} R)}
    (b : P ⊗ Q ⟶ 𝟙_ _) (f : P ⟶ P) (g : Q ⟶ Q) (i : ℤ)
    (x : 𝟙_ _ ⟶ P⟦i⟧) (y : 𝟙_ _ ⟶ Q⟦-i⟧) :
    SixFunctors.identificationDegreeValue b i
        (x ≫ (shiftFunctor _ i).map f) (y ≫ (shiftFunctor _ (-i)).map g) =
      SixFunctors.identificationDegreeValue ((f ⊗ₘ g) ≫ b) i x y := by
  simp only [SixFunctors.identificationDegreeValue]
  rw [← tensorHom_comp_tensorHom, Category.assoc, tensorShift_naturality_assoc]
  erw [(shiftFunctorZero' (DerivedCategory (ModuleCat.{u + 1} R))
    (i + -i) (add_neg_cancel i)).hom.naturality_assoc]
  rfl

private theorem degreewisePoincareValue_invariant
    (Λ : AlgebraicGeometry.ProEtale.CondensedRing.ScalarSixRing.{u})
    {C Q : DerivedCategory (ModuleCat.{u + 1}
      (AlgebraicGeometry.ProEtale.condensedScalarRing Λ.X))}
    (d i : ℤ) (β : C ⊗ Q⟦2 * d⟧ ⟶ 𝟙_ _) (f : End C) (g : End Q)
    (h : (f ⊗ₘ (shiftFunctor _ (2 * d)).map g) ≫ β = β)
    (x : PairingCohomology Λ C i) (y : PairingCohomology Λ Q (2 * d - i)) :
    degreewisePoincareValue Λ d i β
        (x ≫ (shiftFunctor _ i).map f) (y ≫ (shiftFunctor _ (2 * d - i)).map g) =
      degreewisePoincareValue Λ d i β x y := by
  unfold degreewisePoincareValue
  apply congrArg SixFunctors.identificationScalarValue
  have hs := (shiftFunctorAdd' _ (2 * d) (-i) (2 * d - i) rfl).hom.naturality g
  change (shiftFunctor _ (2 * d - i)).map g ≫ (complementaryShift Λ Q d i).hom =
    (complementaryShift Λ Q d i).hom ≫
      (shiftFunctor _ (-i)).map ((shiftFunctor _ (2 * d)).map g) at hs
  rw [Category.assoc, hs, ← Category.assoc, identificationDegreeValue_naturality, h]

private abbrev pairingCoefficientDatum : P.datum.CoefficientDatum := by
  letI : IsAlgClosure (Padic P.ell) (ULift.{u} (PadicAlgCl P.ell)) :=
    { isAlgClosed := ⟨fun p ↦ by
        let e : ULift.{u} (PadicAlgCl P.ell) ≃+* PadicAlgCl P.ell := ULift.ringEquiv
        have h := (IsAlgClosed.splits (p.map e.toRingHom)).map e.symm.toRingHom
        have he : e.symm.toRingHom.comp e.toRingHom = RingHom.id _ := by ext; rfl
        simpa only [Polynomial.map_map, he, Polynomial.map_id] using h⟩
      isAlgebraic :=
        (ULift.algEquiv (R := Padic P.ell) (A := PadicAlgCl P.ell)).symm.isAlgebraic }
  exact { l := P.ell, different := P.different, Qbar := ULift.{u} (PadicAlgCl P.ell) }

private theorem pairingPresentation_admissible :
    IsAdmissibleCoefficientFor (pairingCoefficientDatum P)
      (Mon.mk ((P.presentation c).obj P.ell)) := by
  cases c with
  | finite =>
      let A := Padic.coefficientExtensionRing P.ell P.extension P.level
      let : TopologicalSpace A := ⊥
      let : DiscreteTopology A := ⟨rfl⟩
      refine Or.inl ⟨A, inferInstance,
        Padic.finite_coefficientExtensionRing P.ell P.extension P.level P.level_pos,
        inferInstance, inferInstance, inferInstance, ?_, ⟨Iso.refl _⟩⟩
      refine ⟨P.level, P.level_pos, ?_⟩
      have h := coefficientFiniteTwist_annihilator P.ell P.extension (P.level - 1)
      rw [Nat.sub_add_cancel P.level_pos] at h
      simpa only [pairingCoefficientDatum, Nat.cast_pow] using h
  | integral => exact Or.inr (Or.inl ⟨P.extension, ⟨Iso.refl _⟩⟩)
  | rational => exact Or.inr (Or.inr (Or.inl ⟨P.extension, ⟨Iso.refl _⟩⟩))
  | qbar => exact Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))

set_option maxHeartbeats 1200000 in
-- Unfold the canonical global and native operator coordinates.
set_option maxHeartbeats 1200000 in
-- Unfold the canonical global and native operator coordinates.
private theorem pairingTwistedDualDatum_native (K : P.strictWeil c)
    (hK : IsPerfectOnCoefficientSite ((P.presentation c).obj P.ell) P.X K.carrier.obj) :
    let Λ := (P.presentation c).bundled.{u} P.ell
    let g := pairingGeometricFrobenius P
    letI : ∀ x : P.X, Invertible (P.ell : P.X.residueField x) := fun x ↦ by
      apply IsUnit.invertible
      simpa using (primeUnit P.datum P.ell P.different).map
        (P.structureMap.residueFieldAlgebraMap x)
    let T := smoothTraceCoefficientLine P.ell Λ (P.presentation c) (Iso.refl _) P.X
      P.dimension
    let M := P.coefficientDual c K.carrier ⊗ T
    let phi := finiteWeilStrictDatum Λ.X g K
    let dual := finiteWeilHomDatum Λ.X g phi (leftDerivedUpperStarUnitIso Λ.X g.hom)
    let tate := finiteWeilTraceLineDatum P.ell (P.presentation c) Λ (Iso.refl _) g
      P.dimension
    (leftDerivedUpperStarIsoMapDerivedCategory Λ.X g.hom).app M ≪≫
        pairingTwistedDualDatum P c K hK = finiteWeilTensorDatum Λ.X g.hom dual tate := by
  dsimp only [pairingTwistedDualDatum]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Iso.hom_inv_id_app_assoc]

set_option maxHeartbeats 3000000 in
-- The comparison expands the native derived-operation and exact-section coordinates.
end WeilConjectures.PoincareDuality
