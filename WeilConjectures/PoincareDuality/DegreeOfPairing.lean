/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.SfIdentificationData
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportCompact
public import WeilConjectures.PoincareDuality.GlobalTwistInterchange.GlobalTwistInterchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TraceCupMixed.CondensedMixedSupportCup
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeil.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralTateBasis
public import WeilConjectures.AlgebraicGeometry.Native.NativeSignedLine
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsRegularEnd
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TraceCupProper.CondensedProperComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSmoothTraceUnit
public import WeilConjectures.AlgebraicGeometry.CondensedPoincare.CondensedPoincareSetting
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportUnits
public import WeilConjectures.AlgebraicGeometry.PoincareDualitySetting
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import WeilConjectures.SmoothPurity.CondensedOrdinaryCompactSections
import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.PoincareDuality.Abstract
import Mathlib.Topology.KrullDimension
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
import WeilConjectures.SmoothPurity.Point.PointSectionsScalarExtension
import Mathlib.Algebra.Field.ULift
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import Mathlib.Algebra.Ring.Shrink
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointScalarRealization
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Conv
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
import WeilConjectures.CategoryTheory.RingObjects.Condensed.PadicAlgClGlobalSections
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
import WeilConjectures.CategoryTheory.DerivedCategory.Bounded.BoundedHeartAmplitude
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionLocalizing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
import WeilConjectures.PoincareDuality.VerdierBiduality
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointSectionsExact
import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteConstructibleEncoding
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageBoundedBelow
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageAmplitude
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.AlgebraicGeometry.PurityTransport.CondensedTateLineTrivializations
public import WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.ScalarExtensionMonoidal
public import WeilConjectures.CategoryTheory.Monoidal.Closed.ExceptionalHom
public import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Linear

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointScalarRings
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TraceCup.CondensedTraceCup

/-! # Degree of the Poincare pairing

Source: latest blueprint, `prop-pod-degree-of-the-pairing.md` and its proof,
complementary-degree component and elimination of the invertible point twist
(blueprint: prop-pod-degree-of-the-pairing).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [local instance 10000]
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open WeilConjectures.SixFunctors
open scoped CategoryTheory.Obj CategoryTheory.Functor TensorProduct

namespace WeilConjectures.PoincareDuality

variable (ell : ℕ) [Fact ell.Prime] (Λ : ScalarSixRing.{u})
  (c : PurityTransport.Coefficient ell) (e : c.bundled.{u} ell ≅ Λ)

/-- Hom from the regular derived scalar unit is the cohomology group.
Source: complementary-degree groups (blueprint: prop-pod-degree-of-the-pairing). -/
abbrev PairingCohomology (P : DerivedCategory
    (ModuleCat.{u + 1} (condensedScalarRing Λ.X))) (i : ℤ) := 𝟙_ _ ⟶ P⟦i⟧

/-- The shift convention H^(-i)(Q[2d]) = H^(2d-i)(Q), with its actual
canonical shift-addition map, rather than an equality of unrelated group types.
Source: first proof step (blueprint: prop-pod-degree-of-the-pairing). -/
def complementaryShift (Q : DerivedCategory
    (ModuleCat.{u + 1} (condensedScalarRing Λ.X))) (d i : ℤ) :
    Q⟦(2 * d - i)⟧ ≅ (Q⟦(2 * d)⟧) ⟦(-i)⟧ :=
  (shiftFunctorAdd' _ (2 * d) (-i) (2 * d - i) rfl).app Q

/-- The scalar of the degree-zero component, using the existing tensor-shift
comparison, its total-complex signs, H^0 of the unit and evaluation at 1.
Source: first displayed pairing (blueprint: prop-pod-degree-of-the-pairing). -/
def degreewisePoincareValue
    {P Q : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ.X))} (d i : ℤ)
    (β : P ⊗ Q⟦2 * d⟧ ⟶ 𝟙_ _)
    (x : PairingCohomology Λ P i) (y : PairingCohomology Λ Q (2 * d - i)) :
    condensedScalarRing Λ.X :=
  identificationScalarValue
    (identificationDegreeValue β i x (y ≫ (complementaryShift Λ Q d i).hom))

private theorem degreewise_bilinear
    {P Q : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ.X))} (d i : ℤ)
    (β : P ⊗ Q⟦2 * d⟧ ⟶ 𝟙_ _) :
    ∃ B : PairingCohomology Λ P i →ₗ[condensedScalarRing Λ.X]
        PairingCohomology Λ Q (2 * d - i) →ₗ[condensedScalarRing Λ.X]
          condensedScalarRing Λ.X,
      ∀ x y, B x y = degreewisePoincareValue Λ d i β x y := by
  refine ⟨{ toFun := fun x ↦
    { toFun := fun y ↦ degreewisePoincareValue Λ d i β x y
      map_add' := ?_
      map_smul' := ?_ }
            map_add' := ?_
            map_smul' := ?_ }, fun _ _ ↦ rfl⟩
  · intro y z
    simp [degreewisePoincareValue, identificationDegreeValue, identificationScalarValue,
      MonoidalCategory.tensorHom_def]
  · intro r y
    simp [degreewisePoincareValue, identificationDegreeValue, identificationScalarValue,
      MonoidalCategory.tensorHom_def]
  · intro x z
    ext y
    simp [degreewisePoincareValue, identificationDegreeValue, identificationScalarValue,
      MonoidalCategory.tensorHom_def]
  · intro r x
    ext y
    simp [degreewisePoincareValue, identificationDegreeValue, identificationScalarValue,
      MonoidalCategory.tensorHom_def]

private theorem untwist_bilinear
    {R A U Q L V : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup U] [Module R U]
    [AddCommGroup Q] [Module R Q] [AddCommGroup L] [Module R L]
    [AddCommGroup V] [Module R V]
    (B : A →ₗ[R] Q →ₗ[R] R) (E : TensorProduct R U L ≃ₗ[R] Q)
    (J : V ≃ₗ[R] Module.Dual R L) :
    ∃ B' : A →ₗ[R] U →ₗ[R] V,
      ∀ x y z, J (B' x y) z = B x (E (y ⊗ₜ[R] z)) := by
  let F : A →ₗ[R] U →ₗ[R] Module.Dual R L :=
    { toFun := fun x ↦
      { toFun := fun y ↦
        { toFun := fun z ↦ B x (E (y ⊗ₜ[R] z))
          map_add' := by intros; simp [TensorProduct.tmul_add]
          map_smul' := by intros; simp }
        map_add' := by intros; ext; simp [TensorProduct.add_tmul]
        map_smul' := by intros; ext; simp [TensorProduct.smul_tmul] }
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  let B' : A →ₗ[R] U →ₗ[R] V :=
    { toFun := fun x ↦ J.symm.toLinearMap.comp (F x)
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  exact ⟨B', fun x y z ↦ congrArg (fun f ↦ f z) (J.apply_symm_apply (F x y))⟩

/-- The genuine root-tower Tate power in the given coefficient coordinates.
Its degree-zero derived realization is smoothTraceCoefficientLine.
Source: native Tate twists (blueprint: prop-pod-degree-of-the-pairing). -/
abbrev pairingPointLine (T : Scheme.{u}) (d : ℕ) :=
  (Mod.extendScalars (coefficientMap (Λ := c.obj ell) (Λ' := Λ.X)
    e.hom.hom.hom T)).obj (c.line ell T d)

/-- Canonical exact scalar-extension/single comparison for the native Tate line.
The extension is exact because the coefficient change is an isomorphism.
Source: twist definition (blueprint: prop-pod-degree-of-the-pairing). -/
def pairingLineSingleIso (T : Scheme.{u}) (d : ℕ) :
    smoothTraceCoefficientLine ell Λ c e T d ≅
      (DerivedCategory.singleFunctor _ 0).obj (pairingPointLine ell Λ c e T d) := by
  let a := coefficientMap (Λ := c.obj ell) (Λ' := Λ.X) e.hom.hom.hom T
  have : IsIso a := by dsimp [a, coefficientMap]; infer_instance
  have : PreservesFiniteLimits (Mod.extendScalars a) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv a).symm
  exact (Mod.extendScalars a).singleFunctorCompLeftDerivedFunctorIso.app _

private theorem frame_retract
    {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (G : D ⥤ C) (η : 𝟭 C ≅ F ⋙ G)
    (U : C) (V : D) (ε : G.obj V ≅ U) (M : C)
    (h : Nonempty (F.obj M ≅ V)) : Nonempty (M ≅ U) := by
  obtain ⟨q⟩ := h
  exact ⟨η.app M ≪≫ G.mapIso q ≪≫ ε⟩

private theorem frame_map
    {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (U : C) (V : D) (ε : F.obj U ≅ V)
    (M : C) (h : Nonempty (M ≅ U)) : Nonempty (F.obj M ≅ V) := by
  obtain ⟨q⟩ := h
  exact ⟨F.mapIso q ≪≫ ε⟩

private theorem point_cover_split (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage (Spec (.of k))) :
    ∃ i : C.I₀, ∃ σ : Spec (.of k) ⟶ C.X i, σ ≫ C.f i = 𝟙 _ := by
  let S := Spec (.of k)
  let x : S := IsLocalRing.closedPoint k
  have hc := (show Scheme.proetalePrecoverage ≤ Scheme.precoverage @WeaklyEtale from
    inf_le_right) _ C.mem₀
  obtain ⟨i, y, _⟩ := (Scheme.presieve₀_mem_precoverage_iff C.toPreZeroHypercover).mp hc |>.1 x
  have : WeaklyEtale (C.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ C.mem₀ ⟨i⟩
  obtain ⟨σ, hσ⟩ := exists_comp_eq_id_of_weaklyEtale (C.f i) y
  exact ⟨i, σ, hσ⟩

private theorem point_trivial_of_cover
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] (k : Type u) [Field k] [IsAlgClosed k]
    (L : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj A (Spec (.of k))))
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage (Spec (.of k)))
    (hC : ∀ i : C.I₀, Nonempty ((CondensedRing.upperStar A (C.f i)).obj L ≅ 𝟙_ _)) :
    Nonempty (L ≅ 𝟙_ _) := by
  obtain ⟨i, σ, hσ⟩ := point_cover_split k C
  let S := Spec (.of k)
  exact frame_retract (CondensedRing.upperStar A (C.f i)) (CondensedRing.upperStar A σ)
    ((upperStarId A S).symm ≪≫ upperStarCongr A hσ.symm ≪≫ upperStarComp A σ (C.f i))
    (𝟙_ _) (𝟙_ _) (upperStarObjRegularIso A σ) L (hC i)

private theorem native_point_frame (k : Type u) [Field k] [IsAlgClosed k]
    [∀ x : Spec (.of k), Invertible (ell : (Spec (.of k)).residueField x)] (d : ℕ) :
    Nonempty (c.line ell (Spec (.of k)) d ≅ 𝟙_ _) := by
  obtain ⟨C, hC⟩ := line_locally_unit ell c (Spec (.of k))
  exact point_trivial_of_cover (c.obj ell) k _ C (fun i ↦ hC i d)

private theorem extend_point_frame
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a] (S : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj A S))
    (h : Nonempty (M ≅ 𝟙_ _)) :
    Nonempty ((Mod.extendScalars (coefficientMap a S)).obj M ≅ 𝟙_ _) := by
  exact frame_map (Mod.extendScalars (coefficientMap a S)) (𝟙_ _) (𝟙_ _)
    (Mod.unitComparisonIso _) M h

private theorem pairing_point_trivial (k : Type u) [Field k] [IsAlgClosed k]
    [∀ x : Spec (.of k), Invertible (ell : (Spec (.of k)).residueField x)] (d : ℕ) :
    Nonempty (pairingPointLine ell Λ c e (Spec (.of k)) d ≅ 𝟙_ _) :=
  extend_point_frame (c.obj ell) Λ.X e.hom.hom.hom (Spec (.of k))
    (c.line ell (Spec (.of k)) d) (native_point_frame ell c k d)

/-- The unit comparison for the exact inverse image, built from the ordinary
cartesian regular-module map and the canonical single-complex comparisons.
Source: cartesian coefficients (blueprint: prop-pod-degree-of-the-pairing). -/
def pairingPullUnitIso {T S : Scheme.{u}} (f : T ⟶ S) :
    (scalarSixPull Λ f).obj (𝟙_ _) ≅ 𝟙_ _ :=
  (scalarSixPull Λ f).mapIso (DerivedCategory.singleFunctorObjUnitIso _).symm ≪≫
    ((upperStar Λ.X f).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (upperStarObjRegularIso Λ.X f) ≪≫
    DerivedCategory.singleFunctorObjUnitIso _

/-- A point-line section as a map from the derived regular unit, using the
published terminal-section equivalence and the exact scalar-extension comparison.
Source: point-line sections (blueprint: prop-pod-degree-of-the-pairing). -/
def pairingLineSection (S : Scheme.{u}) (d : ℕ)
    (z : (CohomologyTransport.sections Λ.X S).obj (pairingPointLine ell Λ c e S d)) :
    𝟙_ _ ⟶ smoothTraceCoefficientLine ell Λ c e S d :=
  (DerivedCategory.singleFunctorObjUnitIso _).inv ≫
    (DerivedCategory.singleFunctor _ 0).map
      (GlobalTwistInterchange.sectionArrow Λ.X S (pairingPointLine ell Λ c e S d) z) ≫
    (pairingLineSingleIso ell Λ c e S d).inv

/-- The signed inverse of the positive point line, using the recorded signed
coefficient convention. Taking exponent -1 of Lambda(d) is Lambda(-d).
Source: inverse Tate twist (blueprint: prop-pod-degree-of-the-pairing). -/
abbrev pairingInversePointLine (S : Scheme.{u}) (d : ℕ) :=
  coefficientSignedTwist S (condensedRingObj Λ.X S) (pairingPointLine ell Λ c e S d) (-1)

/-- The actual inverse twist in the derived category, using the recorded
coefficientTwistFunctor applied to the regular unit.
Source: inverse Tate twist (blueprint: prop-pod-degree-of-the-pairing). -/
abbrev pairingInverseComplex (S : Scheme.{u}) (d : ℕ) :=
  (coefficientTwistFunctor S (condensedRingObj Λ.X S)
    (pairingPointLine ell Λ c e S d) (-1)).obj (𝟙_ _)

/-- The unit comparison between the recorded inverse twisting functor at the
unit and its actual ordinary inverse line in degree zero.
Source: inverse Tate twist (blueprint: prop-pod-degree-of-the-pairing). -/
def pairingInverseRealization (S : Scheme.{u}) (d : ℕ) :
    pairingInverseComplex ell Λ c e S d ≅
      (DerivedCategory.singleFunctor _ 0).obj (pairingInversePointLine ell Λ c e S d) :=
  λ_ _

/-- Lambda(-d) is H^0 of the actual negative point twist after exact scalar sections.
Source: inverse point line (blueprint: prop-pod-degree-of-the-pairing). -/
abbrev pairingInverseSections (k : Type u) [Field k] [IsAlgClosed k] (d : ℕ) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (condensedScalarRing Λ.X)) 0).obj
    ((CohomologyTransport.sections Λ.X (Spec (.of k))).mapDerivedCategory.obj
      (pairingInverseComplex ell Λ c e (Spec (.of k)) d))

/-- Exact scalar sections and the single-complex comparison read a class of
Lambda(-d) as an ordinary section of the inverse point line.
Source: inverse-line sections (blueprint: prop-pod-degree-of-the-pairing). -/
def pairingInverseSectionValue (k : Type u) [Field k] [IsAlgClosed k] (d : ℕ) :
    pairingInverseSections ell Λ c e k d ⟶
      (CohomologyTransport.sections Λ.X (Spec (.of k))).obj
        (pairingInversePointLine ell Λ c e (Spec (.of k)) d) :=
  (DerivedCategory.homologyFunctor _ 0).map
    ((CohomologyTransport.sections Λ.X (Spec (.of k))).mapDerivedCategory.map
      (pairingInverseRealization ell Λ c e (Spec (.of k)) d).hom ≫
      ((CohomologyTransport.sections Λ.X (Spec (.of k))).mapDerivedCategorySingleFunctor
        0).hom.app _) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).hom.app _

/-- Canonical evaluation of the actual inverse twist against the positive line.
The signed convention uses Hom(unit tensor L,unit); its left unitor inserts L
in that evaluation. Exact point sections and H^0 read the resulting scalar.
Source: tensor--Hom untwisting (blueprint: prop-pod-degree-of-the-pairing). -/
def pairingInverseEvaluation (k : Type u) [Field k] [IsAlgClosed k] (d : ℕ)
    (v : pairingInverseSections ell Λ c e k d)
    (z : (CohomologyTransport.sections Λ.X (Spec (.of k))).obj
      (pairingPointLine ell Λ c e (Spec (.of k)) d)) : condensedScalarRing Λ.X :=
  let S := Spec (.of k)
  let L := pairingPointLine ell Λ c e S d
  let V := pairingInversePointLine ell Λ c e S d
  let ε := (λ_ (𝟙_ _)).inv ≫
    ((GlobalTwistInterchange.sectionArrow Λ.X S L z ≫ (λ_ L).inv) ⊗ₘ
      GlobalTwistInterchange.sectionArrow Λ.X S V
        ((pairingInverseSectionValue ell Λ c e k d).hom v)) ≫
    (ihom.ev (𝟙_ _ ⊗ L)).app (𝟙_ _)
  identificationScalarValue
    ((pairingExactScalarPointCup_unitIso Λ.X k).hom ≫
      (CohomologyTransport.sections Λ.X S).mapDerivedCategory.map
        ((DerivedCategory.singleFunctorObjUnitIso _).inv ≫
          (DerivedCategory.singleFunctor _ 0).map ε ≫
          (DerivedCategory.singleFunctorObjUnitIso _).hom) ≫
      (pairingExactScalarPointCup_unitIso Λ.X k).inv)

private theorem inverse_frame
    {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]
    (L : C) (t : 𝟙_ C ≅ L) :
    ∃ v : 𝟙_ C ≅ (ihom (𝟙_ C ⊗ L)).obj (𝟙_ C),
      (λ_ (𝟙_ C)).inv ≫ ((t.hom ≫ (λ_ L).inv) ⊗ₘ v.hom) ≫
        (ihom.ev (𝟙_ C ⊗ L)).app (𝟙_ C) = 𝟙 _ := by
  let a : 𝟙_ C ⊗ L ≅ 𝟙_ C := λ_ L ≪≫ t.symm
  have : IsIso (MonoidalClosed.curry' (𝟙 (𝟙_ C))) := by
    dsimp only [MonoidalClosed.curry']
    rw [Category.comp_id, ← unitors_equal]
    infer_instance
  let v := asIso (MonoidalClosed.curry' (𝟙 (𝟙_ C))) ≪≫
    CategoryTheory.ihomIsoOfIso a.symm (Iso.refl (𝟙_ C))
  have hv : v.hom = MonoidalClosed.curry' a.hom := by
    dsimp only [v, Iso.trans_hom, asIso_hom]
    rw [CategoryTheory.curry'_comp_ihomIsoOfIso_hom]
    simp
  refine ⟨v, ?_⟩
  rw [unitors_inv_equal, MonoidalCategory.rightUnitor_inv_comp_tensorHom_assoc, hv,
    MonoidalClosed.whiskerLeft_curry'_ihom_ev_app, Iso.inv_hom_id_assoc]
  simp [a]

private theorem inverse_section_isIso (k : Type u) [Field k] [IsAlgClosed k] (d : ℕ) :
    IsIso (pairingInverseSectionValue ell Λ c e k d) := by
  dsimp only [pairingInverseSectionValue]
  infer_instance

private theorem pairing_inverse_duality
    (k : Type u) [Field k] [IsAlgClosed k]
    [∀ x : Spec (.of k), Invertible (ell : (Spec (.of k)).residueField x)] (d : ℕ) :
    ∃ J : pairingInverseSections ell Λ c e k d ≃ₗ[condensedScalarRing Λ.X]
        Module.Dual (condensedScalarRing Λ.X)
          ((CohomologyTransport.sections Λ.X (Spec (.of k))).obj
            (pairingPointLine ell Λ c e (Spec (.of k)) d)),
      ∀ v z, J v z = pairingInverseEvaluation ell Λ c e k d v z := by
  classical
  let S := Spec (.of k)
  let R := condensedScalarRing Λ.X
  let L := pairingPointLine ell Λ c e S d
  let V := pairingInversePointLine ell Λ c e S d
  obtain ⟨t⟩ := pairing_point_trivial ell Λ c e k d
  obtain ⟨qL, hqL⟩ := point_section_frame Λ k L t.symm
  obtain ⟨v, hv⟩ := inverse_frame L t.symm
  obtain ⟨qV₀, hqV₀⟩ := point_section_frame Λ k V v
  let := inverse_section_isIso ell Λ c e k d
  let eV := (asIso (pairingInverseSectionValue ell Λ c e k d)).toLinearEquiv
  let qV := qV₀.trans eV.symm
  have hqV (r : R) :
      (pairingInverseSectionValue ell Λ c e k d).hom (qV r) = qV₀ r :=
    eV.apply_symm_apply _
  obtain ⟨B, hB⟩ := inverse_evaluation_bilinear ell Λ c e k d
  have hframe : B (qV 1) (qL 1) = 1 := by
    rw [hB]
    dsimp only [pairingInverseEvaluation]
    rw [hqV, hqL, hqV₀, hv]
    have he : (DerivedCategory.singleFunctorObjUnitIso
        (ModuleRingedComparison.internalModules Λ.X S)).inv ≫
        (DerivedCategory.singleFunctor _ 0).map (𝟙 (𝟙_ _)) ≫
        (DerivedCategory.singleFunctorObjUnitIso _).hom = 𝟙 _ := by simp
    rw [he, CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id]
    change identificationScalarValue (𝟙 _) = 1
    simp [identificationScalarValue]
  have hp (x : pairingInverseSections ell Λ c e k d)
      (y : (CohomologyTransport.sections Λ.X S).obj L) :
      qV.symm x * qL.symm y = pairingInverseEvaluation ell Λ c e k d x y := by
    have hx : qV.symm x • qV 1 = x := by
      rw [← map_smul, smul_eq_mul, mul_one, LinearEquiv.apply_symm_apply]
    have hy : qL.symm y • qL 1 = y := by
      rw [← map_smul, smul_eq_mul, mul_one, LinearEquiv.apply_symm_apply]
    rw [← hB]
    calc
      qV.symm x * qL.symm y =
          B (qV.symm x • qV 1) (qL.symm y • qL 1) := by
        simp only [map_smul, LinearMap.smul_apply, hframe, smul_eq_mul, mul_one]
        exact mul_comm _ _
      _ = B x y := by rw [hx, hy]
  have hcoord (x : pairingInverseSections ell Λ c e k d)
      (y : (CohomologyTransport.sections Λ.X S).obj L) :
      B x y = qV.symm x * qL.symm y := (hB x y).trans (hp x y).symm
  have hbij : Function.Bijective B := by
    constructor
    · intro x y h
      apply qV.symm.injective
      have hh := congrArg (fun f ↦ f (qL 1)) h
      simpa only [hcoord, LinearEquiv.symm_apply_apply, mul_one] using hh
    · intro f
      refine ⟨qV (f (qL 1)), ?_⟩
      apply LinearMap.ext
      intro y
      rw [hcoord, LinearEquiv.symm_apply_apply, mul_comm]
      have hy : qL.symm y • qL 1 = y := by
        rw [← map_smul, smul_eq_mul, mul_one, LinearEquiv.apply_symm_apply]
      change qL.symm y • f (qL 1) = f y
      rw [← f.map_smul, hy]
  exact ⟨LinearEquiv.ofBijective B hbij, hB⟩

end WeilConjectures.PoincareDuality
