/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Locally.LocallyPerfectScalarModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators

import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixFiniteGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixNonfiniteGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixPerfectExtension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison

/-! # Extension of scalars preserves constructible finite-Tor complexes

Source: blueprint sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-ctf, clauses (1)--(3).
(blueprint: det-prop-scalar-six-ctf).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard

private theorem scalarSix_admissible_iso (ell : ℕ) [Fact ell.Prime]
    {Λ Γ : ScalarSixRing.{u}} (e : Γ ≅ Λ)
    (hΛ : IsLocalizingAdmissibleCoefficient ell Λ.X) :
    IsLocalizingAdmissibleCoefficient ell Γ.X := by
  let eM := (CommMon.forget₂Mon _).mapIso e
  rcases hΛ with h | h | h | h | h | h
  · obtain ⟨A, hA, tA, dA, rA, hf, hn, ⟨h⟩⟩ := h
    exact Or.inl ⟨A, hA, tA, dA, rA, hf, hn, ⟨eM ≪≫ h⟩⟩
  · exact Or.inr (Or.inl ⟨eM ≪≫ h.some⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨eM ≪≫ h.some⟩))
  · obtain ⟨E, ⟨h⟩⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨eM ≪≫ h⟩⟩)))
  · obtain ⟨E, ⟨h⟩⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨eM ≪≫ h⟩⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨eM ≪≫ h.some⟩))))

private theorem scalarSix_listed_admissible (ell : ℕ) [Fact ell.Prime]
    {Λ Λ' : ScalarSixRing.{u}} {a : Λ ⟶ Λ'}
    (ha : IsListedScalarCoefficientMap ell a) :
    IsLocalizingAdmissibleCoefficient ell Λ.X ∧
      IsLocalizingAdmissibleCoefficient ell Λ'.X := by
  have finite_case (A : Type) [CommRing A] [TopologicalSpace A]
      [IsTopologicalRing A] [DiscreteTopology A] [Finite A]
      (n : ℕ) (hA : (ell : A) ^ n = 0) :
      IsLocalizingAdmissibleCoefficient ell (scalarSixTopologicalRing.{u} A).X := by
    refine Or.inl ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, ⟨n, fun x ↦ ?_⟩, ⟨Iso.refl _⟩⟩
    simp only [nsmul_eq_mul, Nat.cast_pow, hA, zero_mul]
  have integral_case (E : PadicAlgCl.FiniteIntermediateField ell) :
      IsLocalizingAdmissibleCoefficient ell (latticeIntegralRing.{u} ell E).X :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩))))
  have field_case (E : PadicAlgCl.FiniteIntermediateField ell) :
      IsLocalizingAdmissibleCoefficient ell (scalarSixFieldRing.{u} ell E).X :=
    Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩)))
  induction ha with
  | finite n m hA hB f hf =>
    exact ⟨finite_case _ n hA, finite_case _ m hB⟩
  | integral h => exact ⟨integral_case _, integral_case _⟩
  | field h => exact ⟨field_case _, field_case _⟩
  | localization E => exact ⟨integral_case E, field_case E⟩
  | algebraicClosure E =>
    exact ⟨field_case E, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))))⟩
  | integralFinite E n hA f hf => exact ⟨integral_case E, finite_case _ n hA⟩
  | comp ha hb ihA ihB => exact ⟨ihA.1, ihB.2⟩
  | iso e e' ha ih =>
    exact ⟨scalarSix_admissible_iso ell e ih.1,
      scalarSix_admissible_iso ell e'.symm ih.2⟩

private theorem scalarSix_finiteClosure_le
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (G Q : ObjectProperty C) [Q.IsTriangulated] [Q.IsStableUnderRetracts]
    (hG : G ≤ Q) (n : ℕ) :
    ((G.shiftClosure ℤ).extensionProductIter n).retractClosure ≤ Q := by
  apply (ObjectProperty.retractClosure_le_iff _ Q).mpr
  apply ObjectProperty.extensionProductIter_le_of_isTriangulatedClosed₂
  exact (ObjectProperty.shiftClosure_le_iff G Q).mpr hG

private theorem scalarSix_locallyPerfect {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (S : Scheme.{u})
    (P : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S))
    (hP : IsLocallyPerfectScalarModel Λ.X S P) :
    IsLocallyPerfectScalarModel Λ'.X S ((scalarSixChange a S).obj P) := by
  classical
  obtain ⟨𝒰, h𝒰⟩ := hP
  choose C l h hl hh hp e using h𝒰
  have hc := sfbPerfectScalarChangeModel (Λ := Λ.X) (Λ' := Λ'.X)
    a.hom.hom S P 𝒰 C
    (fun j ↦ ⟨l j, h j, hl j, hh j⟩) hp (fun j ↦ (e j).some)
  refine ⟨𝒰, fun j ↦ ?_⟩
  have hb := sfbPerfectScalarChangeModels (Λ := Λ.X) (Λ' := Λ'.X)
    a.hom.hom (𝒰.X j) (C j) (l j) (h j)
    (hl j) (hh j) (hp j)
  refine ⟨sfbScalarChangedComplex (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom (C j),
    l j, h j,
    hb.1, hb.2.1, hb.2.2.1, ?_⟩
  exact ⟨(hc j).1.some ≪≫ (hc j).2.some⟩

/-- The three scalar-six finite-Tor assertions, for all listed maps and their composites.
Finite projective means a retract of a finite free scalar module; the local model uses
its constant sheaf. The finite extension-product iteration, shifts and retract closure
are Mathlib's finitary operations, without any infinite coproduct closure.
Source: blueprint det-prop-scalar-six-ctf (1)--(3)
(blueprint: det-prop-scalar-six-ctf).

Proof:
1. A standing scheme is Noetherian by lem-weil-pbc-finite-type-over-noetherian.
For finite coefficients the two finite-discrete constant-ring comparisons identify the
flat-model generators of det-sf-flat-model-generation. For integral coefficients apply
det-lem-int-tensor-shriek to K in Dctf, hence Dbc. For fields apply
 det-cor-coefficient-heart-ii-generation and the lisse description sk-lem-coefficient-heart.
Rotate cone triangles into extensions. These are finite constructions, including Q_l.
2. On every pro-etale chart use lem-sfb-perfect-scalar-change-model. Ordinary tensor
carries each finite-projective splitting to a finite-projective splitting, retaining
boundedness without any flatness assumption on the map. Thus the changed P is locally
perfect. lem-sfb-admissible-scalar-model-cohomology gives exact scalar realization and
finite scalar cohomology; lem-sfb-stratum-perfect-uniform-bounds gives common bounds,
constructibility and finite Tor amplitude on S. Both S and X are standing schemes,
and a is separated finite type. det-thm-sf-ctf-stability-direct-images (2) then gives
constructibility and finite Tor amplitude of i_*u_! of the changed P.
3. For finite coefficients, lem-sfb-finite-ctf-retract-etale-images gives retract closure.
lem-weil-proetale-dbc-triangulated and the Tor-amplitude well-definedness theorem give
triangle and shift closure. For integral and field coefficients use ambient kernel and
cokernel closure from det-lem-int-integral-heart-triangulated and sk-lem-coefficient-heart;
cohomology of a retract is the kernel of its complementary idempotent with the same
vanishing range. Their triangulated assertions and det-cor-coefficient-heart-ii-triangulated,
intersected with finite Tor amplitude, give thickness. Scalar change is exact by
lem-pur-derived-change-of-rings and preserves retracts functorially. By
 det-prop-scalar-six-pullback (2) it sends a_!P to a_! of the changed P. Apply (2) and
induct on the finite construction (1). For composites iterate and use its scalar-tower
isomorphism (3); the local scalar-model calculation also works for the composite. -/
theorem scalarSixCtf (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (ha : IsListedScalarCoefficientMap ell a)
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    (∀ K : ConstantModelConstructibleFiniteTor Λ.X X.left, ∃ n : ℕ,
      (((sfbPerfectScalarGenerator Λ X).shiftClosure ℤ).extensionProductIter n
        ).retractClosure K.obj) ∧
    (∀ (S : Scheme.{u}) (i : S ⟶ X.left) (hi : IsImmersion i)
      (P : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S)),
      IsLocallyPerfectScalarModel Λ.X S P →
        IsLocallyPerfectScalarModel Λ'.X S ((scalarSixChange a S).obj P) ∧
        constantModelBoundedConstructible Λ'.X X.left
          ((sfbLocallyClosedDerivedExtension Λ' i hi).obj ((scalarSixChange a S).obj P)) ∧
        DerivedCategory.finiteTorAmplitude _
          ((sfbLocallyClosedDerivedExtension Λ' i hi).obj ((scalarSixChange a S).obj P))) ∧
    (∀ K : ConstantModelConstructibleFiniteTor Λ.X X.left,
      constantModelBoundedConstructible Λ'.X X.left ((scalarSixChange a X.left).obj K.obj) ∧
        DerivedCategory.finiteTorAmplitude _ ((scalarSixChange a X.left).obj K.obj)) := by
  obtain ⟨hΛ, hΛ'⟩ := scalarSix_listed_admissible ell ha
  have generation (K : ConstantModelConstructibleFiniteTor Λ.X X.left) :
      ∃ n : ℕ, (((sfbPerfectScalarGenerator Λ X).shiftClosure ℤ).extensionProductIter n
        ).retractClosure K.obj := by
    rcases hΛ with hfinite | hother
    · obtain ⟨A, hA, tA, dA, rA, hf, hn, ⟨e⟩⟩ := hfinite
      let := hA
      let := tA
      let := dA
      let := rA
      let := hf
      exact sfbFiniteScalarGeneration A e X K
    · exact sfbNonfiniteScalarGeneration ell hother k X K
  have models (S : Scheme.{u}) (i : S ⟶ X.left) (hi : IsImmersion i)
      (P : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S))
      (hP : IsLocallyPerfectScalarModel Λ.X S P) :
      IsLocallyPerfectScalarModel Λ'.X S ((scalarSixChange a S).obj P) ∧
      constantModelBoundedConstructible Λ'.X X.left
        ((sfbLocallyClosedDerivedExtension Λ' i hi).obj ((scalarSixChange a S).obj P)) ∧
      DerivedCategory.finiteTorAmplitude _
        ((sfbLocallyClosedDerivedExtension Λ' i hi).obj ((scalarSixChange a S).obj P)) := by
    have hp := scalarSix_locallyPerfect a S P hP
    exact ⟨hp, sfbPerfectLocallyClosedExtension ell Λ' hΛ' k X S i hi _ hp⟩
  refine ⟨generation, models, ?_⟩
  let F := scalarSixChange a X.left
  let Q := constantModelBoundedConstructible Λ'.X X.left ⊓
    DerivedCategory.finiteTorAmplitude (ModuleRingedComparison.internalModules Λ'.X X.left)
  obtain ⟨ht, hr⟩ := sfbAdmissibleConstructibleThickness ell Λ' hΛ' k X
  have : (constantModelBoundedConstructible Λ'.X X.left).IsTriangulated := ht
  have : (constantModelBoundedConstructible Λ'.X X.left).IsStableUnderRetracts := hr
  have htor := constantModelConstructibleFiniteTor_wellDefined Λ'.X X.left
  have : (DerivedCategory.finiteTorAmplitude
      (ModuleRingedComparison.internalModules Λ'.X X.left)).IsTriangulated :=
    htor.2.2.2.2.2.2.2.1
  have : (DerivedCategory.finiteTorAmplitude
      (ModuleRingedComparison.internalModules Λ'.X X.left)).IsStableUnderRetracts :=
    htor.2.2.2.2.2.2.2.2
  have : Q.IsTriangulated := inferInstance
  have : Q.IsStableUnderRetracts := ⟨fun r h ↦
    ⟨(constantModelBoundedConstructible Λ'.X X.left).prop_of_retract r h.1,
      (DerivedCategory.finiteTorAmplitude _).prop_of_retract r h.2⟩⟩
  let adj : F ⊣ (Mod.comap
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X.left)).mapDerivedCategory :=
    Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X.left)
  let : F.CommShift ℤ := adj.leftAdjointCommShift ℤ
  have : adj.CommShift ℤ := adj.commShift_of_rightAdjoint ℤ
  have : F.IsTriangulated := adj.isTriangulated_leftAdjoint
  let R := Q.inverseImage F
  have : R.IsTriangulated := inferInstance
  have : R.IsStableUnderRetracts :=
    ⟨fun r h ↦ Q.prop_of_retract (r.map F) h⟩
  have generators : sfbPerfectScalarGenerator Λ X ≤ R := by
    rintro K ⟨S, i, hi, P, hP, ⟨e⟩⟩
    obtain ⟨c⟩ := sfbCanonicalExtensionScalarComparison a ell k X S i hi P
    exact Q.prop_of_iso (F.mapIso e ≪≫ c).symm (models S i hi P hP).2
  intro K
  obtain ⟨n, hn⟩ := generation K
  exact scalarSix_finiteClosure_le (sfbPerfectScalarGenerator Λ X) R generators n K.obj hn

end AlgebraicGeometry.ProEtale.CondensedRing
