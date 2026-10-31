/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift

import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.SixFunctors.ScalarSixFiniteGeneration
import WeilConjectures.SixFunctors.ScalarSixNonfiniteGeneration
import WeilConjectures.SixFunctors.ScalarSixAdmissibleThickness
import WeilConjectures.SixFunctors.ScalarSixPerfectExtension
import WeilConjectures.SixFunctors.ScalarSixCanonicalExtensionComparison

/-! # Admissibility and scalar preservation for the listed coefficient presentations

Source: blueprint latest, scalar-six coefficient list and
`det-prop-scalar-six-direct-image.proof.md`, Preservation.
(blueprint: lem-sfb-listed-coefficient-ctf).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard
  Functor.leftDerivedFunctor

open scoped CategoryTheory.MonoidalClosed in
/-- Shrink a finite discrete coefficient ring to Type 0. Postcomposition by the
ring equivalence supplies the condensed ring isomorphism, and transports the
annihilating power. Source: blueprint coefficient convention (1), as in
FiniteProperLocalizing.finiteDiscreteCoefficient_admissible.
(blueprint: lem-sfb-listed-coefficient-ctf). -/
private theorem listedCtf_finite_admissible
    (ℓ : ℕ) [Fact ℓ.Prime] (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) :
    IsLocalizingAdmissibleCoefficient ℓ (cartesianFinitePointRing A) := by
  classical
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  let : IsTopologicalRing A := by infer_instance
  let B := Shrink.{0} A
  let : TopologicalSpace B := ⊥
  let : DiscreteTopology B := ⟨rfl⟩
  let : IsTopologicalRing B := by infer_instance
  let e : A ≃+* B := (Shrink.ringEquiv.{0} A).symm
  let h : Profinite.continuousMapRingSheafOfUniverse.{u, u} A ⟶
      Profinite.continuousMapRingSheaf.{u} B :=
    ⟨{ app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((e.toRingHom.compLeftContinuous S.unop (continuous_of_discreteTopology)).comp
            ULift.ringEquiv.toRingHom))
       naturality := by intros; rfl }⟩
  let v : Profinite.continuousMapRingSheaf.{u} B ⟶
      Profinite.continuousMapRingSheafOfUniverse.{u, u} A :=
    ⟨{ app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((e.symm.toRingHom.compLeftContinuous S.unop (continuous_of_discreteTopology)).comp
            ULift.ringEquiv.toRingHom))
       naturality := by intros; rfl }⟩
  let E : Profinite.continuousMapRingSheafOfUniverse.{u, u} A ≅
      Profinite.continuousMapRingSheaf.{u} B :=
    { hom := h
      inv := v
      hom_inv_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.symm_apply_apply _
      inv_hom_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.apply_symm_apply _ }
  let E' := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso E
  let : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
  let eh := presheaf_enrichedHoms_exist
    (C := Profinite.{u}) (A := Ab.{u + 1})
  let : ∀ (F G : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}),
    Enriched.FunctorCategory.HasEnrichedHom Ab.{u + 1} F G := eh.1
  let : ∀ (F G : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}),
    Enriched.FunctorCategory.HasFunctorEnrichedHom Ab.{u + 1} F G := eh.2
  let : ((coherentTopology Profinite.{u}).W (A := Ab.{u + 1})).IsMonoidal :=
    GrothendieckTopology.W.monoidal
  let hmon : IsMonHom E'.hom := Sheaf.isMonHom_sheafCompose_map _ E.hom
  refine Or.inl ⟨B, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_, ⟨Mon.mkIso' E'⟩⟩
  obtain ⟨n, hn⟩ := hA
  refine ⟨n, fun b ↦ ?_⟩
  have hn' : (ℓ ^ n : ℕ) • (1 : B) = 0 := by
    simpa only [map_nsmul, map_one, map_zero] using congrArg e (hn 1)
  simpa only [nsmul_eq_mul, mul_one, zero_mul] using congrArg (fun x : B ↦ x * b) hn'

/-- A thick property containing the generators contains their finite shift,
extension and retract closure. Source: Mathlib finite closure universal properties.
(blueprint: lem-sfb-listed-coefficient-ctf). -/
private theorem listedCtf_finiteClosure_le
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (G Q : ObjectProperty C) [Q.IsTriangulated] [Q.IsStableUnderRetracts]
    (hG : G ≤ Q) (n : ℕ) :
    ((G.shiftClosure ℤ).extensionProductIter n).retractClosure ≤ Q := by
  apply (ObjectProperty.retractClosure_le_iff _ Q).mpr
  apply ObjectProperty.extensionProductIter_le_of_isTriangulatedClosed₂
  exact (ObjectProperty.shiftClosure_le_iff G Q).mpr hG

/-- Apply the two scalar-model comparisons on the given cover, retaining its
bounds and finite-projective splittings. Source: scalar-six Ctf proof (2).
(blueprint: lem-sfb-listed-coefficient-ctf). -/
private theorem listedCtf_locallyPerfect {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
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

/-- The endpoints of a listed map are admissible, and its actual scalar-change
functor preserves bounded constructible objects of finite Tor amplitude.

Source: blueprint latest, scalar-six coefficient list (1)--(4),
`det-prop-scalar-six-ctf` (3), and direct-image proof, Preservation.
(blueprint: lem-sfb-listed-coefficient-ctf).

Proof: Endpoint admissibility follows by induction on ListedCoefficientMap.
For finite rings use the discrete ring Shrink A in Type 0 and postcomposition
with its ring equivalence; the annihilating ell-power transports along it.
Integral, field and algebraic-closure endpoints use their defining disjuncts.
For preservation, the finite and nonfinite scalar-generation theorems express K
using finitely many shifts, extensions and retracts of locally closed extensions
of locally perfect scalar models. Derived scalar change preserves these models
for any ring map: tensoring a bounded finite-projective scalar complex retains
its bounds and projective splittings. The canonical locally closed extension
comparison then identifies the changed generators. Admissibility of the target
and sfbPerfectLocallyClosedExtension put them in Dctf. Target constructibility
and finite Tor amplitude are thick, and derived scalar change is triangulated
and preserves retracts. Induction on the finite construction proves preservation.
Thus no normalization of the actual map, flatness, or scalar-tower transport is
needed. Empty schemes and zero finite rings use the same finite constructions. -/
theorem listedCoefficientCtf (ell : ℕ) [Fact ell.Prime]
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (ha : ListedCoefficientMap ell a) :
    IsLocalizingAdmissibleCoefficient ell Λ.X ∧
    IsLocalizingAdmissibleCoefficient ell Λ'.X ∧
    (∀ (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
      (X : Over (Spec (.of k)))
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X.left)),
      (constantModelBoundedConstructible Λ.X X.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      constantModelBoundedConstructible Λ'.X X.left ((scalarSixChange a X.left).obj K) ∧
        DerivedCategory.finiteTorAmplitude _ ((scalarSixChange a X.left).obj K)) := by
  classical
  have integral_case (E : PadicAlgCl.FiniteIntermediateField ell) :
      IsLocalizingAdmissibleCoefficient ell (Profinite.padicIntegersRingObj ell E) := by
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩))))
  have field_case (E : PadicAlgCl.FiniteIntermediateField ell) :
      IsLocalizingAdmissibleCoefficient ell (Profinite.continuousMapRingObj E) :=
    Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩)))
  have closure_case : IsLocalizingAdmissibleCoefficient ell
      (Profinite.padicAlgClRingObj ell) :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))))
  have endpoints : IsLocalizingAdmissibleCoefficient ell Λ.X ∧
      IsLocalizingAdmissibleCoefficient ell Λ'.X := by
    induction ha with
    | finite A B hA hB φ a ha =>
      exact ⟨listedCtf_finite_admissible ell A hA, listedCtf_finite_admissible ell B hB⟩
    | integers E F h a ha => exact ⟨integral_case E, integral_case F⟩
    | fields E F h a ha => exact ⟨field_case E, field_case F⟩
    | localization E a ha => exact ⟨integral_case E, field_case E⟩
    | algebraicClosure E a ha => exact ⟨field_case E, closure_case⟩
    | integralFinite E A hA a ha =>
      exact ⟨integral_case E, listedCtf_finite_admissible ell A hA⟩
    | algebraicClosureIdentity => exact ⟨closure_case, closure_case⟩
    | comp a b ha hb ihA ihB => exact ⟨ihA.1, ihB.2⟩
  obtain ⟨hΛ, hΛ'⟩ := endpoints
  refine ⟨hΛ, hΛ', ?_⟩
  intro k _ _ _ X _ _ _ K hK
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
    have hp := listedCtf_locallyPerfect a S P hP
    exact ⟨hp, sfbPerfectLocallyClosedExtension ell Λ' hΛ' k X S i hi _ hp⟩
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
  obtain ⟨n, hn⟩ := generation ⟨K, hK⟩
  exact listedCtf_finiteClosure_le (sfbPerfectScalarGenerator Λ X) R generators n K hn

end AlgebraicGeometry.ProEtale.CondensedRing
