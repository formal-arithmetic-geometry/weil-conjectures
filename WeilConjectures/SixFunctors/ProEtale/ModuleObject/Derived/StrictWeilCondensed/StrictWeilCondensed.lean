/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SmoothPurity.WeilSheafComplex
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientFreeTensorLinear
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull
import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
public import WeilConjectures.SmoothPurity.CondensedWeilModules
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison

public import WeilConjectures.AlgebraicGeometry.TwistModelComparison
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportFiniteLines
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleUpperStar

/-! # Strict Weil complexes with actual condensed coefficients

Source: latest blueprint, part-duality-trace-formula/
sec-lefschetz-verdier/sec-frobenius/
sk-def-sf-weil-complexes/_section.md (blueprint: sk-def-sf-weil-complexes).

The category is the recorded fixed-pair category on the recorded finite-constant-model
Dctf. Its dual data live in the ambient derived category. No triangulated structure
on strict pairs, or automatic constructibility of duals, is asserted.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.StrictWeilCondensed

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Geometric Frobenius on any model, without a finite-type restriction.
Source: latest blueprint, semilinear automorphism paragraph
(blueprint: sk-def-sf-weil-complexes). -/
def modelFrobenius (D : WeilConjectures.FiniteFieldDatum.{u})
    (T₀ : Over (Spec (.of D.k₀))) :
    Aut (pullback T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) :=
  letI := Fintype.ofFinite D.k₀
  { hom := D.galoisMap T₀.hom
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)
    inv := D.galoisMap T₀.hom
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k).symm
    hom_inv_id := (D.galoisMap_inverse T₀.hom _).1
    inv_hom_id := (D.galoisMap_inverse T₀.hom _).2 }

/-- The exact module inverse image, applied termwise and localized.
Source: latest blueprint, P_T paragraph (blueprint: sk-def-sf-weil-complexes). -/
abbrev action {T : Scheme.{u}} (g : T ≅ T) :=
  (upperStar Λ g.hom).mapDerivedCategory

/-- An automorphism reindexes stratifications and preserves and reflects each Tor interval.
Source: latest blueprint, P_T paragraph (blueprint: sk-def-sf-weil-complexes).
Proof: inverse image along g and its inverse are exact inverse monoidal equivalences.
They transport covering families, finite scalar local models and locally closed strata.
Exactness commutes with homology, so bounded constructibility is preserved and reflected.
The tensorator identifies tensoring a pulled-back complex with a test module with the
pullback of the tensor with the inverse-pulled-back test module. Exactness preserves the
same vanishing interval; apply the inverse equivalence for the converse. -/
theorem action_preserves {T : Scheme.{u}} (g : T ≅ T)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))) :
    (constantModelBoundedConstructible Λ T ((action Λ g).obj K) ↔
      constantModelBoundedConstructible Λ T K) ∧
    (∀ a b : ℤ, DerivedCategory.torAmplitudeIn _ a b ((action Λ g).obj K) ↔
      DerivedCategory.torAmplitudeIn _ a b K) := by
  sorry

/-- The restriction of exact Frobenius inverse image to Dctf.
Source: latest blueprint, P_T paragraph (blueprint: sk-def-sf-weil-complexes).
Proof: use action_preserves on bounded constructibility and on the single finite
Tor interval witnessing finite Tor amplitude. -/
theorem action_mem {T : Scheme.{u}} (g : T ≅ T)
    (K : ConstantModelConstructibleFiniteTor Λ T) :
    (constantModelBoundedConstructible Λ T ⊓ fun L ↦
      DerivedCategory.finiteTorAmplitude _ L) ((action Λ g).obj K.obj) := by
  refine ⟨(action_preserves Λ g K.obj).1.mpr K.property.1, ?_⟩
  obtain ⟨a, b, h⟩ := K.property.2
  exact ⟨a, b, (action_preserves Λ g K.obj).2 a b |>.mpr h⟩

/-- The inverse of the exact derived action is pullback by the inverse automorphism.
Source: latest blueprint, inverse and monoidal equivalence clauses
(blueprint: sk-def-sf-weil-complexes).
Proof: inverse image composition and identity comparisons give both functor isomorphisms
on modules. Exact-functor localization descends them to the ordinary derived categories. -/
theorem action_inverse {T : Scheme.{u}} (g : T ≅ T) :
    Nonempty (action Λ g ⋙ action Λ g.symm ≅ 𝟭 _) ∧
    Nonempty (action Λ g.symm ⋙ action Λ g ≅ 𝟭 _) := by
  constructor
  · exact ⟨(Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        ((upperStarComp Λ g.inv g.hom).symm ≪≫
          upperStarCongr Λ g.inv_hom_id ≪≫ upperStarId Λ T) ≪≫
      Functor.mapDerivedCategoryIdIso _⟩
  · exact ⟨(Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        ((upperStarComp Λ g.hom g.inv).symm ≪≫
          upperStarCongr Λ g.hom_inv_id ≪≫ upperStarId Λ T) ≪≫
      Functor.mapDerivedCategoryIdIso _⟩

/-- Frobenius pullback as an endofunctor of the actual Dctf full subcategory.
Source: latest blueprint, P_T paragraph (blueprint: sk-def-sf-weil-complexes). -/
def smallAction {T : Scheme.{u}} (g : T ≅ T) :
    ConstantModelConstructibleFiniteTor Λ T ⥤ ConstantModelConstructibleFiniteTor Λ T :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ action Λ g) (action_mem Λ g)

/-- The restricted action is an autoequivalence, with the inverse restricted pullback.
Source: latest blueprint, P_T on Dctf (blueprint: sk-def-sf-weil-complexes).
Proof: action_mem applies to g and its inverse. The two isomorphisms of action_inverse
restrict through the fully faithful full-subcategory inclusion and give the equivalence. -/
theorem smallAction_isEquivalence {T : Scheme.{u}} (g : T ≅ T) :
    (smallAction Λ g).IsEquivalence := by
  obtain ⟨⟨e⟩, ⟨e'⟩⟩ := action_inverse Λ g
  let unit : 𝟭 _ ≅ smallAction Λ g ⋙ smallAction Λ g.symm :=
    NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _ (e.symm.app K.obj))
      (fun f ↦ ObjectProperty.hom_ext _ (e.inv.naturality f.hom))
  let counit : smallAction Λ g.symm ⋙ smallAction Λ g ≅ 𝟭 _ :=
    NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _ (e'.app K.obj))
      (fun f ↦ ObjectProperty.hom_ext _ (e'.hom.naturality f.hom))
  exact (CategoryTheory.Equivalence.mk (smallAction Λ g) (smallAction Λ g.symm)
    unit counit).isEquivalence_functor

/-- Strict pairs, with exactly the recorded commuting morphisms, identities and composition.
No smooth map is data of a pair. The admissible coefficient stages are all specializations
of this construction for a commutative condensed ring.
Source: latest blueprint, strict-pair paragraphs (blueprint: sk-def-sf-weil-complexes). -/
abbrev Complex {T : Scheme.{u}} (g : T ≅ T) :=
  CategoryTheory.Endofunctor.IsoAlgebra (smallAction Λ g)

/-- The faithful forgetful functor of strict pairs.
Source: latest blueprint, pair category paragraph (blueprint: sk-def-sf-weil-complexes). -/
abbrev forget {T : Scheme.{u}} (g : T ≅ T) :=
  CategoryTheory.Endofunctor.IsoAlgebra.forget (smallAction Λ g)

/-- Native Weil modules are the abelian fixed pairs before deriving.
Source: latest blueprint, native category paragraph (blueprint: sk-def-sf-weil-complexes). -/
abbrev WeilModule {T : Scheme.{u}} (g : T ≅ T) :=
  WeilConjectures.condensedWeilModules Λ g.hom

/-- For the stated field coefficients, Dctf has the same objects as the dependency's Dbc.
Source: latest blueprint, Complement, "they are the strict Weil complexes of
[def-weil-weil-sheaf-complex]" (blueprint: sk-def-sf-weil-complexes).
Proof: adicConstructibilityPredicateComparison identifies finite scalar constant models
with the dependency's locally finitely presented strata, including Qbar. Transport this
identification through the coefficient-ring isomorphism. The field case of
integral_ctf_equals_bc identifies bounded constant-model constructibility with its
intersection with finite Tor amplitude. Compose these two predicate equalities.
Noetherianity supplies the qcqs and locally Noetherian hypotheses of these results. -/
theorem field_ctf_eq_boundedConstructible {T : Scheme.{u}} [IsNoetherian T]
    (ell : ℕ) [Fact ell.Prime]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell))) :
    (constantModelBoundedConstructible Λ T ⊓ fun L ↦
      DerivedCategory.finiteTorAmplitude _ L) = boundedConstructible (condensedRingObj Λ T) := by
  have hcoef :
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ell])) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ell])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ell,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)) := by
    rcases hΛ with ⟨E, e⟩ | e
    · exact Or.inr (Or.inr (Or.inl ⟨E, Or.inr e⟩))
    · exact Or.inr (Or.inr (Or.inr e))
  have hmod (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T)) :
      IsConstructibleModuleObject (condensedRingObj Λ T) M ↔
        IsConstantModelConstructible Λ T M := by
    rcases hΛ with hΛ | hΛ
    · obtain ⟨E, ⟨e⟩⟩ := hΛ
      exact comparison_transport e.symm T
        (adicConstructibilityPredicateComparison ell T _ (.continuous E.1)).1 M
    · obtain ⟨e⟩ := hΛ
      exact comparison_transport e.symm T
        (adicConstructibilityPredicateComparison ell T _ .algebraicClosure).1 M
  refine (integral_ctf_equals_bc ell T (Mon.mk Λ) hcoef).2.2.2.trans ?_
  funext K
  apply propext
  exact and_congr_right fun _ ↦ forall_congr' fun n ↦ (hmod _).symm

/-- The identity on carriers and structure maps from Dctf pairs to the dependency's pairs.
Source: latest blueprint, identification of strict Weil complexes in the Complement
(blueprint: sk-def-sf-weil-complexes). -/
def toRecordedStrict {T : Scheme.{u}} [IsNoetherian T] (g : T ≅ T)
    (ell : ℕ) [Fact ell.Prime]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell))) :
    Complex Λ g ⥤ WeilConjectures.condensedStrictWeilComplex Λ g.hom where
  obj K := ⟨CategoryTheory.Endofunctor.IsoAlgebra.mk K.carrier.obj
      ((ObjectProperty.ι _).mapIso K.str),
    (congrFun (field_ctf_eq_boundedConstructible Λ ell hΛ) K.carrier.obj).mp
      K.carrier.property⟩
  map f := ObjectProperty.homMk (ObjectProperty.homMk
    { f := f.hom.f.hom
      h := congrArg (fun a ↦ a.hom) f.hom.h })

/-- Repackage the same carrier and Frobenius map in Dctf, using the field predicate equality.
Source: latest blueprint, identification of strict Weil complexes in the Complement
(blueprint: sk-def-sf-weil-complexes). -/
def fromRecordedStrict {T : Scheme.{u}} [IsNoetherian T] (g : T ≅ T)
    (ell : ℕ) [Fact ell.Prime]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell))) :
    WeilConjectures.condensedStrictWeilComplex Λ g.hom ⥤ Complex Λ g where
  obj K := CategoryTheory.Endofunctor.IsoAlgebra.mk
    ⟨K.obj.carrier,
      (congrFun (field_ctf_eq_boundedConstructible Λ ell hΛ) K.obj.carrier).mpr K.property⟩
    (ObjectProperty.isoMk _ K.obj.str)
  map f := ObjectProperty.homMk
    { f := ObjectProperty.homMk f.hom.hom.f
      h := ObjectProperty.hom_ext _ f.hom.hom.h }

/-- The canonical equivalence keeps each underlying complex, map and Weil structure.
Both directions are the explicit repackaging functors above; no equivalence is chosen.
Source: latest blueprint, Complement, identification with the dependency's strict pairs
(blueprint: sk-def-sf-weil-complexes). -/
def recordedStrictEquivalence {T : Scheme.{u}} [IsNoetherian T] (g : T ≅ T)
    (ell : ℕ) [Fact ell.Prime]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell))) :
    Complex Λ g ≌ WeilConjectures.condensedStrictWeilComplex Λ g.hom :=
  CategoryTheory.Equivalence.mk (toRecordedStrict Λ g ell hΛ)
    (fromRecordedStrict Λ g ell hΛ) (Iso.refl _) (Iso.refl _)

/-- The equivalence is compatible with the two actual forgetful functors.
Source: latest blueprint, "they are the strict Weil complexes" and the For clause
(blueprint: sk-def-sf-weil-complexes). -/
def recordedStrictForgetIso {T : Scheme.{u}} [IsNoetherian T] (g : T ≅ T)
    (ell : ℕ) [Fact ell.Prime]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell))) :
    (recordedStrictEquivalence Λ g ell hΛ).functor ⋙ ObjectProperty.ι _ ⋙
      CategoryTheory.Endofunctor.IsoAlgebra.forget (action Λ g) ≅
      forget Λ g ⋙ ObjectProperty.ι _ := Iso.refl _

section Native

open CategoryTheory.Endofunctor.IsoAlgebra

variable {T : Scheme.{u}} (g : T ≅ T)

/-- Bounded native derived Weil modules with constructible underlying cohomology.
Source: latest blueprint, native category paragraph (blueprint: sk-def-sf-weil-complexes). -/
abbrev Native :=
  WeilConjectures.condensedWeilComplex Λ g.hom

/-- The canonical ambient comparison localizes the termwise structure, without a choice.
Source: latest blueprint, K maps to (For K, theta_K)
(blueprint: sk-def-sf-weil-complexes). -/
def ambientComparison : DerivedCategory (WeilModule Λ g) ⥤
    CategoryTheory.Endofunctor.IsoAlgebra (action Λ g) :=
  { obj K := CategoryTheory.Endofunctor.IsoAlgebra.mk
      ((WeilConjectures.condensedWeilModuleForget Λ g.hom).mapDerivedCategory.obj K)
      ((WeilConjectures.condensedWeilDerivedStructure Λ g.hom).app K)
    map f := ObjectProperty.homMk
      { f := (WeilConjectures.condensedWeilModuleForget Λ g.hom).mapDerivedCategory.map f
        h := (WeilConjectures.condensedWeilDerivedStructure Λ g.hom).hom.naturality f } }

/-- For field coefficients the native underlying object belongs to the recorded Dctf.
Source: latest blueprint, field-coefficient comparison paragraph
(blueprint: sk-def-sf-weil-complexes).
Proof: exact forgetting commutes with homology and the standard truncations, so preserves
boundedness and the finite-constant-model constructibility condition. Over a field each
constructible cohomology object has Tor amplitude zero; boundedness supplies one common
finite interval. This is the field case of integral_ctf_equals_bc. -/
theorem native_mem (ell : ℕ) [Fact ell.Prime] [IsNoetherian T]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    (K : Native Λ g) :
    (constantModelBoundedConstructible Λ T ⊓ fun L ↦
      DerivedCategory.finiteTorAmplitude _ L)
      (((ambientComparison Λ g).obj K.obj).carrier) := by
  rw [field_ctf_eq_boundedConstructible Λ ell hΛ]
  exact WeilConjectures.condensedWeilForget_mem Λ g.hom K

/-- The specified termwise forgetful functor, restricted to the finite-Tor subcategory.
Source: latest blueprint, For in the displayed comparison
(blueprint: sk-def-sf-weil-complexes). -/
def nativeForget (ell : ℕ) [Fact ell.Prime] [IsNoetherian T]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell))) :
    Native Λ g ⥤ ConstantModelConstructibleFiniteTor Λ T :=
  ObjectProperty.lift _ ((WeilConjectures.condensedWeilComplexProperty Λ g.hom).ι ⋙
      (CategoryTheory.Endofunctor.IsoAlgebra.forget (upperStar Λ g.hom)).mapDerivedCategory)
    (fun K ↦ by simpa [ambientComparison] using native_mem Λ g ell hΛ K)

/-- The comparison sends K to (For K, theta_K), using the localized termwise isomorphism.
Source: latest blueprint, displayed native-to-strict comparison
(blueprint: sk-def-sf-weil-complexes). -/
def nativeComparison (ell : ℕ) [Fact ell.Prime] [IsNoetherian T]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell))) :
    Native Λ g ⥤ Complex Λ g :=
  { obj K := CategoryTheory.Endofunctor.IsoAlgebra.mk
      ((nativeForget Λ g ell hΛ).obj K)
      (ObjectProperty.isoMk _
        ((WeilConjectures.condensedWeilDerivedStructure Λ g.hom).app K.obj))
    map f := ObjectProperty.homMk
      { f := (nativeForget Λ g ell hΛ).map f
        h := ObjectProperty.hom_ext _
          ((WeilConjectures.condensedWeilDerivedStructure Λ g.hom).hom.naturality f.hom) } }

/-- Geometric Frobenius on the geometric point, written directly with Spec.
Source: latest blueprint, point example (blueprint: sk-def-sf-weil-complexes). -/
def pointFrobenius (D : WeilConjectures.FiniteFieldDatum.{u}) :
    Aut (Spec (.of D.k)) :=
  letI := Fintype.ofFinite D.k₀
  Scheme.Spec.mapIso
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k).toRingEquiv.toCommRingCatIso.op

/-- The ordinary coefficient unit with its coefficient-unit Weil structure.
Source: latest blueprint, phi_Lambda and the point example
(blueprint: sk-def-sf-weil-complexes). -/
def unitWeilModule {T : Scheme.{u}} (g : T ≅ T) : WeilModule Λ g :=
  CategoryTheory.Endofunctor.IsoAlgebra.mk (𝟙_ _)
    (Functor.Monoidal.εIso (upperStar Λ g.hom)).symm

/-- The unipotent matrix with rows (1, 1) and (0, 1) on a biproduct a ⊞ a, with its inverse.
Source: latest blueprint, displayed two-by-two matrix
(blueprint: sk-def-sf-weil-complexes). -/
noncomputable def unipotentBiproductIso {C : Type*} [Category C] [Preadditive C]
    [HasBinaryBiproducts C] (a : C) : a ⊞ a ≅ a ⊞ a where
  hom := 𝟙 _ + biprod.snd ≫ biprod.inl
  inv := 𝟙 _ - biprod.snd ≫ biprod.inl
  hom_inv_id := by simp
  inv_hom_id := by simp

/-- The Jordan block on K ⊞ K: the structure of K on each summand, then the unipotent matrix.
Source: latest blueprint, point example, Frobenius matrix with rows (1, 1) and (0, 1)
(blueprint: sk-def-sf-weil-complexes). -/
noncomputable def unipotentBlock {C : Type*} [Category C] [Preadditive C]
    [HasBinaryBiproducts C] {F : C ⥤ C} [F.Additive]
    (K : CategoryTheory.Endofunctor.IsoAlgebra F) :
    CategoryTheory.Endofunctor.IsoAlgebra F :=
  haveI : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  CategoryTheory.Endofunctor.IsoAlgebra.mk (K.carrier ⊞ K.carrier)
    (F.mapBiprod K.carrier K.carrier ≪≫
      biprod.mapIso K.str K.str ≪≫ unipotentBiproductIso K.carrier)

/-- First coordinate of the Jordan block structure: the sum of both pulled-back coordinates.
Source: latest blueprint, point example, first row of the matrix
(blueprint: sk-def-sf-weil-complexes).
Proof: expand the composite; F preserves the biproduct, the diagonal structure acts on
each summand, and the first row of the unipotent matrix is (1, 1). -/
lemma unipotentBlock_str_hom_fst {C : Type*} [Category C] [Preadditive C]
    [HasBinaryBiproducts C] {F : C ⥤ C} [F.Additive]
    (K : CategoryTheory.Endofunctor.IsoAlgebra F) :
    (unipotentBlock K).str.hom ≫ (biprod.fst : K.carrier ⊞ K.carrier ⟶ K.carrier) =
      F.map (biprod.fst : K.carrier ⊞ K.carrier ⟶ K.carrier) ≫ K.str.hom +
        F.map (biprod.snd : K.carrier ⊞ K.carrier ⟶ K.carrier) ≫ K.str.hom := by
  simp [unipotentBlock, unipotentBiproductIso,
    Preadditive.comp_add, Preadditive.add_comp, Category.assoc]

/-- Second coordinate of the Jordan block structure: the pulled-back second coordinate.
Source: latest blueprint, point example, second row of the matrix
(blueprint: sk-def-sf-weil-complexes).
Proof: expand the composite; the second row of the unipotent matrix is (0, 1), so only
the second summand contributes, through the structure of K. -/
lemma unipotentBlock_str_hom_snd {C : Type*} [Category C] [Preadditive C]
    [HasBinaryBiproducts C] {F : C ⥤ C} [F.Additive]
    (K : CategoryTheory.Endofunctor.IsoAlgebra F) :
    (unipotentBlock K).str.hom ≫ (biprod.snd : K.carrier ⊞ K.carrier ⟶ K.carrier) =
      F.map (biprod.snd : K.carrier ⊞ K.carrier ⟶ K.carrier) ≫ K.str.hom := by
  simp [unipotentBlock, unipotentBiproductIso,
    Preadditive.comp_add, Preadditive.add_comp, Category.assoc]

/-- The first biproduct inclusion as a morphism of pairs into the Jordan block.
Source: latest blueprint, point example, the sub-object of the extension
(blueprint: sk-def-sf-weil-complexes). -/
noncomputable def unipotentInl {C : Type*} [Category C] [Preadditive C]
    [HasBinaryBiproducts C] {F : C ⥤ C} [F.Additive]
    (K : CategoryTheory.Endofunctor.IsoAlgebra F) : K ⟶ unipotentBlock K :=
  ObjectProperty.homMk
    { f := (biprod.inl : K.carrier ⟶ K.carrier ⊞ K.carrier)
      h := by
        refine biprod.hom_ext _ _ ?_ ?_
        · rw [Category.assoc, ← CategoryTheory.Endofunctor.IsoAlgebra.str_hom,
            unipotentBlock_str_hom_fst, Preadditive.comp_add,
            ← F.map_comp_assoc, ← F.map_comp_assoc]
          simp
        · rw [Category.assoc, ← CategoryTheory.Endofunctor.IsoAlgebra.str_hom,
            unipotentBlock_str_hom_snd, ← F.map_comp_assoc]
          simp }

/-- The second biproduct projection as a morphism of pairs out of the Jordan block.
Source: latest blueprint, point example, the quotient of the extension
(blueprint: sk-def-sf-weil-complexes). -/
noncomputable def unipotentSnd {C : Type*} [Category C] [Preadditive C]
    [HasBinaryBiproducts C] {F : C ⥤ C} [F.Additive]
    (K : CategoryTheory.Endofunctor.IsoAlgebra F) : unipotentBlock K ⟶ K :=
  ObjectProperty.homMk
    { f := (biprod.snd : K.carrier ⊞ K.carrier ⟶ K.carrier)
      h := by
        rw [← CategoryTheory.Endofunctor.IsoAlgebra.str_hom,
          ← CategoryTheory.Endofunctor.IsoAlgebra.str_hom,
          unipotentBlock_str_hom_snd] }

/-- The inclusion followed by the projection of the Jordan block is zero.
Source: latest blueprint, point example, the extension is a complex
(blueprint: sk-def-sf-weil-complexes).
Proof: the underlying composite is biprod.inl followed by biprod.snd, which is zero;
morphisms of pairs are determined by their underlying morphisms. -/
@[reassoc (attr := simp)] theorem unipotentInlSnd {C : Type*} [Category C] [Preadditive C]
    [HasBinaryBiproducts C] {F : C ⥤ C} [F.Additive]
    (K : CategoryTheory.Endofunctor.IsoAlgebra F) : unipotentInl K ≫ unipotentSnd K = 0 := by
  apply (CategoryTheory.Endofunctor.IsoAlgebra.forget F).map_injective
  change (biprod.inl : K.carrier ⟶ K.carrier ⊞ K.carrier) ≫ biprod.snd = 0
  exact biprod.inl_snd

/-- The actual unipotent Jordan extension, with the first inclusion and second projection.
Source: latest blueprint, displayed two-by-two matrix
(blueprint: sk-def-sf-weil-complexes). -/
def jordanExtension {T : Scheme.{u}} (g : T ≅ T) : ShortComplex (WeilModule Λ g) :=
  ShortComplex.mk
    (unipotentInl (unitWeilModule Λ g))
    (unipotentSnd (unitWeilModule Λ g))
    (unipotentInlSnd (unitWeilModule Λ g))

/-- The Jordan extension is short exact before and after forgetting.
Source: latest blueprint, point extension (blueprint: sk-def-sf-weil-complexes).
Proof: forgetting identifies the two arrows with the first biproduct inclusion and
second projection. They give a split short exact sequence. Exact faithful forgetting
reflects short exactness. -/
theorem jordanExtension_shortExact {T : Scheme.{u}} (g : T ≅ T) :
    (jordanExtension Λ g).ShortExact := by
  let F := CategoryTheory.Endofunctor.IsoAlgebra.forget (upperStar Λ g.hom)
  apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful F
  exact (ShortComplex.Splitting.ofHasBinaryBiproduct (𝟙_ _) (𝟙_ _)).shortExact

/-- The ambient comparison is exactly the dependency's realization after its inclusion.
Source: latest blueprint, K maps to (For K, theta_K)
(blueprint: sk-def-sf-weil-complexes). -/
def ambientComparison_recordedIso :
    (WeilConjectures.condensedWeilComplexProperty Λ g.hom).ι ⋙ ambientComparison Λ g ≅
      WeilConjectures.condensedWeilRealization Λ g.hom ⋙ ObjectProperty.ι _ := Iso.refl _

/-- The new packaging and the dependency's realization agree as functors of strict pairs.
Source: latest blueprint, native-to-strict comparison in the Complement
(blueprint: sk-def-sf-weil-complexes). -/
def nativeComparison_recordedIso (ell : ℕ) [Fact ell.Prime] [IsNoetherian T]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell))) :
    nativeComparison Λ g ell hΛ ⋙ (recordedStrictEquivalence Λ g ell hΛ).functor ≅
      WeilConjectures.condensedWeilRealization Λ g.hom := Iso.refl _

/-- Finite type over the closure field makes the specified geometric fibre Noetherian.
This is inferred from the existing finite-type and quasi-compact assumptions.
Source: latest blueprint, finite-type setting of the cited Weil-sheaf definition
(blueprint: sk-def-sf-weil-complexes). -/
instance recordedModel_isNoetherian (D : FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] :
    IsNoetherian (D.geometricFiber Y₀).left where
  toIsLocallyNoetherian := by
    change IsLocallyNoetherian (pullback Y₀.hom _)
    infer_instance
  toCompactSpace := by
    change CompactSpace ↥(pullback Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) : Scheme.{u})
    infer_instance

/-- The coefficient choices of the dependency are the two field rings used above.
Source: latest blueprint, Lambda in {E,Qlb} (blueprint: sk-def-sf-weil-complexes).
Proof: for finite E use E itself and the identity ring-object isomorphism; for Qbar use
its identity ring-object isomorphism. These are precisely the two constructors. -/
theorem weilCoefficient_field (ell : ℕ) [Fact ell.Prime] (c : WeilCoefficient ell) :
    (∃ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty (Mon.mk (WeilCoefficient.ab c) ≅
        Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk (WeilCoefficient.ab c) ≅
        Mon.mk (Profinite.padicAlgClRingObj ell)) := by
  cases c with
  | finite E => exact Or.inl ⟨E, ⟨Iso.refl _⟩⟩
  | qbar => exact Or.inr ⟨Iso.refl _⟩

/-- On the geometric fibre this is the dependency's strict Weil category, over the
identical underlying complex and geometric-Frobenius structure map.
Source: latest blueprint, Complement, "they are the strict Weil complexes of
[def-weil-weil-sheaf-complex]" (blueprint: sk-def-sf-weil-complexes). -/
def weilStrictEquivalence (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ D.p) (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (c : WeilCoefficient ell) :
    Complex (WeilCoefficient.ab c) (D.geometricFrobenius Y₀) ≌
      strictWeilComplexCategory D ell hEll Y₀ c :=
  recordedStrictEquivalence (WeilCoefficient.ab c) (D.geometricFrobenius Y₀) ell
    (weilCoefficient_field ell c)

/-- The requested comparison is the dependency's recorded realization followed by the
inverse of the explicit equivalence. In particular it retains the same For and theta_K.
Source: latest blueprint, K maps to (For K, theta_K)
(blueprint: sk-def-sf-weil-complexes). -/
def weilComparison (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ D.p) (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (c : WeilCoefficient ell) :
    weilComplexCategory D ell hEll Y₀ c ⥤
      Complex (WeilCoefficient.ab c) (D.geometricFrobenius Y₀) :=
  weilComplexRealization D ell hEll Y₀ c ⋙ (weilStrictEquivalence D ell hEll Y₀ c).inverse

/-- Identifying strict categories recovers exactly the dependency's recorded functor.
Source: latest blueprint, comparison clause (blueprint: sk-def-sf-weil-complexes). -/
def weilComparison_recordedIso (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ D.p) (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (c : WeilCoefficient ell) :
    weilComparison D ell hEll Y₀ c ⋙ (weilStrictEquivalence D ell hEll Y₀ c).functor ≅
      weilComplexRealization D ell hEll Y₀ c := Iso.refl _

/-- The field-model comparison specializes the generic comparison, rather than
introducing another realization.
Source: latest blueprint, comparison clause (blueprint: sk-def-sf-weil-complexes). -/
def weilComparison_nativeIso (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ D.p) (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (c : WeilCoefficient ell) :
    weilComparison D ell hEll Y₀ c ≅
      nativeComparison (WeilCoefficient.ab c) (D.geometricFrobenius Y₀) ell
        (weilCoefficient_field ell c) := Iso.refl _

/-- The actual comparison is an equivalence on hearts, transported from the dependency.
Source: latest blueprint, Complement, equivalence on hearts
(blueprint: sk-def-sf-weil-complexes).
Proof: apply weilComplexRealization_heart_equivalence. The explicit strict equivalence
preserves carriers in both directions, hence preserves degree-zero concentration.
Its maps are the identity on underlying morphisms. Transport the dependency's
bijections on heart morphisms and its essential-surjectivity witnesses along its
inverse. The identity comparison weilComparison_recordedIso identifies the functors. -/
theorem weilComparison_heart_equivalence (D : FiniteFieldDatum.{u}) (ell : ℕ)
    [Fact ell.Prime] (hEll : ell ≠ D.p) (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (c : WeilCoefficient ell) :
    (∀ K L : weilComplexCategory D ell hEll Y₀ c,
      DerivedCategory.TStructure.t.IsLE K.obj 0 → DerivedCategory.TStructure.t.IsGE K.obj 0 →
      DerivedCategory.TStructure.t.IsLE L.obj 0 → DerivedCategory.TStructure.t.IsGE L.obj 0 →
        Function.Bijective (fun f : K ⟶ L ↦ (weilComparison D ell hEll Y₀ c).map f)) ∧
    (∀ P : Complex (WeilCoefficient.ab c) (D.geometricFrobenius Y₀),
      DerivedCategory.TStructure.t.IsLE P.carrier.obj 0 →
      DerivedCategory.TStructure.t.IsGE P.carrier.obj 0 →
        ∃ K : weilComplexCategory D ell hEll Y₀ c,
          DerivedCategory.TStructure.t.IsLE K.obj 0 ∧ DerivedCategory.TStructure.t.IsGE K.obj 0 ∧
            Nonempty ((weilComparison D ell hEll Y₀ c).obj K ≅ P)) := by
  obtain ⟨hfull, hess⟩ := weilComplexRealization_heart_equivalence D ell hEll Y₀ c
  let e := weilStrictEquivalence D ell hEll Y₀ c
  constructor
  · intro K L hK₁ hK₂ hL₁ hL₂
    exact (e.fullyFaithfulInverse.map_bijective _ _).comp
      (hfull K L hK₁ hK₂ hL₁ hL₂)
  · intro P hP₁ hP₂
    obtain ⟨K, hK₁, hK₂, ⟨i⟩⟩ := hess (e.functor.obj P) hP₁ hP₂
    exact ⟨K, hK₁, hK₂, ⟨e.inverse.mapIso i ≪≫ (e.unitIso.app P).symm⟩⟩

/-- The nonfaithfulness is that of the dependency's recorded realization at the point.
Source: latest blueprint, Complement, Jordan-block nonfaithfulness
(blueprint: sk-def-sf-weil-complexes).
Proof: use the two distinct morphisms supplied by weilComplexRealization_not_faithful.
Their images remain equal after the inverse strict equivalence. Thus their images
under weilComparison coincide, contradicting injectivity if that functor were faithful.
This uses the same Jordan class as the dependency, not a second independent example. -/
theorem weilComparison_not_faithful (D : FiniteFieldDatum.{u}) (ell : ℕ)
    [Fact ell.Prime] (hEll : ell ≠ D.p) (c : WeilCoefficient ell) :
    ¬ (weilComparison D ell hEll (Over.mk (𝟙 (Spec (.of D.k₀)))) c).Faithful := by
  intro h
  let := h
  obtain ⟨K, L, f₁, f₂, hne, heq⟩ :=
    weilComplexRealization_not_faithful D ell hEll c
  apply hne
  apply (weilComparison D ell hEll (Over.mk (𝟙 (Spec (.of D.k₀)))) c).map_injective
  exact congrArg
    ((weilStrictEquivalence D ell hEll (Over.mk (𝟙 (Spec (.of D.k₀)))) c).inverse.map) heq

end Native

/-- The ambient dual is the recorded relative derived internal Hom into the coefficient unit.
Source: latest blueprint, contragredient paragraph (blueprint: sk-def-sf-weil-complexes). -/
abbrev dual {T : Scheme.{u}} (K : DerivedCategory
    (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))) :=
  (ihom K).obj (𝟙_ _)

/-- The three typed arrows of the contragredient datum, with inverse in the first Hom slot.
The first arrow is the evaluation-transpose comparison for the monoidal equivalence.
Source: latest blueprint, displayed contragredient composite
(blueprint: sk-def-sf-weil-complexes). -/
def dualDatum {T : Scheme.{u}} (g : T ≅ T)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)))
    (phi : (action Λ g).obj K ≅ K) : (action Λ g).obj (dual Λ K) ≅ dual Λ K :=
  Functor.Monoidal.ihomObjIso (action Λ g) K (𝟙_ _) ≪≫
    (ihom ((action Λ g).obj K)).mapIso (Functor.Monoidal.εIso (action Λ g)).symm ≪≫
      (MonoidalClosed.internalHom.mapIso phi.symm.op).app (𝟙_ _)

/-- Restrict a dual datum only with its stated domain condition.
Source: latest blueprint, dual-domain qualification (blueprint: sk-def-sf-weil-complexes). -/
def dualComplex {T : Scheme.{u}} (g : T ≅ T) (K : Complex Λ g)
    (hK : (constantModelBoundedConstructible Λ T ⊓ fun L ↦
      DerivedCategory.finiteTorAmplitude _ L) (dual Λ K.carrier.obj)) : Complex Λ g :=
  CategoryTheory.Endofunctor.IsoAlgebra.mk ⟨dual Λ K.carrier.obj, hK⟩
    (ObjectProperty.isoMk _ (dualDatum Λ g K.carrier.obj
      ((ObjectProperty.ι _).mapIso K.str)))

/-- The tensorator is included in the tensor of two ambient Weil data.
Source: latest blueprint, twisted-dual composite (blueprint: sk-def-sf-weil-complexes). -/
def tensorDatum {T : Scheme.{u}} (g : T ≅ T)
    {K L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))}
    (phi : (action Λ g).obj K ≅ K) (psi : (action Λ g).obj L ≅ L) :
    (action Λ g).obj (K ⊗ L) ≅ K ⊗ L :=
  (Functor.Monoidal.μIso (action Λ g) K L).symm ≪≫ tensorIso phi psi

/-- Signed ordinary Tate sheaves, built from the recorded coefficient line and its dual.
The coefficient presentation c runs through all admissible stages, including finite
rings (the zero ring as well), integral coefficients and the algebraic closure.
Source: latest blueprint, actual signed Tate sheaves
(blueprint: sk-def-sf-weil-complexes). -/
def presentationLine (T : Scheme.{u}) : ℤ →
    Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj (c.obj ell) T)
  | .ofNat n => c.line ell T n
  | .negSucc n => (ihom (c.line ell T (n + 1))).obj (𝟙_ _)

/-- The actual signed Tate sheaf from the recorded `sk-def-sp-tate-twist` node.
The coefficient line is the specified `c.firstLine`; no replacement line is introduced.
Source: latest blueprint, actual signed Tate sheaves
(blueprint: sk-def-sf-weil-complexes). -/
def tateLine (T : Scheme.{u}) (r : ℤ) :
    Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj (c.obj ell) T) :=
  spInternalSignedTwist T (condensedRingObj (c.obj ell) T) (c.firstLine ell T) r

/-- The positive tensor recursion agrees with the recorded internal signed convention.
Source: latest blueprint, tensor powers (blueprint: sk-def-sf-weil-complexes). -/
theorem presentationPower_eq (T : Scheme.{u}) (n : ℕ) :
    c.line ell T n = coefficientTwistNat T (condensedRingObj (c.obj ell) T)
      (c.firstLine ell T) n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun M ↦ M ⊗ c.firstLine ell T) ih

/-- The presentation is the internal positive-power and negative-dual convention.
Source: latest blueprint, signed powers (blueprint: sk-def-sf-weil-complexes). -/
def presentationSignedIso (T : Scheme.{u}) (r : ℤ) :
    presentationLine ell c T r ≅ coefficientSignedTwist T
      (condensedRingObj (c.obj ell) T) (c.firstLine ell T) r :=
  eqToIso (by
    cases r with
    | ofNat n => exact presentationPower_eq ell c T n
    | negSucc n =>
      exact congrArg (fun M ↦ (ihom M).obj (𝟙_ _)) (presentationPower_eq ell c T (n + 1)))

/-- The canonical identification with the actual recorded signed Tate sheaf.
The existing `podSignedComparison` is uniquely specified on unit sections, tensor
sections and evaluation, and `Mod.comapId` removes its identity scalar restriction.
Root inverse image enters through `presentationPull` and its normalized coordinates.
Source: latest blueprint, signed Tate sheaves (blueprint: sk-def-sf-weil-complexes). -/
def tateLine_identification (T : Scheme.{u}) (r : ℤ) :
    tateLine ell c T r ≅ presentationLine ell c T r :=
  (presentationSignedIso ell c T r ≪≫
    podSignedComparison T _ _ (Iso.refl _) (c.firstLine ell T) (c.firstLine ell T)
      ((Mod.comapId _).symm.app _) r ≪≫ (Mod.comapId _).app _).symm

/-- Signed powers agree with the recorded sectionwise encoding of the same line.
Source: latest blueprint, actual signed Tate sheaves
(blueprint: sk-def-sf-weil-complexes).
Proof: the section-module equivalence is monoidal closed. Its unit and tensorators
identify zero and positive powers by induction. The evaluation-transpose comparison
identifies the internal dual for negative powers. -/
theorem signedLine_published (T : Scheme.{u}) (r : ℤ) :
    Nonempty
      (((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
        (Scheme.ProEt.topology T) (condensedRingObj (c.obj ell) T)).functor.obj
          (presentationLine ell c T r)) ≅
        spSignedTwist T (condensedRingObj (c.obj ell) T) (c.firstLine ell T) r) := by
  let E := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology T) (condensedRingObj (c.obj ell) T)
  exact ⟨E.functor.mapIso (tateLine_identification ell c T r).symm ≪≫
    E.counitIso.app _⟩

/-- Multiplication by q is invertible on the coefficient unit in every admissible stage.
Source: latest blueprint, q inverse in Z_ell units (blueprint: sk-def-sf-weil-complexes).
Proof: ell differs from p and q is a power of p, so q is an ell-adic unit.
Its inverse passes through each specified integral coefficient map, including a finite
quotient and the zero ring, and gives a two-sided inverse to scalar multiplication. -/
theorem cardinal_scalar_isIso (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) (T : Scheme.{u}) :
    IsIso (D.q • 𝟙 (𝟙_ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (c.obj ell) T)))) := by
  have hcop : ell.Coprime D.q := by
    rw [D.cardinality_eq]
    exact ((Fact.out : ell.Prime).coprime_iff_not_dvd.mpr
      (fun h ↦ hEll ((Nat.prime_dvd_prime_iff_eq (Fact.out : ell.Prime) D.prime).mp h))).pow_right _
  have hq : IsUnit (D.q : ℤ_[ell]) :=
    PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr hcop)
  have hpoint : IsIso (D.q • 𝟙 (Profinite.continuousMapRingObj.{u} ℤ_[ell])) := by
    have hm : IsIso ((sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
        (D.q • 𝟙 (Profinite.continuousMapRingObj.{u} ℤ_[ell]))) := by
      change IsIso (D.q • 𝟙 (Profinite.continuousMapRingObj.{u} ℤ_[ell]).obj)
      rw [NatTrans.isIso_iff_isIso_app]
      intro S
      apply (ConcreteCategory.isIso_iff_bijective _).mpr
      change Function.Bijective (fun x : ULift.{u + 1} C(S.unop, ℤ_[ell]) ↦ D.q • x)
      simp only [nsmul_eq_mul]
      have hu : IsUnit (D.q : ULift.{u + 1} C(S.unop, ℤ_[ell])) := by
        simpa only [map_natCast] using
          ((hq.map (ContinuousMap.C : ℤ_[ell] →+* C(S.unop, ℤ_[ell]))).map
            ULift.ringEquiv.symm.toRingHom)
      exact IsUnit.isUnit_iff_mulLeft_bijective.mp hu
    exact isIso_of_reflects_iso _
      (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  let R := condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[ell]) T
  have : (upperStarFromPoint T).IsLeftAdjoint :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ T))).isLeftAdjoint
  have : (upperStarFromPoint T).Additive :=
    rightExactFunctor_le_additiveFunctor _ _ _ (by
      rw [rightExactFunctor_iff]
      infer_instance)
  have hR : IsIso (D.q • 𝟙 R) := by
    have hm : IsIso ((upperStarFromPoint T).map
        (D.q • 𝟙 (Profinite.continuousMapRingObj.{u} ℤ_[ell]))) := inferInstance
    rw [Functor.map_nsmul, (upperStarFromPoint T).map_id] at hm
    exact hm
  have : IsIso (D.q • 𝟙 (Mod.regular R)) := by
    have hm : IsIso ((Mod.forget R).map (D.q • 𝟙 (Mod.regular R))) := by
      change IsIso (D.q • 𝟙 R)
      exact hR
    exact isIso_of_reflects_iso _ (Mod.forget R)
  let F := Mod.extendScalars (coefficientMap (c.integralMap ell) T)
  have hF : IsIso (D.q • 𝟙 (F.obj (Mod.regular R))) := by
    have hm : IsIso (F.map (D.q • 𝟙 (Mod.regular R))) := inferInstance
    rw [Functor.map_nsmul, F.map_id] at hm
    exact hm
  let e : F.obj (Mod.regular R) ≅
      𝟙_ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (c.obj ell) T)) :=
    Mod.extendScalarsObjRegularIso (coefficientMap (c.integralMap ell) T)
  have he : IsIso (e.inv ≫ (D.q • 𝟙 (F.obj (Mod.regular R))) ≫ e.hom) := inferInstance
  simpa only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.comp_id,
    Category.id_comp, Iso.inv_hom_id] using he

/-- The scalar q^(-r) on the coefficient unit, using the actual inverse of multiplication q.
Source: latest blueprint, signed normalization (blueprint: sk-def-sf-weil-complexes). -/
def cardinalScalar (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) (T : Scheme.{u}) (r : ℤ) :
    Aut (𝟙_ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (c.obj ell) T))) :=
  letI := cardinal_scalar_isIso ell c D hEll T
  let a : Aut (𝟙_ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (c.obj ell) T))) := asIso (D.q • 𝟙 _)
  a ^ (-r)

/-- In any root-line frame over the geometric point the specified datum has scalar q^(-r).
The unit power has scalar 1 and the negative power has the inverse scalar.
Source: latest blueprint, Tate normalization paragraph
(blueprint: sk-def-sf-weil-complexes).
Proof: geometric field Frobenius is the inverse q-power automorphism; hence on each
ell-power root it is the inverse q-power map. The projection normalization of
integralTatePull passes these equalities to the inverse limit. Scalar extension retains
them. Tensor powers multiply scalars, while the inverse in the contravariant Hom slot
inverts them on the dual. Zero uses exactly the coefficient-unit isomorphism. Every
change of root frame is coefficient-linear with Frobenius-fixed coefficient, so the
same scalar equation holds in any frame. -/
theorem tatePull_scalar (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p)
    [∀ x : Spec (.of D.k), Invertible (ell : (Spec (.of D.k)).residueField x)]
    (r : ℤ) (e : tateLine ell c (Spec (.of D.k)) r ≅ 𝟙_ _) :
    tatePull ell c (pointFrobenius D) r =
      (upperStar (c.obj ell) (pointFrobenius D).hom).mapIso e ≪≫
        (Functor.Monoidal.εIso (upperStar (c.obj ell) (pointFrobenius D).hom)).symm ≪≫
        cardinalScalar ell c D hEll (Spec (.of D.k)) r ≪≫ e.symm := by
  sorry

/-- The actual Tate sheaf placed in degree zero.
Source: latest blueprint, Tate sheaves in degree zero (blueprint: sk-def-sf-weil-complexes). -/
def derivedTateLine (T : Scheme.{u}) (r : ℤ) : c.derived ell T :=
  (DerivedCategory.singleFunctor _ 0).obj (tateLine ell c T r)

/-- The termwise root-normalized Tate structure in the ambient derived category.
At r=0 it is the canonical coefficient-unit isomorphism.
Source: latest blueprint, tau_r and varphi_Lambda (blueprint: sk-def-sf-weil-complexes). -/
def tateDatum {T : Scheme.{u}} (g : T ≅ T)
    [∀ x : T, Invertible (ell : T.residueField x)] (r : ℤ) :
    (action (c.obj ell) g).obj (derivedTateLine ell c T r) ≅ derivedTateLine ell c T r :=
  ((upperStar (c.obj ell) g.hom).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (tatePull ell c g r)

/-- The signed Tate line in degree zero belongs to the actual Dctf.
Source: latest blueprint, Tate sheaves with their canonical Weil structures
(blueprint: sk-def-sf-weil-complexes).
Proof: a compatible primitive-root cover trivializes the first integral line and
all its finite, integral, rational and Qbar scalar extensions. The same cover
trivializes the unit, tensor powers and duals. The signed line is thus locally free
of rank one, constructible and flat; its degree-zero complex has Tor interval [0,0]. -/
theorem tate_mem (T : Scheme.{u})
    [∀ x : T, Invertible (ell : T.residueField x)] (r : ℤ) :
    (constantModelBoundedConstructible (c.obj ell) T ⊓ fun L ↦
      DerivedCategory.finiteTorAmplitude _ L) (derivedTateLine ell c T r) := by
  sorry

/-- The actual signed Tate sheaf with its root-normalized strict Weil structure.
Source: latest blueprint, tau_r on the Tate sheaf
(blueprint: sk-def-sf-weil-complexes). -/
def tateComplex {T : Scheme.{u}} (g : T ≅ T)
    [∀ x : T, Invertible (ell : T.residueField x)] (r : ℤ) : Complex (c.obj ell) g :=
  CategoryTheory.Endofunctor.IsoAlgebra.mk
    ⟨derivedTateLine ell c T r, tate_mem ell c T r⟩
    (ObjectProperty.isoMk _ (tateDatum ell c g r))

/-- The typed twisted-dual datum contains the inverse tensorator before the two structures.
Source: latest blueprint, final displayed composite (blueprint: sk-def-sf-weil-complexes). -/
def twistedDualDatum {T : Scheme.{u}} (g : T ≅ T)
    [∀ x : T, Invertible (ell : T.residueField x)] (K : c.derived ell T)
    (phi : (action (c.obj ell) g).obj K ≅ K) (r : ℤ) :
    (action (c.obj ell) g).obj (dual (c.obj ell) K ⊗ derivedTateLine ell c T r) ≅
      dual (c.obj ell) K ⊗ derivedTateLine ell c T r :=
  tensorDatum (c.obj ell) g (dualDatum (c.obj ell) g K phi) (tateDatum ell c g r)

end AlgebraicGeometry.ProEtale.CondensedRing.StrictWeilCondensed

namespace AlgebraicGeometry.ProEtale.CondensedRing.StrictWeilCondensed

open PurityTransport

variable (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)

end AlgebraicGeometry.ProEtale.CondensedRing.StrictWeilCondensed
