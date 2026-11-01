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
  sorry

/-- Frobenius pullback as an endofunctor of the actual Dctf full subcategory.
Source: latest blueprint, P_T paragraph (blueprint: sk-def-sf-weil-complexes). -/
def smallAction {T : Scheme.{u}} (g : T ≅ T) :
    ConstantModelConstructibleFiniteTor Λ T ⥤ ConstantModelConstructibleFiniteTor Λ T :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ action Λ g) (action_mem Λ g)

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

end Native

/-- The ambient dual is the recorded relative derived internal Hom into the coefficient unit.
Source: latest blueprint, contragredient paragraph (blueprint: sk-def-sf-weil-complexes). -/
abbrev dual {T : Scheme.{u}} (K : DerivedCategory
    (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))) :=
  (ihom K).obj (𝟙_ _)

/-- The actual signed Tate sheaf from the recorded `sk-def-sp-tate-twist` node.
The coefficient line is the specified `c.firstLine`; no replacement line is introduced.
Source: latest blueprint, actual signed Tate sheaves
(blueprint: sk-def-sf-weil-complexes). -/
def tateLine (T : Scheme.{u}) (r : ℤ) :
    Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj (c.obj ell) T) :=
  spInternalSignedTwist T (condensedRingObj (c.obj ell) T) (c.firstLine ell T) r

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

end AlgebraicGeometry.ProEtale.CondensedRing.StrictWeilCondensed

namespace AlgebraicGeometry.ProEtale.CondensedRing.StrictWeilCondensed

open PurityTransport

variable (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)

end AlgebraicGeometry.ProEtale.CondensedRing.StrictWeilCondensed
