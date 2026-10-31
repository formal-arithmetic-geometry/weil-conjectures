/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdmissibleCondensedCoefficients
public import WeilConjectures.AlgebraicGeometry.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.DerivedFixedPairRealization
public import WeilConjectures.WeilSheaf.StrictWeilComplexNotFaithful
public import WeilConjectures.AlgebraicGeometry.ProEtaleTateTwistsOfUniverses
public import WeilConjectures.SecSmoothPurity.TransportLinePull
public import WeilConjectures.SecSmoothPurity.TransportFiniteLines
public import WeilConjectures.AlgebraicGeometry.PointProEtaleSectionsExactOfUniverses
public import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
public import WeilConjectures.AlgebraicGeometry.CondensedWeilModules
public import WeilConjectures.AlgebraicGeometry.CoefficientHeart
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-! # Strict Weil complexes with actual condensed coefficients

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
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

namespace AlgebraicGeometry.ProEtale.CondensedRing.StrictWeil

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

/-- The canonical derived monoidal structure, transported through the exact comparison.
Source: latest blueprint, monoidal descent paragraph
(blueprint: sk-def-sf-weil-complexes). -/
instance actionMonoidal {T : Scheme.{u}} (g : T ≅ T) : (action Λ g).Monoidal :=
  Functor.Monoidal.transport (leftDerivedUpperStarIsoMapDerivedCategory Λ g.hom)

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

/-- The inverse of the exact derived action is pullback by the inverse automorphism.
Source: latest blueprint, inverse and monoidal equivalence clauses
(blueprint: sk-def-sf-weil-complexes).
Proof: inverse image composition and identity comparisons give both functor isomorphisms
on modules. Exact-functor localization descends them to the ordinary derived categories. -/
theorem action_inverse {T : Scheme.{u}} (g : T ≅ T) :
    Nonempty (action Λ g ⋙ action Λ g.symm ≅ 𝟭 _) ∧
    Nonempty (action Λ g.symm ⋙ action Λ g ≅ 𝟭 _) := by
  sorry

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
  sorry

/-- A Weil structure is an isomorphism P_T K to K in Dctf.
Source: latest blueprint, displayed phi_K (blueprint: sk-def-sf-weil-complexes). -/
abbrev Structure {T : Scheme.{u}} (g : T ≅ T)
    (K : ConstantModelConstructibleFiniteTor Λ T) :=
  (smallAction Λ g).obj K ≅ K

/-- Strict pairs, with exactly the recorded commuting morphisms, identities and composition.
No smooth map is data of a pair. The admissible coefficient stages are all specializations
of this construction for a commutative condensed ring.
Source: latest blueprint, strict-pair paragraphs (blueprint: sk-def-sf-weil-complexes). -/
abbrev Complex {T : Scheme.{u}} (g : T ≅ T) :=
  CategoryTheory.Endofunctor.IsoAlgebra (smallAction Λ g)

/-- The strict Weil category on any model over the stated global finite field.
The admissibility witness is the recorded coefficient notion, not a new coefficient type.
Smoothness of a morphism between models adds no datum to this category.
Source: latest blueprint, definition and first context paragraph
(blueprint: sk-def-sf-weil-complexes). -/
abbrev modelComplex (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hEll : ell ≠ D.p)
    (_hΛ : IsAdmissibleCoefficient Λ) (T₀ : Over (Spec (.of D.k₀))) :=
  Complex Λ (modelFrobenius D T₀)

/-- The faithful forgetful functor of strict pairs.
Source: latest blueprint, pair category paragraph (blueprint: sk-def-sf-weil-complexes). -/
abbrev forget {T : Scheme.{u}} (g : T ≅ T) :=
  CategoryTheory.Endofunctor.IsoAlgebra.forget (smallAction Λ g)

/-- Native Weil modules are the abelian fixed pairs before deriving.
Source: latest blueprint, native category paragraph (blueprint: sk-def-sf-weil-complexes). -/
abbrev WeilModule {T : Scheme.{u}} (g : T ≅ T) :=
  WeilConjectures.condensedWeilModules Λ g.hom

section Native

open CategoryTheory.Endofunctor.IsoAlgebra

variable {T : Scheme.{u}} (g : T ≅ T) [HasDerivedCategory.{w} (WeilModule Λ g)]

/-- Bounded native derived Weil modules with constructible underlying cohomology.
Source: latest blueprint, native category paragraph (blueprint: sk-def-sf-weil-complexes). -/
abbrev Native :=
  (fixedPairRealizationSource (upperStar Λ g.hom)
    (IsConstantModelConstructible Λ T)).FullSubcategory

/-- The canonical ambient comparison localizes the termwise structure, without a choice.
Source: latest blueprint, K maps to (For K, theta_K)
(blueprint: sk-def-sf-weil-complexes). -/
def ambientComparison : DerivedCategory (WeilModule Λ g) ⥤
    CategoryTheory.Endofunctor.IsoAlgebra (action Λ g) :=
  lift (CategoryTheory.Endofunctor.IsoAlgebra.forget (upperStar Λ g.hom)).mapDerivedCategory
    (cyclicDerivedStructure (upperStar Λ g.hom))

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
  ObjectProperty.lift _ ((fixedPairRealizationSource (upperStar Λ g.hom)
    (IsConstantModelConstructible Λ T)).ι ⋙
      (CategoryTheory.Endofunctor.IsoAlgebra.forget (upperStar Λ g.hom)).mapDerivedCategory)
    (native_mem Λ g ell hΛ)

/-- The comparison sends K to (For K, theta_K), using the localized termwise isomorphism.
Source: latest blueprint, displayed native-to-strict comparison
(blueprint: sk-def-sf-weil-complexes). -/
def nativeComparison (ell : ℕ) [Fact ell.Prime] [IsNoetherian T]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell))) :
    Native Λ g ⥤ Complex Λ g :=
  lift (nativeForget Λ g ell hΛ)
    (NatIso.ofComponents
      (fun K ↦ ObjectProperty.isoMk _
        ((cyclicDerivedStructure (upperStar Λ g.hom)).app K.obj))
      (fun f ↦ ObjectProperty.hom_ext _
        ((cyclicDerivedStructure (upperStar Λ g.hom)).hom.naturality f.hom)))

/-- The native heart is concentrated in degree zero in the ordinary derived category.
Source: latest blueprint, degree-zero hearts (blueprint: sk-def-sf-weil-complexes). -/
def nativeHeart : ObjectProperty (Native Λ g) :=
  DerivedCategory.TStructure.t.heart.inverseImage
    (fixedPairRealizationSource (upperStar Λ g.hom)
      (IsConstantModelConstructible Λ T)).ι

/-- The strict heart is the full subcategory whose underlying derived object is in degree zero.
Source: latest blueprint, degree-zero hearts (blueprint: sk-def-sf-weil-complexes). -/
def strictHeart : ObjectProperty (Complex Λ g) :=
  DerivedCategory.TStructure.t.heart.inverseImage (forget Λ g ⋙ ObjectProperty.ι _)

/-- The canonical comparison is an equivalence on the degree-zero hearts.
Source: latest blueprint, comparison and its equivalence on hearts
(blueprint: sk-def-sf-weil-complexes).
Proof: use coefficientHeart for kernels, cokernels and extensions of the constructible
heart, and derivedFixedPairRealization. The degree-zero embeddings are fully faithful;
therefore a strict structure and its inverse lift uniquely to the constructible sheaf.
Exact forgetting identifies the resulting native structure with the displayed comparison.
This argument is invariant under the stated coefficient-ring isomorphisms. -/
theorem nativeComparison_hearts (ell : ℕ) [Fact ell.Prime] [IsNoetherian T]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell))) :
    ∃ hR : ∀ K : (nativeHeart Λ g).FullSubcategory,
      strictHeart Λ g ((nativeComparison Λ g ell hΛ).obj K.obj),
      ((strictHeart Λ g).lift
        ((nativeHeart Λ g).ι ⋙ nativeComparison Λ g ell hΛ) hR).IsEquivalence := by
  sorry

end Native

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

/-- The actual unipotent Jordan extension, with the first inclusion and second projection.
Source: latest blueprint, displayed two-by-two matrix
(blueprint: sk-def-sf-weil-complexes). -/
def jordanExtension {T : Scheme.{u}} (g : T ≅ T) : ShortComplex (WeilModule Λ g) :=
  ShortComplex.mk
    (CategoryTheory.Endofunctor.IsoAlgebra.jordanBlockInl (unitWeilModule Λ g))
    (CategoryTheory.Endofunctor.IsoAlgebra.jordanBlockSnd (unitWeilModule Λ g))
    (CategoryTheory.Endofunctor.IsoAlgebra.jordanBlockInl_jordanBlockSnd (unitWeilModule Λ g))

/-- The Jordan extension is short exact before and after forgetting.
Source: latest blueprint, point extension (blueprint: sk-def-sf-weil-complexes).
Proof: forgetting identifies the two arrows with the first biproduct inclusion and
second projection. They give a split short exact sequence. Exact faithful forgetting
reflects short exactness. -/
theorem jordanExtension_shortExact {T : Scheme.{u}} (g : T ≅ T) :
    (jordanExtension Λ g).ShortExact := by
  sorry

/-- On the geometric point the Jordan block is nonsplit, its class survives natively and
vanishes after comparison, and every underlying unit-to-unit[1] map is zero.
This is the stated example of nonfaithfulness, with no assertion for an empty scheme.
Source: latest blueprint, scope paragraph (blueprint: sk-def-sf-weil-complexes).
Proof: point sections of the coefficient unit have trivial Frobenius. A hypothetical
section of the Jordan projection has second coordinate 1, whereas Frobenius invariance
forces that coordinate to be zero. The coefficient field is nonzero, a contradiction.
Underlying forgetting has the biproduct splitting. The short exact connecting morphism
is nonzero precisely because the sequence is nonsplit, and becomes zero after exact
forgetting. All three terms are constructible; their singles and the shifted endpoint
belong to Native. Thus derivedFixedPairRealization gives nonfaithfulness of its canonical
comparison. Finally point sections are exact by point_proEtale_sections_exact_of_universes;
the coefficient unit represents sections, so its positive Ext groups vanish. -/
theorem point_jordan_nonfaithful (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    [HasDerivedCategory.{w} (WeilModule Λ (pointFrobenius D))] :
    ¬ Nonempty (jordanExtension Λ (pointFrobenius D)).Splitting ∧
    Nonempty ((jordanExtension Λ (pointFrobenius D)).map
      (CategoryTheory.Endofunctor.IsoAlgebra.forget
        (upperStar Λ (pointFrobenius D).hom))).Splitting ∧
    (jordanExtension_shortExact Λ (pointFrobenius D)).singleδ ≠ 0 ∧
    (CategoryTheory.Endofunctor.IsoAlgebra.forget
      (upperStar Λ (pointFrobenius D).hom)).mapDerivedCategory.map
        (jordanExtension_shortExact Λ (pointFrobenius D)).singleδ = 0 ∧
    ¬ (nativeComparison Λ (pointFrobenius D) ell hΛ).Faithful ∧
    ∀ h : (𝟙_ (DerivedCategory (Mod
      (Sheaf (Scheme.ProEt.topology (Spec (.of D.k))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of D.k)))))) ⟶
        (𝟙_ (DerivedCategory (Mod
          (Sheaf (Scheme.ProEt.topology (Spec (.of D.k))) Ab.{u + 1})
          (condensedRingObj Λ (Spec (.of D.k)))))) ⟦(1 : ℤ)⟧, h = 0 := by
  sorry

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

end AlgebraicGeometry.ProEtale.CondensedRing.StrictWeil

namespace AlgebraicGeometry.ProEtale.CondensedRing.StrictWeil

open PurityTransport

variable (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)

/-- The existing normalized root coordinates. Their integral component is uniquely
fixed by every root projection; scalar and power components are fixed by the record's
normalization equations. No root frame or arbitrary unnormalized map is selected.
Source: latest blueprint, roots, limits and scalar extensions
(blueprint: sk-def-sf-weil-complexes). -/
def tateCoordinates {T : Scheme.{u}} (g : T ≅ T)
    [∀ x : T, Invertible (ell : T.residueField x)] : LinePullCoordinates ell c g.hom :=
  Classical.choice (linePullCoordinates_nonempty ell c g.hom)

/-- The unique projection-normalized pullback of the integral root line.
Source: latest blueprint, roots and inverse-limit Tate normalization
(blueprint: sk-def-sf-weil-complexes). -/
def integralTatePull {T : Scheme.{u}} (g : T ≅ T)
    [∀ x : T, Invertible (ell : T.residueField x)] :=
  (tateCoordinates ell .integers g).integral

/-- The chosen integral map retains every root-level projection normalization.
Source: latest blueprint, inverse-limit normalization
(blueprint: sk-def-sf-weil-complexes).
Proof: take the property of the unique integralComparison; its finite-level components
are characterized by rootTensorPull, which uses the recorded inverse image of roots. -/
theorem integralTatePull_normalized {T : Scheme.{u}} (g : T ≅ T)
    [∀ x : T, Invertible (ell : T.residueField x)] :
    ∀ n : ℕ, ∃ en :
      (upperStar (Profinite.continuousMapRingObj ℤ_[ell]) g.hom).obj
        (tateModuleLevel T ell n) ≅ tateModuleLevel T ell n,
      PullNormalized (Profinite.continuousMapRingObj ℤ_[ell]) g.hom en
        (rootTensorPull ell g.hom n) ∧
      (integralTatePull ell g).hom ≫ limit.π (tateModuleSystem T ell) (Opposite.op n) =
        (upperStar (Profinite.continuousMapRingObj ℤ_[ell]) g.hom).map
          (limit.π (tateModuleSystem T ell) (Opposite.op n)) ≫ en.hom := by
  sorry

/-- Positive Tate powers use the specified scalar extension and tensorator maps.
The coordinates record includes their equality to those canonical constructions.
Source: latest blueprint, tensor and scalar-extension Tate constructions
(blueprint: sk-def-sf-weil-complexes). -/
def positiveTatePull {T : Scheme.{u}} (g : T ≅ T)
    [∀ x : T, Invertible (ell : T.residueField x)] (n : ℕ) :=
  (tateCoordinates ell c g).power n

/-- Signed ordinary Tate sheaves, built from the recorded coefficient line and its dual.
The coefficient presentation c runs through all admissible stages, including finite
rings (the zero ring as well), integral coefficients and the algebraic closure.
Source: latest blueprint, actual signed Tate sheaves
(blueprint: sk-def-sf-weil-complexes). -/
def tateLine (T : Scheme.{u}) : ℤ →
    Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj (c.obj ell) T)
  | .ofNat n => c.line ell T n
  | .negSucc n => (ihom (c.line ell T (n + 1))).obj (𝟙_ _)

/-- Root-normalized Frobenius on signed ordinary Tate sheaves. The negative case is
contragredient, using the canonical closed comparison, the unit and the inverse
positive Tate isomorphism in the contravariant slot.
Source: latest blueprint, tau_r (blueprint: sk-def-sf-weil-complexes). -/
def tatePull {T : Scheme.{u}} (g : T ≅ T)
    [∀ x : T, Invertible (ell : T.residueField x)] :
    (r : ℤ) → (upperStar (c.obj ell) g.hom).obj (tateLine ell c T r) ≅
      tateLine ell c T r
  | .ofNat n => positiveTatePull ell c g n
  | .negSucc n =>
      Functor.Monoidal.ihomObjIso (upperStar (c.obj ell) g.hom)
          (c.line ell T (n + 1)) (𝟙_ _) ≪≫
        (ihom ((upperStar (c.obj ell) g.hom).obj (c.line ell T (n + 1)))).mapIso
          (Functor.Monoidal.εIso (upperStar (c.obj ell) g.hom)).symm ≪≫
        (MonoidalClosed.internalHom.mapIso (positiveTatePull ell c g (n + 1)).symm.op).app
          (𝟙_ _)

/-- The finite root-tower scalar extension is the actual published finite Tate sheaf.
The displayed equation on the lifted ring is precisely its annihilator hypothesis.
Source: latest blueprint, finite admissible stages (blueprint: sk-def-sf-weil-complexes).
Proof: reduction of the integral root limit at level n+1 is the finite root module.
Extension to A and associativity of scalar extension give A tensor that root module.
The internal/sectionwise equivalence and the canonical constant-ring comparison preserve
the scalar-root tensor generators, giving the asserted underlying-sheaf isomorphism. -/
theorem finiteLine_published (T : Scheme.{u})
    [∀ x : T, Invertible (ell : T.residueField x)]
    (A : CommRingCat.{0}) [hfin : Finite A] (n : ℕ) (hA : (ell ^ (n + 1) : A) = 0)
    :
    Nonempty (((Coefficient.finite A hfin n hA).firstLine ell T).X ≅
      (SheafOfModules.toSheaf _).obj
        (spFiniteTwist T ell (ULift.{u + 1} A) n
          ((Nat.cast_pow ell (n + 1)).symm.trans (finiteLiftAnnihilator ell A n hA)))) := by
  sorry

/-- The root-tower presentation is the published integral, rational and Qbar Tate sheaf.
Source: latest blueprint, actual Tate sheaves clause
(blueprint: sk-def-sf-weil-complexes).
Proof: compare the finite scalar-root tensors on each compatible primitive-root cover.
Their maps respect every projection, so the inverse-limit universal property identifies
the integral lines. Scalar association identifies the rational lines, and the compatible
finite-subextension coprojections identify Qbar. These are comparisons of the specified
sheaves, rather than replacement coefficient constructions. -/
theorem firstLine_published (T : Scheme.{u})
    [∀ x : T, Invertible (ell : T.residueField x)] :
    (∀ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty ((Coefficient.integral E).firstLine ell T ≅ spIntegralTwist T ell E) ∧
      Nonempty ((Coefficient.rational E).firstLine ell T ≅ spRationalTwist T ell E)) ∧
    Nonempty (Coefficient.closure.firstLine ell T ≅ spQbarTwist T ell) := by
  sorry

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
          (tateLine ell c T r)) ≅
        spSignedTwist T (condensedRingObj (c.obj ell) T) (c.firstLine ell T) r) := by
  sorry

/-- Multiplication by q is invertible on the coefficient unit in every admissible stage.
Source: latest blueprint, q inverse in Z_ell units (blueprint: sk-def-sf-weil-complexes).
Proof: ell differs from p and q is a power of p, so q is an ell-adic unit.
Its inverse passes through each specified integral coefficient map, including a finite
quotient and the zero ring, and gives a two-sided inverse to scalar multiplication. -/
theorem cardinal_scalar_isIso (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) (T : Scheme.{u}) :
    IsIso (D.q • 𝟙 (𝟙_ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (c.obj ell) T)))) := by
  sorry

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

/-- The zeroth Tate datum is the coefficient-unit structure under its degree-zero unit iso.
Source: latest blueprint, varphi_Lambda = tau_0
(blueprint: sk-def-sf-weil-complexes).
Proof: tateLine at zero is the ordinary coefficient unit and positiveTatePull at zero
is its inverse-image unit map. The single-functor unit comparison identifies its exact
derivation with the coefficient-unit isomorphism of the derived monoidal functor. -/
theorem tateDatum_zero {T : Scheme.{u}} (g : T ≅ T)
    [∀ x : T, Invertible (ell : T.residueField x)] :
    ∃ e : derivedTateLine ell c T 0 ≅ 𝟙_ (c.derived ell T),
      tateDatum ell c g 0 ≪≫ e =
        (action (c.obj ell) g).mapIso e ≪≫
          (Functor.Monoidal.εIso (action (c.obj ell) g)).symm := by
  sorry

/-- The typed twisted-dual datum contains the inverse tensorator before the two structures.
Source: latest blueprint, final displayed composite (blueprint: sk-def-sf-weil-complexes). -/
def twistedDualDatum {T : Scheme.{u}} (g : T ≅ T)
    [∀ x : T, Invertible (ell : T.residueField x)] (K : c.derived ell T)
    (phi : (action (c.obj ell) g).obj K ≅ K) (r : ℤ) :
    (action (c.obj ell) g).obj (dual (c.obj ell) K ⊗ derivedTateLine ell c T r) ≅
      dual (c.obj ell) K ⊗ derivedTateLine ell c T r :=
  tensorDatum (c.obj ell) g (dualDatum (c.obj ell) g K phi) (tateDatum ell c g r)

/-- The bounded constructible finite-Tor condition is supplied only as a domain condition
when the ambient twisted dual is restricted to strict complexes.
Source: latest blueprint, twisted-dual domain (blueprint: sk-def-sf-weil-complexes). -/
def twistedDualComplex {T : Scheme.{u}} (g : T ≅ T)
    [∀ x : T, Invertible (ell : T.residueField x)] (K : Complex (c.obj ell) g) (r : ℤ)
    (hK : (constantModelBoundedConstructible (c.obj ell) T ⊓ fun L ↦
      DerivedCategory.finiteTorAmplitude _ L)
        (dual (c.obj ell) K.carrier.obj ⊗ derivedTateLine ell c T r)) :
    Complex (c.obj ell) g :=
  CategoryTheory.Endofunctor.IsoAlgebra.mk ⟨_, hK⟩
    (ObjectProperty.isoMk _ (twistedDualDatum ell c g K.carrier.obj
      ((ObjectProperty.ι _).mapIso K.str) r))

end AlgebraicGeometry.ProEtale.CondensedRing.StrictWeil
