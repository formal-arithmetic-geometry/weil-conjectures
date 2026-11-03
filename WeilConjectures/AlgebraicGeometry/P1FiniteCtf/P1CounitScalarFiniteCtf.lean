/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleCtfChartDomain
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarData
public import WeilConjectures.AlgebraicGeometry.OrdinaryScalarSite.OrdinaryScalarSiteComparisons
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.Proper.ProperFiniteCoefficientExtension
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.BoundedFlatCoefficientSiteSquare.BoundedFlatCoefficientSiteSquare
public import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientSiteSquare
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleFlatConstructibleModel
public import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleExceptionalObjectComparison
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartP1CounitScalar
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartTateScalar
public import WeilConjectures.AlgebraicGeometry.P1FiniteCtf.P1FiniteCtfNormalizedAdjunction
public import WeilConjectures.AlgebraicGeometry.P1FiniteCtf.P1FiniteCtfOriginCounitScalar
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.SupportedEtaleTensorOrigin.SupportedEtaleTensorOrigin
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
public import WeilConjectures.CategoryTheory.Ringed.RingedProEtaleTorAmplitudeOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtension

/-! # Finite-ctf projective-line counits and coefficient extension

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts, lines 20--35.
(blueprint: lem-sp-p1-counit-scalar).

The pro-etale right functor uses comparison inverse image of the shifted Tate line.
Exact comparison commutes canonically with the shift, so this is q^*(-)(1)[2].
The right scalar arrow is written in etale coordinates using only the normalized
pullback, tensor, shift and balanced Tate comparisons. Its descent is required on
all etale origins, making its value independent of the origin.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v w v' w'
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.P1FiniteCtf
open AdjunctionTransfer OrdinaryScalarSite

-- Fix the standard small-site instance before elaborating ambient object binders.
local instance proEtaleEssentiallySmall (S : Scheme.{u}) :
    EssentiallySmall.{u + 1} S.ProEt := essentiallySmallSelf.{0} _

/-- The intrinsic ordinary pro-etale finite-ctf domain: constructible cohomology,
boundedness, and a single finite Tor interval against every module sheaf. In
particular, an etale origin is a theorem about this domain, not part of its definition.
Source: def-weil-proetale-constructible-sheaf and
 def-weil-proetale-tor-amplitude; Charts (blueprint: lem-sp-p1-counit-scalar). -/
def proCtf (R : Type (u + 1)) [CommRing R] [Finite R] (S : Scheme.{u}) :
    ObjectProperty (_root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} R))) :=
  fun K ↦
    (∀ i : ℤ, IsConstructibleProEtaleFixedModuleSheaf S R
      ((_root_.DerivedCategory.homologyFunctor
        (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} R)) i).obj K)) ∧
    (∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((_root_.DerivedCategory.homologyFunctor
        (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} R)) i).obj K)) ∧
    _root_.DerivedCategory.finiteTorAmplitude
      (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} R)) K

/-- Restrict an actual ambient functor to two specified full subcategories.
Source: Charts, finite-ctf domains (blueprint: lem-sp-p1-counit-scalar). -/
def restrict {C : Type v} [Category.{w} C] {D : Type v'} [Category.{w'} D]
    (P : ObjectProperty C) (Q : ObjectProperty D) (F : C ⥤ D)
    (h : ∀ K, P K → Q (F.obj K)) : P.FullSubcategory ⥤ Q.FullSubcategory :=
  Q.lift (P.ι ⋙ F) (fun K ↦ h K.obj K.property)

/-- The recorded exact comparison inverse image on derived categories.
Source: Charts, finite-site comparison (blueprint: lem-sp-p1-counit-scalar). -/
abbrev sitePull (R : Type (u + 1)) [CommRing R] (S : Scheme.{u}) :=
  (comparisonUpperStar (ModuleCat.{u + 1} R) S).mapDerivedCategory

/-- The ordinary pro-etale projective-line direct image. For this proper map it is
compact support at the trivial compactification, under its canonical identity-open
identification. Source: Charts (blueprint: lem-sp-p1-counit-scalar). -/
abbrev direct (R : Type (u + 1)) [CommRing R] (S : Scheme.{u}) :=
  (lowerStar (ModuleCat.{u + 1} R) (ProjectiveLine S ↘ S)).rightDerivedFunctor

/-- The displayed pro-etale right functor: inverse image followed by right tensor
with comparison inverse image of the shifted finite Tate line. Source: Charts,
canonical pullback/Tate/shift comparisons (blueprint: lem-sp-p1-counit-scalar). -/
def right (R : Type (u + 1)) [CommRing R] (N : ℕ) (hR : (N : R) = 0)
    (S : Scheme.{u}) :=
  EtaleChartComparison.proPull R (ProjectiveLine S ↘ S) ⋙
    (derivedTensor (ModuleCat.{u + 1} R) (ProjectiveLine S)).flip.obj
      ((sitePull R (ProjectiveLine S)).obj
        ((Etale.ordinaryFiniteLine R N hR (ProjectiveLine S))⟦(2 : ℤ)⟧))

/-- The actual pullback and tensor comparison on one right-adjoint input. The two
outer comparisons identify termwise exact comparison with its left-derived model.
Source: Charts, canonical right-object comparison
(blueprint: lem-sp-p1-counit-scalar). -/
def rightSite (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hR : (N : R) = 0) (S : Scheme.{u})
    (K : Etale.DerivedCategoryModule R S) :
    (sitePull R (ProjectiveLine S)).obj
        ((Etale.ordinaryFiniteP1Right R N hR S).obj K) ≅
      (right R N hR S).obj ((sitePull R S).obj K) :=
  let C := comparisonUpperStar (ModuleCat.{u + 1} R) (ProjectiveLine S)
  let L := (Etale.ordinaryFiniteLine R N hR (ProjectiveLine S))⟦(2 : ℤ)⟧
  (C.leftDerivedFunctorIsoMapDerivedCategory.app _).symm ≪≫
    asIso (EtaleChartComparison.nuTensor R (ProjectiveLine S)
      ((Etale.ordinaryFinitePullback R (ProjectiveLine S ↘ S)).obj K) L) ≪≫
    (Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} R)
      (ProjectiveLine S))).mapIso
        (Iso.prod ((EtaleChartComparison.schemeIso R (ProjectiveLine S ↘ S)).app K)
          (C.leftDerivedFunctorIsoMapDerivedCategory.app L)) ≪≫
    (right R N hR S).mapIso
      ((comparisonUpperStar (ModuleCat.{u + 1} R) S).leftDerivedFunctorIsoMapDerivedCategory.app K)

/-- The canonical ordinary right scalar arrow. Its line factor is the published
shifted balanced Tate map, specified on root/scalar generators by
`(z tensor a) tensor b ↦ z tensor phi(a)b`.
Source: Charts, integral Kummer classes and free summands
(blueprint: lem-sp-p1-counit-scalar). -/
def etaleArrow {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (K : Etale.DerivedCategoryModule A S) :
    (scalar.{u} (ProjectiveLine S).smallEtaleTopology φ).obj
        ((Etale.ordinaryFiniteP1Right A N hA S).obj K) ⟶
      (Etale.ordinaryFiniteP1Right B N hB S).obj
        ((scalar S.smallEtaleTopology φ).obj K) :=
  (Etale.ExceptionalCoefficients.tensorIso φ (ProjectiveLine S)).hom.app
      ((Etale.ordinaryFinitePullback A (ProjectiveLine S ↘ S)).obj K,
        (Etale.ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
    ((Etale.ordinaryFiniteTensor B (ProjectiveLine S)).map
      ((Etale.scalarPullbackIso φ (ProjectiveLine S ↘ S)).inv.app K)).app _ ≫
    ((Etale.ordinaryFiniteTensor B (ProjectiveLine S)).obj
      ((Etale.ordinaryFinitePullback B (ProjectiveLine S ↘ S)).obj
        ((scalar S.smallEtaleTopology φ).obj K))).map
      (Etale.VectorTraceScalar.line φ N hN hA hB (ProjectiveLine S)
        (Etale.ordinaryFiniteP1_isUnit N S hS))

/-- A projective-line adjunction on the actual ordinary pro-etale finite-ctf domain,
with its counit fixed by the proper counit-mate site comparison and the normalized
ordinary trace. The origin clause is essential surjectivity of that same comparison;
it ensures that normalization at etale origins determines every component.
Source: Charts and det-sp-et-proet-adjunction-transfer, actual counit formula
(blueprint: lem-sp-p1-counit-scalar). -/
structure NormalizedAdjunction (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) where
  comparison_preserves : ∀ L, etaleProperty R S L →
    proCtf R S ((sitePull R S).obj L)
  origins : ∀ K, proCtf R S K → ∃ L, etaleProperty R S L ∧
    Nonempty ((sitePull R S).obj L ≅ K)
  direct_preserves : ∀ M, proCtf R (ProjectiveLine S) M →
    proCtf R S ((direct R S).obj M)
  right_preserves : ∀ K, proCtf R S K →
    proCtf R (ProjectiveLine S) ((right R N hR S).obj K)
  adjunction :
    restrict (proCtf R (ProjectiveLine S)) (proCtf R S)
        (direct R S) direct_preserves ⊣
      restrict (proCtf R S) (proCtf R (ProjectiveLine S))
        (right R N hR S) right_preserves
  counit_normalization : ∀ (L : Etale.DerivedCategoryModule R S)
      (hL : etaleProperty R S L),
    (ambientEtaleProEtaleDirectImageComparison R (ProjectiveLine S ↘ S)).app
        ((Etale.ordinaryFiniteP1Right R N hR S).obj L) ≫
      (direct R S).map (rightSite R N hR S L).hom ≫
      (adjunction.counit.app ⟨(sitePull R S).obj L, comparison_preserves L hL⟩).hom =
    (sitePull R S).map
      ((Etale.projectiveLineTraceDatum N hN R hR S hS).adjunction.counit.app L)

/-- The right scalar arrow in an arbitrary etale-origin coordinate for K. Every
factor is prescribed: the origin iso, the right/site comparison, scalar/site delta,
the ordinary balanced arrow, and the inverse output delta. No map is chosen.
Source: Charts, transport of the canonical right arrow
(blueprint: lem-sp-p1-counit-scalar). -/
def arrowOnOrigin {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)))
    (L : Etale.DerivedCategoryModule A S) (e : (sitePull A S).obj L ≅ K) :
    (scalar.{u} (Scheme.ProEt.topology (ProjectiveLine S)) φ).obj
        ((right A N hA S).obj K) ⟶
      (right B N hB S).obj ((scalar.{u} (Scheme.ProEt.topology S) φ).obj K) :=
  (scalar.{u} (Scheme.ProEt.topology (ProjectiveLine S)) φ).map
      ((right A N hA S).map e.inv ≫ (rightSite A N hA S L).inv) ≫
    (delta.{u} φ (ProjectiveLine S)).hom.app ((Etale.ordinaryFiniteP1Right A N hA S).obj L) ≫
    (sitePull B (ProjectiveLine S)).map (etaleArrow φ N hN hA hB S hS L) ≫
    (rightSite B N hB S ((scalar S.smallEtaleTopology φ).obj L)).hom ≫
    (right B N hB S).map
      ((delta.{u} φ S).inv.app L ≫ (scalar.{u} (Scheme.ProEt.topology S) φ).map e.hom)

/-- The actual pro-etale counit identity, invertibility and inverse-beta mate
characterization. The hom equivalence belongs to the normalized restricted adjunction;
its arrows are included by the full subcategory inclusion.
The proper coefficient mate is the compact-support coefficient map at the trivial
compactification under the identity-open normalization.
Source: Charts, final two sentences (blueprint: lem-sp-p1-counit-scalar). -/
def ProIdentity {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (dA : NormalizedAdjunction A N hN hA S hS)
    (dB : NormalizedAdjunction B N hN hB S hS)
    (hTS : ∀ K, proCtf A S K → proCtf B S
      ((scalar.{u} (Scheme.ProEt.topology S) φ).obj K))
    (hTP : ∀ M, proCtf A (ProjectiveLine S) M →
      proCtf B (ProjectiveLine S)
        ((scalar.{u} (Scheme.ProEt.topology (ProjectiveLine S)) φ).obj M))
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)))
    (hK : proCtf A S K)
    (a : (scalar.{u} (Scheme.ProEt.topology (ProjectiveLine S)) φ).obj
        ((right A N hA S).obj K) ⟶
      (right B N hB S).obj ((scalar.{u} (Scheme.ProEt.topology S) φ).obj K)) : Prop :=
  (proEtaleGamma.{u} φ (ProjectiveLine S ↘ S)).app ((right A N hA S).obj K) ≫
      (direct B S).map a ≫
      (dB.adjunction.counit.app
        ⟨(scalar.{u} (Scheme.ProEt.topology S) φ).obj K, hTS K hK⟩).hom =
    (scalar.{u} (Scheme.ProEt.topology S) φ).map (dA.adjunction.counit.app ⟨K, hK⟩).hom ∧
  ∃ hβ : IsIso ((proEtaleGamma.{u} φ (ProjectiveLine S ↘ S)).app
      ((right A N hA S).obj K)),
    IsIso a ∧
    a = (dB.adjunction.homEquiv
      ⟨(scalar.{u} (Scheme.ProEt.topology (ProjectiveLine S)) φ).obj
        ((right A N hA S).obj K), hTP _ (dA.right_preserves K hK)⟩
      ⟨(scalar.{u} (Scheme.ProEt.topology S) φ).obj K, hTS K hK⟩
      (ObjectProperty.homMk
        (@inv _ _ _ _ ((proEtaleGamma.{u} φ (ProjectiveLine S ↘ S)).app
          ((right A N hA S).obj K)) hβ ≫
          (scalar.{u} (Scheme.ProEt.topology S) φ).map
            (dA.adjunction.counit.app ⟨K, hK⟩).hom))).hom

private theorem proCtf_iff
    (R : Type (u + 1)) [CommRing R] [Finite R] (T : Scheme.{u}) [IsNoetherian T]
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R))) :
    proCtf R T K ↔ proEtaleProperty R T K := by
  have hc := congrFun (exceptionalTransport_constructible_comparison R T) K
  constructor
  · intro hK
    obtain ⟨a, b, hab, hz⟩ := hK.2.1
    refine ⟨hc.mp ⟨?_, hK.1⟩, hK.2.2⟩
    exact ⟨⟨a, (_root_.DerivedCategory.isGE_iff K a).2
      (fun i hi ↦ hz i (.inl hi))⟩,
      ⟨b, (_root_.DerivedCategory.isLE_iff K b).2 (fun i hi ↦ hz i (.inr hi))⟩⟩
  · rintro ⟨hcons, htor⟩
    obtain ⟨hb, hc⟩ := hc.mpr hcons
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hb
    refine ⟨hc, ⟨min a b, b, min_le_right _ _, fun i hi ↦ ?_⟩, htor⟩
    rcases hi with hi | hi
    · exact (_root_.DerivedCategory.isGE_iff K a).1 ha i
        (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff K b).1 hb i hi

private theorem proCtf_iso
    (R : Type (u + 1)) [CommRing R] [Finite R] (T : Scheme.{u}) [IsNoetherian T]
    {K L : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R))}
    (e : K ≅ L) (hK : proCtf R T K) : proCtf R T L := by
  rw [proCtf_iff] at hK ⊢
  exact ⟨((Etale.DerivedCategory.isBoundedConstructible R T).map
    (sitePull R T)).prop_of_iso e hK.1,
    (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso e hK.2⟩

private theorem site_preserves
    (R : Type (u + 1)) [CommRing R] [Finite R] (T : Scheme.{u}) [IsNoetherian T]
    (L : Etale.DerivedCategoryModule R T) (hL : etaleProperty R T L) :
    proCtf R T ((sitePull R T).obj L) := by
  rw [proCtf_iff]
  refine ⟨ObjectProperty.prop_map_obj _ _ hL.1, ?_⟩
  obtain ⟨a, b, ht⟩ := hL.2
  exact ⟨a, b, (_root_.DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj_iff
    (comparisonUpperStar (ModuleCat.{u + 1} R) T) a b L).2 ht⟩

private theorem site_origins
    (R : Type (u + 1)) [CommRing R] [Finite R] (T : Scheme.{u}) [IsNoetherian T]
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R)))
    (hK : proCtf R T K) :
    ∃ L, etaleProperty R T L ∧ Nonempty ((sitePull R T).obj L ≅ K) := by
  obtain ⟨⟨L, hc, ⟨e⟩⟩, ht⟩ := (proCtf_iff R T K).1 hK
  obtain ⟨a, b, ht⟩ := (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso e.symm ht
  exact ⟨L, ⟨hc, a, b, (_root_.DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj_iff
    (comparisonUpperStar (ModuleCat.{u + 1} R) T) a b L).1 ht⟩, ⟨e⟩⟩

private theorem scalar_preserves_etale
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (ℓ n : ℕ) (hℓ : ℓ.Prime) (φ : A →+* B)
    (hA : ((ℓ ^ n : ℕ) : A) = 0) (hB : ((ℓ ^ n : ℕ) : B) = 0)
    (T : Scheme.{u}) [IsNoetherian T]
    (K : Etale.DerivedCategoryModule A T) (hK : etaleProperty A T K) :
    etaleProperty B T ((scalar T.smallEtaleTopology φ).obj K) := by
  obtain ⟨a, b, ht⟩ := hK.2
  have hprimary (R : Type (u + 1)) [CommRing R] (hR : ((ℓ ^ n : ℕ) : R) = 0) :
      ∃ m : ℕ, ∀ x : R, (ℓ ^ m) • x = 0 := by
    exact ⟨n, fun x ↦ by rw [nsmul_eq_mul, hR, zero_mul]⟩
  have h := finiteCoefficientInputModels T ℓ hℓ A B
    (hprimary A hA) (hprimary B hB) φ (min a b) b (min_le_right _ _) K hK.1
    (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
      (ht.mono (min_le_left _ _) le_rfl))
  obtain ⟨P, hf, hc, hz, hp, he, hfe, hze, hpe, hee, hfn, hzn, hpn, hen,
    hfne, hzne, hpne, hene, hbc, htor, hrest⟩ := h
  exact ⟨hbc, min a b, b,
    Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 htor⟩

private theorem scalar_preserves_pro
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (ℓ n : ℕ) (hℓ : ℓ.Prime) (φ : A →+* B)
    (hA : ((ℓ ^ n : ℕ) : A) = 0) (hB : ((ℓ ^ n : ℕ) : B) = 0)
    (T : Scheme.{u}) [IsNoetherian T]
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (hK : proCtf A T K) :
    proCtf B T ((scalar (Scheme.ProEt.topology T) φ).obj K) := by
  obtain ⟨L, hL, ⟨e⟩⟩ := site_origins A T K hK
  have h := site_preserves B T _ (scalar_preserves_etale ℓ n hℓ φ hA hB T L hL)
  exact proCtf_iso B T ((delta φ T).symm.app L ≪≫
    (scalar (Scheme.ProEt.topology T) φ).mapIso e) h

private theorem etaleArrow_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (K : Etale.DerivedCategoryModule A S) :
    (reductionEtaleP1ScalarIso φ S N hA hB hS K).hom =
      etaleArrow φ N hN hA hB S hS K := by
  simp only [reductionEtaleP1ScalarIso, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Iso.prod_hom, Functor.uncurry_obj_map, Iso.symm_hom,
    Etale.ordinaryChartShiftedLineScalarEq φ N hN, etaleArrow, Functor.prod_obj,
    Functor.comp_obj]
  rfl

private theorem etale_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (K : Etale.DerivedCategoryModule A S) :
    (Etale.scalarMate φ (ProjectiveLine S ↘ S)).app
        ((Etale.ordinaryFiniteP1Right A N hA S).obj K) ≫
      (Etale.ordinaryFinitePushforward B (ProjectiveLine S ↘ S)).map
        (etaleArrow φ N hN hA hB S hS K) ≫
      (Etale.projectiveLineTraceDatum N hN B hB S hS).adjunction.counit.app
        ((scalar S.smallEtaleTopology φ).obj K) =
    (scalar S.smallEtaleTopology φ).map
      ((Etale.projectiveLineTraceDatum N hN A hA S hS).adjunction.counit.app K) := by
  rw [← etaleArrow_eq]
  exact Etale.ordinaryChartP1CounitScalar φ N hN hA hB S hS
    (Etale.projectiveLineTraceTransport N hN A hA)
    (Etale.projectiveLineTraceTransport N hN B hB)
    (Etale.projectiveLineTraceDatum N hN A hA S hS)
    (Etale.projectiveLineTraceDatum N hN B hB S hS) K

private theorem transpose_of_counit
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {X : C} {Y Z : D} (β : Y ⟶ F.obj X) [IsIso β]
    (a : X ⟶ G.obj Z) (ε : Y ⟶ Z)
    (h : β ≫ F.map a ≫ adj.counit.app Z = ε) :
    a = adj.homEquiv _ _ (inv β ≫ ε) := by
  apply (adj.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply]
  change F.map a ≫ adj.counit.app Z = inv β ≫ ε
  rw [← h, IsIso.inv_hom_id_assoc]

private theorem arrowOnOrigin_transport
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)))
    (L : Etale.DerivedCategoryModule A S) (e : (sitePull A S).obj L ≅ K) :
    arrowOnOrigin φ N hN hA hB S hS K L e =
      (scalar (Scheme.ProEt.topology (ProjectiveLine S)) φ).map
          ((right A N hA S).map e.inv) ≫
        arrowOnOrigin φ N hN hA hB S hS ((sitePull A S).obj L) L (Iso.refl _) ≫
        (right B N hB S).map ((scalar (Scheme.ProEt.topology S) φ).map e.hom) := by
  simp [arrowOnOrigin, Functor.map_comp, Category.assoc]

private theorem origin_counit_transport
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (dA : NormalizedAdjunction A N hN hA S hS)
    (dB : NormalizedAdjunction B N hN hB S hS)
    (hTS : ∀ K, proCtf A S K → proCtf B S
      ((scalar (Scheme.ProEt.topology S) φ).obj K))
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)))
    (hK : proCtf A S K)
    (L : Etale.DerivedCategoryModule A S) (hL : etaleProperty A S L)
    (e : (sitePull A S).obj L ≅ K)
    (h : (proEtaleGamma φ (ProjectiveLine S ↘ S)).app
          ((right A N hA S).obj ((sitePull A S).obj L)) ≫
        (direct B S).map
          (arrowOnOrigin φ N hN hA hB S hS ((sitePull A S).obj L) L (Iso.refl _)) ≫
        (dB.adjunction.counit.app
          ⟨(scalar (Scheme.ProEt.topology S) φ).obj ((sitePull A S).obj L),
            hTS _ (dA.comparison_preserves L hL)⟩).hom =
      (scalar (Scheme.ProEt.topology S) φ).map
        (dA.adjunction.counit.app
          ⟨(sitePull A S).obj L, dA.comparison_preserves L hL⟩).hom) :
    (proEtaleGamma φ (ProjectiveLine S ↘ S)).app ((right A N hA S).obj K) ≫
        (direct B S).map (arrowOnOrigin φ N hN hA hB S hS K L e) ≫
        (dB.adjunction.counit.app
          ⟨(scalar (Scheme.ProEt.topology S) φ).obj K, hTS K hK⟩).hom =
      (scalar (Scheme.ProEt.topology S) φ).map
        (dA.adjunction.counit.app ⟨K, hK⟩).hom := by
  let T := scalar (Scheme.ProEt.topology S) φ
  let U := scalar (Scheme.ProEt.topology (ProjectiveLine S)) φ
  have hn := (proEtaleGamma φ (ProjectiveLine S ↘ S)).naturality
    ((right A N hA S).map e.inv)
  have hb := congrArg (fun f ↦ f.hom) (dB.adjunction.counit.naturality
    (ObjectProperty.homMk (T.map e.hom) :
      (⟨T.obj ((sitePull A S).obj L), hTS _ (dA.comparison_preserves L hL)⟩ :
        (proCtf B S).FullSubcategory) ⟶ ⟨T.obj K, hTS K hK⟩))
  have ha := congrArg (fun f ↦ f.hom) (dA.adjunction.counit.naturality
    (ObjectProperty.homMk e.inv : (⟨K, hK⟩ : (proCtf A S).FullSubcategory) ⟶
      ⟨(sitePull A S).obj L, dA.comparison_preserves L hL⟩))
  change T.map ((direct A S).map ((right A N hA S).map e.inv)) ≫ _ =
    _ ≫ (direct B S).map (U.map ((right A N hA S).map e.inv)) at hn
  change (direct B S).map ((right B N hB S).map (T.map e.hom)) ≫ _ =
    _ ≫ T.map e.hom at hb
  change (direct A S).map ((right A N hA S).map e.inv) ≫ _ =
    _ ≫ e.inv at ha
  rw [arrowOnOrigin_transport]
  simp only [Functor.map_comp, Category.assoc]
  erw [hb, ← reassoc_of% hn, reassoc_of% h]
  rw [← T.map_comp_assoc, ha, T.map_comp, Category.assoc,
    ← T.map_comp, e.inv_hom_id, T.map_id, Category.comp_id]

private theorem isIso_natural_app_of_iso
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (α : F ⟶ G) {X Y : C} (e : X ≅ Y) [IsIso (α.app X)] :
    IsIso (α.app Y) := by
  have h : α.app Y = F.map e.inv ≫ α.app X ≫ G.map e.hom := by
    rw [← α.naturality, ← F.map_comp_assoc, e.inv_hom_id,
      F.map_id, Category.id_comp]
  rw [h]
  infer_instance

private theorem pro_identity_of_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (dA : NormalizedAdjunction A N hN hA S hS)
    (dB : NormalizedAdjunction B N hN hB S hS)
    (hTS : ∀ K, proCtf A S K → proCtf B S
      ((scalar (Scheme.ProEt.topology S) φ).obj K))
    (hTP : ∀ M, proCtf A (ProjectiveLine S) M →
      proCtf B (ProjectiveLine S)
        ((scalar (Scheme.ProEt.topology (ProjectiveLine S)) φ).obj M))
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)))
    (hK : proCtf A S K)
    (a : (scalar (Scheme.ProEt.topology (ProjectiveLine S)) φ).obj
        ((right A N hA S).obj K) ⟶
      (right B N hB S).obj ((scalar (Scheme.ProEt.topology S) φ).obj K))
    [IsIso ((proEtaleGamma φ (ProjectiveLine S ↘ S)).app ((right A N hA S).obj K))]
    [IsIso a]
    (h : (proEtaleGamma φ (ProjectiveLine S ↘ S)).app ((right A N hA S).obj K) ≫
        (direct B S).map a ≫
        (dB.adjunction.counit.app
          ⟨(scalar (Scheme.ProEt.topology S) φ).obj K, hTS K hK⟩).hom =
      (scalar (Scheme.ProEt.topology S) φ).map
        (dA.adjunction.counit.app ⟨K, hK⟩).hom) :
    ProIdentity φ N hN hA hB S hS dA dB hTS hTP K hK a := by
  refine ⟨h, inferInstance, inferInstance, ?_⟩
  let X : (proCtf B (ProjectiveLine S)).FullSubcategory :=
    ⟨(scalar (Scheme.ProEt.topology (ProjectiveLine S)) φ).obj
      ((right A N hA S).obj K), hTP _ (dA.right_preserves K hK)⟩
  let Y : (proCtf B S).FullSubcategory :=
    ⟨(scalar (Scheme.ProEt.topology S) φ).obj K, hTS K hK⟩
  have ht : (ObjectProperty.homMk a : X ⟶
      (restrict (proCtf B S) (proCtf B (ProjectiveLine S))
        (right B N hB S) dB.right_preserves).obj Y) =
      dB.adjunction.homEquiv X Y (ObjectProperty.homMk
        (inv ((proEtaleGamma φ (ProjectiveLine S ↘ S)).app
          ((right A N hA S).obj K)) ≫
          (scalar (Scheme.ProEt.topology S) φ).map
            (dA.adjunction.counit.app ⟨K, hK⟩).hom)) := by
    apply (dB.adjunction.homEquiv X Y).symm.injective
    rw [Equiv.symm_apply_apply]
    apply ObjectProperty.hom_ext
    change (direct B S).map a ≫ (dB.adjunction.counit.app Y).hom = _
    erw [← h, IsIso.inv_hom_id_assoc]
    rfl
  exact congrArg (fun f ↦ f.hom) ht

/-- Scalar compatibility of the actual normalized projective-line counits on both
finite-ctf domains, including characteristic zero and nonflat coefficient maps.
All data introduced existentially are characterized by the displayed canonical maps;
no extra geometric, coefficient, or comparison hypothesis is assumed.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts, lines 20--35.
(blueprint: lem-sp-p1-counit-scalar).

Proof plan:
1. Since char(k) differs from ell, N is invertible on S and P, including char(k)=0.
Finite type over a field makes S Noetherian; properness does the same for P.
The chart-domain theorem supplies preservation, the finite-ctf comparison equivalence,
and an etale origin for every pro-etale input.
2. Apply lem-pur-ordinary-chart-p1-counit-scalar to the etale input. Its trace is
projection onto the free twisted summand of the Kummer-normalized splitting.
lem-sp-finite-p1-coefficient-splitting supplies the same integral Kummer and diagonal
classes. Thus its right arrow is precisely etaleArrow, with the balanced Tate map.
3. Transfer each actual adjunction using det-sp-et-proet-adjunction-transfer and
the specified compact-support comparison. The right functor is identified by
rightSite, built from the actual pullback and tensor comparisons. Exact comparison
commutes with shifts. Scalar/site delta and the balanced Tate map identify its
right scalar arrow with arrowOnOrigin for every origin.
4. Apply lem-sp-et-proet-coefficient-compatibility at the right-adjoint input.
Paste its site/coefficient square with the two normalized counit equations and
the right-arrow comparison. Naturality moves the outer deltas and origin isos.
Cancel the invertible outer maps. The ordinary counit equation then gives the
pro-etale equation, independently of the chosen origin.
5. lem-asd-proper-finite-coefficient-extension makes ordinary beta invertible.
The site/coefficient square and the comparison equivalences do so on pro-etale
finite-ctf inputs. Precompose the counit equation with inverse beta; the actual
B adjunction Hom bijection identifies the specified arrow as its unique transpose.
No purity, exchange, or biduality comparison is used. -/
theorem p1CounitScalarFiniteCtf
    (ℓ n : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (_hk : Finite k ∨ IsAlgClosed k) (_hchar : ringChar k ≠ ℓ)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (hA : ((ℓ ^ n : ℕ) : A) = 0) (hB : ((ℓ ^ n : ℕ) : B) = 0)
    (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))] :
    ∃ hN : 0 < ℓ ^ n, ∃ hS : IsUnit ((ℓ ^ n : ℕ) : Γ(S, ⊤)),
    ∃ hNoeth : IsNoetherian S,
    have := hNoeth
    (∀ (K : Etale.DerivedCategoryModule A S) (_hK : etaleProperty A S K),
      (Etale.scalarMate φ (ProjectiveLine S ↘ S)).app
          ((Etale.ordinaryFiniteP1Right A (ℓ ^ n) hA S).obj K) ≫
        (Etale.ordinaryFinitePushforward B (ProjectiveLine S ↘ S)).map
          (etaleArrow φ (ℓ ^ n) hN hA hB S hS K) ≫
        (Etale.projectiveLineTraceDatum (ℓ ^ n) hN B hB S hS).adjunction.counit.app
          ((scalar S.smallEtaleTopology φ).obj K) =
      (scalar S.smallEtaleTopology φ).map
        ((Etale.projectiveLineTraceDatum (ℓ ^ n) hN A hA S hS).adjunction.counit.app K) ∧
      ∃ hβ : IsIso ((Etale.scalarMate φ (ProjectiveLine S ↘ S)).app
          ((Etale.ordinaryFiniteP1Right A (ℓ ^ n) hA S).obj K)),
        IsIso (etaleArrow φ (ℓ ^ n) hN hA hB S hS K) ∧
        etaleArrow φ (ℓ ^ n) hN hA hB S hS K =
          (Etale.projectiveLineTraceDatum (ℓ ^ n) hN B hB S hS).adjunction.homEquiv _ _
            (@inv _ _ _ _ ((Etale.scalarMate φ (ProjectiveLine S ↘ S)).app
              ((Etale.ordinaryFiniteP1Right A (ℓ ^ n) hA S).obj K)) hβ ≫
              (scalar S.smallEtaleTopology φ).map
                ((Etale.projectiveLineTraceDatum (ℓ ^ n) hN A hA S hS).adjunction.counit.app K))) ∧
    ∃ dA : NormalizedAdjunction A (ℓ ^ n) hN hA S hS,
    ∃ dB : NormalizedAdjunction B (ℓ ^ n) hN hB S hS,
    ∃ hTS : ∀ K, proCtf A S K → proCtf B S
      ((scalar.{u} (Scheme.ProEt.topology S) φ).obj K),
    ∃ hTP : ∀ M, proCtf A (ProjectiveLine S) M →
      proCtf B (ProjectiveLine S)
        ((scalar.{u} (Scheme.ProEt.topology (ProjectiveLine S)) φ).obj M),
    ∀ (K : _root_.DerivedCategory
        (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)))
      (hK : proCtf A S K),
      ∃ a : (scalar.{u} (Scheme.ProEt.topology (ProjectiveLine S)) φ).obj
          ((right A (ℓ ^ n) hA S).obj K) ⟶
        (right B (ℓ ^ n) hB S).obj ((scalar.{u} (Scheme.ProEt.topology S) φ).obj K),
        (∀ (L : Etale.DerivedCategoryModule A S) (_hL : etaleProperty A S L)
          (e : (sitePull A S).obj L ≅ K),
          a = arrowOnOrigin φ (ℓ ^ n) hN hA hB S hS K L e) ∧
        ProIdentity φ (ℓ ^ n) hN hA hB S hS dA dB hTS hTP K hK a  := by
  have hℓ : (ℓ : k) ≠ 0 := fun h ↦ _hchar (CharP.ringChar_of_prime_eq_zero (Fact.out : ℓ.Prime) h)
  let g : k →+* Γ(S, ⊤) :=
    (S ↘ Spec (.of k)).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  have hS : IsUnit ((ℓ ^ n : ℕ) : Γ(S, ⊤)) := by
    simpa only [map_natCast, map_pow, Nat.cast_pow] using
      ((isUnit_iff_ne_zero.mpr hℓ).pow n).map g
  have : IsLocallyNoetherian S :=
    LocallyOfFiniteType.isLocallyNoetherian (S ↘ Spec (.of k))
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (S ↘ Spec (.of k))
  have hNoeth : IsNoetherian S := ⟨⟩
  have := hNoeth
  refine ⟨pow_pos (Fact.out : ℓ.Prime).pos n, hS, hNoeth, ?_, ?_⟩
  · intro K hK
    have hN : 0 < ℓ ^ n := pow_pos (Fact.out : ℓ.Prime).pos n
    have h := etale_counit φ (ℓ ^ n) hN hA hB S hS K
    have : IsLocallyNoetherian (ProjectiveLine S) :=
      LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine S ↘ S)
    have : CompactSpace (ProjectiveLine S) :=
      QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine S ↘ S)
    have : IsNoetherian (ProjectiveLine S) := ⟨⟩
    have hβ := (Etale.properFiniteCoefficientExtension φ (ProjectiveLine S ↘ S)).1
      ((Etale.ordinaryFiniteP1Right A (ℓ ^ n) hA S).obj K)
    have := hβ
    have ha : IsIso (etaleArrow φ (ℓ ^ n) hN hA hB S hS K) := by
      rw [← etaleArrow_eq]
      infer_instance
    exact ⟨h, hβ, ha, transpose_of_counit _ _ _ _ h⟩
  · have hN : 0 < ℓ ^ n := pow_pos (Fact.out : ℓ.Prime).pos n
    have : IsLocallyNoetherian (ProjectiveLine S) :=
      LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine S ↘ S)
    have : CompactSpace (ProjectiveLine S) :=
      QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine S ↘ S)
    have : IsNoetherian (ProjectiveLine S) := ⟨⟩
    obtain ⟨dA⟩ := p1FiniteCtfNormalizedAdjunction ℓ n k _hk _hchar A hA S hN hS
    obtain ⟨dB⟩ := p1FiniteCtfNormalizedAdjunction ℓ n k _hk _hchar B hB S hN hS
    let hTS := scalar_preserves_pro ℓ n (Fact.out : ℓ.Prime) φ hA hB S
    let hTP := scalar_preserves_pro ℓ n (Fact.out : ℓ.Prime) φ hA hB (ProjectiveLine S)
    refine ⟨dA, dB, hTS, hTP, ?_⟩
    intro K hK
    have horigin (L : Etale.DerivedCategoryModule A S) (hL : etaleProperty A S L)
        (e : (sitePull A S).obj L ≅ K) :
        ProIdentity φ (ℓ ^ n) hN hA hB S hS dA dB hTS hTP K hK
          (arrowOnOrigin φ (ℓ ^ n) hN hA hB S hS K L e) := by
      obtain ⟨hβ, ha, hc⟩ := p1FiniteCtfOriginCounitScalar φ (ℓ ^ n) hN hA hB
        S hS dA dB hTS L hL (etale_counit φ (ℓ ^ n) hN hA hB S hS L)
      have := hβ
      have := ha
      have : IsIso ((proEtaleGamma φ (ProjectiveLine S ↘ S)).app
          ((right A (ℓ ^ n) hA S).obj K)) :=
        isIso_natural_app_of_iso _ ((right A (ℓ ^ n) hA S).mapIso e)
      have : IsIso (arrowOnOrigin φ (ℓ ^ n) hN hA hB S hS K L e) := by
        rw [arrowOnOrigin_transport]
        infer_instance
      exact pro_identity_of_counit φ (ℓ ^ n) hN hA hB S hS dA dB hTS hTP K hK _
        (origin_counit_transport φ (ℓ ^ n) hN hA hB S hS dA dB hTS K hK L hL e hc)
    obtain ⟨L, hL, ⟨e⟩⟩ := dA.origins K hK
    refine ⟨arrowOnOrigin φ (ℓ ^ n) hN hA hB S hS K L e, ?_, horigin L hL e⟩
    intro L' hL' e'
    exact (horigin L hL e).2.choose_spec.2.trans
      (horigin L' hL' e').2.choose_spec.2.symm

end AlgebraicGeometry.ProEtale.P1FiniteCtf
