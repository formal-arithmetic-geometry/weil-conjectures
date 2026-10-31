/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackExact
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.SecSmoothPurity.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.RingedProEtaleTorAmplitudeOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
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
public import WeilConjectures.AlgebraicGeometry.WitnessCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtension
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import Mathlib.AlgebraicGeometry.Noetherian

import WeilConjectures.AlgebraicGeometry.EtaleFlatConstructibleModel
import WeilConjectures.SecSmoothPurity.SupportedEtaleTensorOrigin
import WeilConjectures.AlgebraicGeometry.BoundedFlatCoefficientSiteSquare
import WeilConjectures.AlgebraicGeometry.ConstructibleCoefficientSiteSquare
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-! # Finite coefficient and site extension of bounded flat input models

Source: Stacks Project, more-etale.tex, Tag 0GL6, bounded finite-Tor domain
verification, and the eight-step deduction recorded in the DAG
(blueprint: lem-sp-finite-coefficient-input-models).

The complex comparison below is the termwise conjugate of identity-on-sections
scalar restriction. Both scalar functors retain the target coefficient action.
The Tor conclusion tests every module sheaf on the relevant site.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry

/-- Additivity of ordinary pro-etale scalar extension, from its existing adjunction.
Source: Stacks 03EK (blueprint: lem-sp-finite-coefficient-input-models). -/
instance finiteInputProScalar_additive {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) : (ProEtale.sheafExtendScalars φ X).Additive :=
  (ProEtale.sheafExtendScalarsAdjunction φ X).left_adjoint_additive

/-- Additivity of ordinary etale scalar extension, from its existing adjunction.
Source: Stacks 03EK (blueprint: lem-sp-finite-coefficient-input-models). -/
instance finiteInputEtaleScalar_additive {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) : (ProEtale.etaleSheafExtendScalars φ X).Additive :=
  (ProEtale.etaleSheafExtendScalarsAdjunction φ X).left_adjoint_additive

/-- The published left-derived scalar extension on the actual small pro-etale site.
The explicit essential-smallness witness fixes the standard coefficient size.
Source: Stacks 06YY (blueprint: lem-sp-finite-coefficient-input-models). -/
abbrev finiteInputProScalar {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) :
    _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) :=
  @ProEtale.pbcFixedScalarExtension.{u} X.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X)
    A B inferInstance inferInstance φ

/-- The actual termwise etale scalar extension, retaining the B-action.
Source: Stacks 06YY (blueprint: lem-sp-finite-coefficient-input-models). -/
abbrev finiteInputEtaleExtension {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u})
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :=
  ((ProEtale.etaleSheafExtendScalars φ X).mapHomologicalComplex (.up ℤ)).obj P

/-- Exact site inverse image applied termwise to the chosen input model.
Source: Stacks 099R (blueprint: lem-sp-finite-coefficient-input-models). -/
abbrev finiteInputComparison (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :=
  ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapHomologicalComplex
    (.up ℤ)).obj P

/-- The actual termwise pro-etale scalar extension, retaining the B-action.
Source: Stacks 06YY (blueprint: lem-sp-finite-coefficient-input-models). -/
abbrev finiteInputProExtension {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u})
    (P : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ℤ) :=
  ((ProEtale.sheafExtendScalars φ X).mapHomologicalComplex (.up ℤ)).obj P

/-- The canonical B-linear complex comparison, obtained from the scalar-restriction
conjugate, in the direction (nu P) tensor B to nu(P tensor B).
Source: Stacks 03EL and 07A4 (blueprint: lem-sp-finite-coefficient-input-models). -/
def finiteInputTensorComparison {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u})
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    finiteInputProExtension φ X (finiteInputComparison A X P) ≅
      finiteInputComparison B X (finiteInputEtaleExtension φ X P) :=
  ((NatIso.mapHomologicalComplex
    (ProEtale.etaleSheafExtendScalarsCompComparisonUpperStarIso φ X) (.up ℤ)).app P).symm

/-- The canonical tensor comparison in the derived category, obtained by localizing
its specified termwise B-linear complex comparison. On the K-flat models in the
main theorem this identifies the two representatives of (N_X L)_B.
Source: Stacks 07A4 (blueprint: lem-sp-finite-coefficient-input-models). -/
def finiteInputDerivedTensorComparison {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u})
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    _root_.DerivedCategory.Q.obj
        (finiteInputProExtension φ X (finiteInputComparison A X P)) ≅
      _root_.DerivedCategory.Q.obj
        (finiteInputComparison B X (finiteInputEtaleExtension φ X P)) :=
  _root_.DerivedCategory.Q.mapIso (finiteInputTensorComparison φ X P)

private theorem proConstructible_of_iso
    (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R] [Finite R]
    {F G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)} (e : F ≅ G)
    (hG : Scheme.IsConstructibleProEtaleFixedModuleSheaf X R G) :
    Scheme.IsConstructibleProEtaleFixedModuleSheaf X R F := by
  obtain ⟨S, hn, hs, hG⟩ := hG
  refine ⟨S, hn, hs, fun i ↦ ?_⟩
  let d := (ProEtale.upperStar (ModuleCat.{u + 1} R) (S.immersion i)).mapIso e
  obtain ⟨hl, hf⟩ := hG i
  obtain ⟨I, U, f, hc, hm⟩ := hl
  refine ⟨⟨I, U, f, hc, fun j ↦ ?_⟩, fun Ω _ _ y ↦ ?_⟩
  · obtain ⟨M, ⟨m⟩⟩ := hm j
    exact ⟨M, ⟨((Scheme.ProEt.topology (S.domain i)).overPullback
      (ModuleCat.{u + 1} R) (U j)).mapIso d ≪≫ m⟩⟩
  · let t : Scheme.proEtaleGeometricFixedModuleStalk y R
        ((ProEtale.upperStar (ModuleCat.{u + 1} R) (S.immersion i)).obj F) ≅
        Scheme.proEtaleGeometricFixedModuleStalk y R
          ((ProEtale.upperStar (ModuleCat.{u + 1} R) (S.immersion i)).obj G) :=
      colim.mapIso (Functor.isoWhiskerLeft
        (Scheme.proEtaleGeometricNeighbourhoodForget y).op
          ((sheafToPresheaf _ _).mapIso d))
    let := hf Ω y
    exact Finite.of_equiv
      (Scheme.proEtaleGeometricFixedModuleStalk y R
        ((ProEtale.upperStar (ModuleCat.{u + 1} R) (S.immersion i)).obj G))
      (Equiv.ofBijective t.hom (ConcreteCategory.bijective_of_isIso t.hom)).symm

private theorem etaleConstructible_of_iso
    (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R] [Finite R]
    {K L : Etale.DerivedCategoryModule R X} (e : K ≅ L)
    (hL : Etale.DerivedCategory.isBoundedConstructible R X L) :
    Etale.DerivedCategory.isBoundedConstructible R X K := by
  obtain ⟨hc, a, b, hab, hz⟩ := hL
  refine ⟨fun q ↦ ?_, a, b, hab, fun q hq ↦
    (hz q hq).of_iso ((_root_.DerivedCategory.homologyFunctor _ q).mapIso e)⟩
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
  have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc q)
  exact Scheme.IsConstructibleSheaf.of_iso
    ((_root_.DerivedCategory.homologyFunctor _ q).mapIso e).symm

/-- A bounded flat constructible input model survives arbitrary finite coefficient
extension and exact etale/pro-etale comparison in the same interval.
Source: Stacks 0GL6, bounded finite-Tor input verification, with Tags 06YQ, 0G7E,
06YY, 03EL, 07A4, 0GKB, 03RZ and 08G1
(blueprint: lem-sp-finite-coefficient-input-models).

Proof plan:
1. Use lem-sf-etale-flat-constructible to choose P, flat and constructible termwise,
   zero outside [a,b], and representing L.
2. Its upper bound and flat terms imply K-flatness against arbitrary acyclic tests
   by lem-pc-bounded-above-flat-kflat-site (Stacks 06YQ).
3. Apply lem-weil-pbc-ringed-pullback-preserves-kflat to both coefficient maps and
   to site comparison. The three resulting complexes are K-flat with flat terms;
   additive pullback preserves their zero terms. Their derived identifications use
   lem-weil-pbc-ringed-topoi-derived-pullback and lem-sf-comparison-pullback-exact.
4. The termwise tensor maps of lem-weil-pbc-ringed-topoi-module-pullback-tensor,
   with the constant-module identification from lem-sfb-geometric-inverse-image-constant-module,
   give finiteInputTensorComparison. Naturality commutes with differentials. Its
   localization is the K-flat representative comparison specified by
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback.
5. On a constructible stratum, scalar extension of the finite local value M is
   B tensor_A M, finite since A and B are finite. Use the scalar clause of
   lem-pod-lisse-tensor-and-scalar-extension and the constant-module identification.
6. Apply thm-constructible-serre to the kernels and cokernels computing cohomology
   of the bounded scalar-extended complex, proving bounded constructibility of L_B.
7. Noetherian X is qcqs (lem-weil-pbc-locally-noetherian-quasi-separated). Apply
   sk-thm-pe-constructible-comparison and exactness to its cohomology. The same finite
   partitions work intrinsically: lem-weil-pbc-comparison-pullback restricts nu to
   each stratum, and etale trivializing covers are pro-etale covers. This treats
   both N_X L and, using Step 4, (N_X L)_B.
8. On each target ringed site, lem-sp-ringed-site-tor-flat-model applied to the
   displayed bounded flat model gives the identical Tor interval against every
   degree-zero module. No flatness or finite projective dimension of B over A
   was used. Empty strata, the zero ring, and the empty scheme are included. -/
theorem finiteCoefficientInputModels
    (X : Scheme.{u}) [IsNoetherian X]
    (ℓ : ℕ) (_hℓ : ℓ.Prime)
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (_hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (_hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0)
    (φ : A →+* B) (a b : ℤ) (_hab : a ≤ b) (L : Etale.DerivedCategoryModule A X)
    (_hL : Etale.DerivedCategory.isBoundedConstructible A X L)
    (_hTor : Etale.DerivedCategory.hasTorAmplitudeIn A X a b L) :
    ∃ P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
      (∀ q : ℤ, exactFunctor _ _ (tensorRight (P.X q))) ∧
      (∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf (P.X q)) ∧
      (∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q)) ∧
      @MorphismProperty.kFlat
        (CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) inferInstance
        (HomologicalComplex.monoidalCategory
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ))
        (HomologicalComplex.quasiIso (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ))
        P ∧
      Nonempty (L ≅ _root_.DerivedCategory.Q.obj P) ∧
      (∀ q : ℤ, exactFunctor _ _ (tensorRight ((finiteInputEtaleExtension φ X P).X q))) ∧
      (∀ q : ℤ, q < a ∨ b < q → IsZero ((finiteInputEtaleExtension φ X P).X q)) ∧
      @MorphismProperty.kFlat
        (CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ) inferInstance
        (HomologicalComplex.monoidalCategory
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) (.up ℤ))
        (HomologicalComplex.quasiIso (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) (.up ℤ))
        (finiteInputEtaleExtension φ X P) ∧
      Nonempty ((ProEtale.pbcFixedScalarExtension.{u} X.smallEtaleTopology φ).obj L ≅
        _root_.DerivedCategory.Q.obj (finiteInputEtaleExtension φ X P)) ∧
      (∀ q : ℤ, exactFunctor _ _ (tensorRight ((finiteInputComparison A X P).X q))) ∧
      (∀ q : ℤ, q < a ∨ b < q → IsZero ((finiteInputComparison A X P).X q)) ∧
      @MorphismProperty.kFlat
        (CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ℤ) inferInstance
        (HomologicalComplex.monoidalCategory
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) (.up ℤ))
        (HomologicalComplex.quasiIso
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) (.up ℤ))
        (finiteInputComparison A X P) ∧
      Nonempty (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory).obj L ≅
        _root_.DerivedCategory.Q.obj (finiteInputComparison A X P)) ∧
      (∀ q : ℤ, exactFunctor _ _ (tensorRight
        ((finiteInputProExtension φ X (finiteInputComparison A X P)).X q))) ∧
      (∀ q : ℤ, q < a ∨ b < q →
        IsZero ((finiteInputProExtension φ X (finiteInputComparison A X P)).X q)) ∧
      @MorphismProperty.kFlat
        (CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) ℤ) inferInstance
        (HomologicalComplex.monoidalCategory
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) (.up ℤ))
        (HomologicalComplex.quasiIso
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) (.up ℤ))
        (finiteInputProExtension φ X (finiteInputComparison A X P)) ∧
      Nonempty ((finiteInputProScalar φ X).obj
        (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory).obj L) ≅
          _root_.DerivedCategory.Q.obj
            (finiteInputProExtension φ X (finiteInputComparison A X P))) ∧
      Etale.DerivedCategory.isBoundedConstructible B X
        ((ProEtale.pbcFixedScalarExtension.{u} X.smallEtaleTopology φ).obj L) ∧
      Etale.DerivedCategory.hasTorAmplitudeIn B X a b
        ((ProEtale.pbcFixedScalarExtension.{u} X.smallEtaleTopology φ).obj L) ∧
      (∀ i : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf X A
        ((_root_.DerivedCategory.homologyFunctor
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) i).obj
          (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory).obj L))) ∧
      _root_.DerivedCategory.TStructure.t.{u + 1, u + 1, u + 2}.bounded
        (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory).obj L) ∧
      ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) X a b
        (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory).obj L) ∧
      (∀ i : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf X B
        ((_root_.DerivedCategory.homologyFunctor
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) i).obj
          ((finiteInputProScalar φ X).obj
            (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory).obj L)))) ∧
      _root_.DerivedCategory.TStructure.t.{u + 1, u + 1, u + 2}.bounded
        ((finiteInputProScalar φ X).obj
          (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory).obj L)) ∧
      ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} B) X a b
        ((finiteInputProScalar φ X).obj
          (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory).obj L)) := by
  obtain ⟨P, hf, hc, hz, ⟨e⟩⟩ :=
    (Etale.hasTorAmplitudeIn_iff_exists_finiteValueConstructibleModel
      A X a b _hab L _hL).1 _hTor
  have hf' : ∀ q : ℤ, exactFunctor _ _ (tensorRight (P.X q)) := fun q ↦ (hf q).2
  obtain ⟨hP, hE, hN, hNE, _, hrepE, hrepNE, _⟩ :=
    ProEtale.BoundedFlatCoefficientSiteSquare.boundedFlatCoefficientSiteSquare
      X φ a b _hab P hf' hz
  let := hrepE
  let := hrepNE
  let eE : (ProEtale.pbcFixedScalarExtension X.smallEtaleTopology φ).obj L ≅
      _root_.DerivedCategory.Q.obj (finiteInputEtaleExtension φ X P) :=
    (ProEtale.pbcFixedScalarExtension X.smallEtaleTopology φ).mapIso e.symm ≪≫
      asIso (Etale.scalarExtensionRepresentative φ X P)
  let eN : ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory).obj L ≅
      _root_.DerivedCategory.Q.obj (finiteInputComparison A X P) :=
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.mapIso e.symm ≪≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryFactors.app P
  let eNE : (finiteInputProScalar φ X).obj
      (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory).obj L) ≅
      _root_.DerivedCategory.Q.obj
        (finiteInputProExtension φ X (finiteInputComparison A X P)) :=
    (finiteInputProScalar φ X).mapIso eN ≪≫
      asIso (ProEtale.SupportedEtaleTensorOrigin.proScalarExtensionRepresentative φ X
        (finiteInputComparison A X P))
  obtain ⟨_, _, _, hCE, _, hCN, hZN, _⟩ :=
    constructibleCoefficientSiteSquare X A B φ a b _hab P hz hc
  let eNB := eNE ≪≫ finiteInputDerivedTensorComparison φ X P
  refine ⟨P, hf', hc, hz, hP.1.2.2, ⟨e.symm⟩,
    hE.1.1, hE.1.2.1, hE.1.2.2, ⟨eE⟩,
    hN.1.1, hN.1.2.1, hN.1.2.2, ⟨eN⟩,
    hNE.1.1, hNE.1.2.1, hNE.1.2.2, ⟨eNE⟩,
    etaleConstructible_of_iso X B eE hCE, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro M q hq
    exact (hE.2 M q hq).of_iso
      ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
        (((Etale.derivedTensor (ModuleCat.{u + 1} B) X).mapIso eE).app
          ((_root_.DerivedCategory.singleFunctor _ 0).obj M)))
  · intro q
    exact proConstructible_of_iso X A
      ((_root_.DerivedCategory.homologyFunctor _ q).mapIso eN) (hCN q).1
  · exact ⟨⟨a, (_root_.DerivedCategory.isGE_iff _ a).2
      (fun q hq ↦ ((hZN q (Or.inl hq)).1).of_iso
        ((_root_.DerivedCategory.homologyFunctor _ q).mapIso eN))⟩,
      ⟨b, (_root_.DerivedCategory.isLE_iff _ b).2
      (fun q hq ↦ ((hZN q (Or.inr hq)).1).of_iso
        ((_root_.DerivedCategory.homologyFunctor _ q).mapIso eN))⟩⟩
  · exact (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso eN.symm hN.2.2
  · intro q
    exact proConstructible_of_iso X B
      ((_root_.DerivedCategory.homologyFunctor _ q).mapIso eNB) (hCN q).2
  · exact ⟨⟨a, (_root_.DerivedCategory.isGE_iff _ a).2
      (fun q hq ↦ ((hZN q (Or.inl hq)).2).of_iso
        ((_root_.DerivedCategory.homologyFunctor _ q).mapIso eNB))⟩,
      ⟨b, (_root_.DerivedCategory.isLE_iff _ b).2
      (fun q hq ↦ ((hZN q (Or.inr hq)).2).of_iso
        ((_root_.DerivedCategory.homologyFunctor _ q).mapIso eNB))⟩⟩
  · exact (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso eNE.symm hNE.2.2

end AlgebraicGeometry
