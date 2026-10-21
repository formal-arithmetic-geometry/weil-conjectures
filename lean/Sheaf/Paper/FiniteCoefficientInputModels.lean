/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.Paper.ComparisonPullbackExact
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.AlgebraicGeometry.RingedProEtaleTorAmplitudeOfUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Paper.WitnessCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtension
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import Mathlib.AlgebraicGeometry.Noetherian

import Sheaf.AlgebraicGeometry.EtaleFlatConstructibleModel
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Paper.RingedTopoiDerivedPullbackIndependent
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.SixFunctors.GeometricInverseImageConstantModule
import Sheaf.Paper.LisseTensorScalarExtension
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.Algebra.Homology.RingedSiteTorFlatModel

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
  sorry

end AlgebraicGeometry
