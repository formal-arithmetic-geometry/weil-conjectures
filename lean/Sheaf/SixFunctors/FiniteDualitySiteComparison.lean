/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q63
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.FiniteTorAmplitudeProEtaleModule
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.Paper.DualityPairing
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage
public import Sheaf.AlgebraicGeometry.EvaluationHomSiteComparison

import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import WeilConjectures.Algebra.Homology.HomComplex
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
import Sheaf.AlgebraicGeometry.ProEtaleStalkConservative
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import WeilConjectures.Algebra.Homology.HomTensorTotal
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.Paper.FiniteFreeHomComparison
import Sheaf.Paper.SfHomTriangulated
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.ProEtaleLisseOrigin
import Sheaf.SixFunctors.EtaleLocallyClosedExtensionComparison
import Sheaf.CategoryTheory.DerivedCategory.BoundedFiniteTorPerfect
import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.Paper.StratumAmbientHom
import Sheaf.Paper.WeilVerdierPreservationStrata
import WeilConjectures.SixFunctors.Finite.Exact
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import Sheaf.AlgebraicGeometry.EtaleOriginAdjointClass
import Sheaf.Paper.EtaleGeometricBiduality
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.FiniteDualityLocallyClosedComparison
import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
import Sheaf.Paper.SfPreservationClass
import Sheaf.SixFunctors.FiniteDualityClosedComparison

/-! # Finite-stage duality under the site comparison

Source: Weil conjectures blueprint, sec-six-functors/sk-prop-sf-rf-shriek-preservation,
lem-weil-finite-duality-site-comparison, order 2084
(blueprint: lem-weil-finite-duality-site-comparison).

The comparison is the evaluation-defined arrow. The dualizing object on the
pro-etale site is the transported etale exceptional functor applied to the unit.
The equations below specify preservation of evaluation and its transpose.
-/

@[expose] public section
set_option autoImplicit false
universe u v w c d
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry

namespace CategoryTheory

/-- Transport a specified degree-zero map through an exact functor and specified
identifications of the degree-zero source and target. This packages only composition
of the existing canonical comparisons.
Source: blueprint order 2084, proof step 9
(blueprint: lem-weil-finite-duality-site-comparison). -/
noncomputable def finiteDualitySingleTransport
    {C : Type c} [Category.{v} C] [Abelian C] [HasDerivedCategory.{v} C]
    {D : Type d} [Category.{w} D] [Abelian D] [HasDerivedCategory.{w} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {V : C} {V' : D} (ε : F.obj V ⟶ V')
    {U : DerivedCategory C} {U' : DerivedCategory D}
    (i : (DerivedCategory.singleFunctor C 0).obj V ≅ U)
    (j : (DerivedCategory.singleFunctor D 0).obj V' ≅ U') :
    F.mapDerivedCategory.obj U ⟶ U' :=
  F.mapDerivedCategory.map i.inv ≫
    (F.mapDerivedCategorySingleFunctor 0).hom.app V ≫
    (DerivedCategory.singleFunctor D 0).map ε ≫ j.hom

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- The canonical map from the etale constant unit to the derived direct image of the
pro-etale constant unit: the comparison adjunction unit followed by constant transport.
Source: blueprint order 2084, proof step 9
(blueprint: lem-weil-finite-duality-site-comparison). -/
noncomputable def finiteDualityBaseUnit
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] (S : Scheme.{u})
    (ε : (comparisonUpperStar A S).obj (𝟙_ _) ⟶ 𝟙_ _) :
    (𝟙_ (DerivedCategory (Sheaf S.smallEtaleTopology A))) ⟶
      (comparisonLowerStar A S).rightDerivedFunctor.obj (𝟙_ _) :=
  (derivedComparisonAdjunction A S).unit.app (𝟙_ _) ≫
    (comparisonLowerStar A S).rightDerivedFunctor.map
      (finiteDualitySingleTransport (comparisonUpperStar A S) ε
        (DerivedCategory.singleFunctorObjUnitIso _)
        (DerivedCategory.singleFunctorObjUnitIso _))

/-- The ordinary etale dualizing object using the specified compactification.
This instantiates the existing ambient compact-support right adjoint; no adjoint
hypothesis on the pro-etale category is introduced.
Source: blueprint order 2084, definition of omega_et
(blueprint: lem-weil-finite-duality-site-comparison). -/
noncomputable def finiteDualityEtaleObject
    (A : Type u) [CommRing A] [Finite A]
    {X S : Scheme.{u}} {a : X ⟶ S} (c : Compactification a) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :=
  letI := c.hasCompactification
  Etale.dualizingComplex (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) a

/-- The pro-etale dualizing object is the recorded comparison-transport exceptional
inverse image applied to the pro-etale constant unit.
Source: blueprint order 2084, definition of omega_proet
(blueprint: lem-weil-finite-duality-site-comparison). -/
noncomputable def finiteDualityProEtaleObject
    (A : Type u) [CommRing A] [Finite A]
    {X S : Scheme.{u}} {a : X ⟶ S} (c : Compactification a) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :=
  (sfFiniteExceptionalFixed A c).obj (𝟙_ _)

/-- The canonical dualizing-object arrow: apply the etale exceptional inverse image
and then comparison pullback to the comparison adjunction unit at the base constant unit.
This formula supplies the global overlap normalization of the dualizing comparison.
Source: blueprint order 2084, proof step 9
(blueprint: lem-weil-finite-duality-site-comparison). -/
noncomputable def finiteDualityObjectMap
    (A : Type u) [CommRing A] [Finite A]
    {X S : Scheme.{u}} {a : X ⟶ S} (c : Compactification a) :
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory.obj
        (finiteDualityEtaleObject A c) ⟶ finiteDualityProEtaleObject A c :=
  letI := c.hasCompactification
  (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory.map
    ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) a).map
      (finiteDualityBaseUnit (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) S
        (comparisonUpperStarUnitIso (ULift.{u + 1, u} A) S).hom))

/-- The normalized ambient pairings from lem-weil-duality-pairing, with the explicit
Hom-comparison, identify evaluation and its transpose on a given etale input.
Source: blueprint order 2084, final paragraph
(blueprint: lem-weil-finite-duality-site-comparison). -/
noncomputable def FiniteDualityCompatibility
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(comparisonUpperStar A X).PreservesFlat]
    (W : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (W' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (ω : (comparisonUpperStar A X).mapDerivedCategory.obj W ≅ W')
    (hEt : Etale.AmbientDualityPairing A X W)
    (hPro : AmbientDualityPairing A X W')
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) : Prop :=
  let F := (comparisonUpperStar A X).mapDerivedCategory
  let HC := Etale.derivedHom A X
  let HD := derivedHom A X
  ∃ cK : F.obj ((HC.obj (op K)).obj W) ≅ (HD.obj (op (F.obj K))).obj W',
    cK.hom = siteComparisonEvaluationHom A X K W ≫
      (HD.obj (op (F.obj K))).map ω.hom ∧
    ∃ cDK : F.obj ((HC.obj (op ((HC.obj (op K)).obj W))).obj W) ≅
        (HD.obj (op (F.obj ((HC.obj (op K)).obj W)))).obj W',
      cDK.hom = siteComparisonEvaluationHom A X ((HC.obj (op K)).obj W) W ≫
        (HD.obj (op (F.obj ((HC.obj (op K)).obj W)))).map ω.hom ∧
      ((derivedTensor A X).map cK.hom).app (F.obj K) ≫
          hPro.choose_spec.2.choose (F.obj K) =
        (siteComparisonTensorIso A X ((HC.obj (op K)).obj W)).inv.app K ≫
          F.map (hEt.choose_spec.2.choose K) ≫ ω.hom ∧
      F.map (Etale.AmbientDualityPairing.bidualityMap A X hEt K) ≫
          cDK.hom ≫ (HD.map cK.inv.op).app W' =
        AmbientDualityPairing.bidualityMap A X hPro (F.obj K)

/-- The site-comparison and Verdier-duality assertions for the supplied, fixed ambient
objects and constructibility predicates. All comparison arrows and normalized pairings
are the recorded ones; the coefficient specialization fixes every parameter below.
Source: blueprint order 2084, final paragraph
(blueprint: lem-weil-finite-duality-site-comparison). -/
noncomputable def FiniteDualityComparisonData
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(comparisonUpperStar A X).PreservesFlat]
    (W : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (W' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (w : (comparisonUpperStar A X).mapDerivedCategory.obj W ⟶ W')
    (Pet Qet : ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology A)))
    (Ppro : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))) : Prop :=
  (∀ K M : DerivedCategory (Sheaf X.smallEtaleTopology A),
    Pet K → Qet M → IsIso (siteComparisonEvaluationHom A X K M)) ∧
  ∃ ω : (comparisonUpperStar A X).mapDerivedCategory.obj W ≅ W',
    ω.hom = w ∧
    ∃ hEt : Etale.AmbientDualityPairing A X W,
    ∃ hPro : AmbientDualityPairing A X W',
      (∀ K : DerivedCategory (Sheaf X.smallEtaleTopology A), Pet K →
        FiniteDualityCompatibility A X W W' ω hEt hPro K) ∧
      (∃ e : Pet.FullSubcategory ≌ Ppro.FullSubcategory,
        Nonempty (e.functor ⋙ Ppro.ι ≅
          Pet.ι ⋙ (comparisonUpperStar A X).mapDerivedCategory)) ∧
      (∃ d : Ppro.FullSubcategoryᵒᵖ ≌ Ppro.FullSubcategory,
        Nonempty (d.functor ⋙ Ppro.ι ≅ Ppro.ι.op ⋙ (derivedHom A X).flip.obj W')) ∧
      ∀ K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A),
        Ppro K → IsIso (AmbientDualityPairing.bidualityMap A X hPro K)

end AlgebraicGeometry.ProEtale

namespace WeilConjectures

/-- The finite-stage comparison conclusion. Each abbreviation inside this definition
is the existing canonical object or functor. In particular the two dualizing objects
are fixed before the comparison isomorphism is quantified. Its hom is prescribed by
the base adjunction unit, and the Hom comparison is prescribed by evaluation.
The last clauses record the induced equivalence of finite-Tor constructible categories,
the anti-equivalence with the specified Verdier functor, and its canonical biduality map.
Source: blueprint order 2084 (blueprint: lem-weil-finite-duality-site-comparison). -/
noncomputable def FiniteDualitySiteComparison
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] : Prop :=
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  let A := Padic.coefficientExtensionRing l E n
  let Λ := ULift.{u + 1, u} A
  letI : Finite Λ := inferInstance
  letI : IsNoetherianRing Λ := isNoetherian_of_finite Λ Λ
  letI : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).PreservesFlat :=
    ProEtale.preservesFlat_comparisonUpperStar (X := X)
  let c := NagataCompactification (X ↘ Spec (.of D.k))
  ProEtale.FiniteDualityComparisonData (ModuleCat.{u + 1} Λ) X
    (ProEtale.finiteDualityEtaleObject A c) (ProEtale.finiteDualityProEtaleObject A c)
    (ProEtale.finiteDualityObjectMap A c)
    (finiteTorConstructibleEtale l E n hn X)
    (Etale.DerivedCategory.isBoundedConstructible Λ X)
    (finiteTorConstructibleProEtaleModule l E n hn X)

/-- The canonical evaluation comparison is invertible for a finite-Tor constructible
first input and a bounded constructible second input. The canonical dualizing comparison
identifies evaluations and their double-dual transposes, and transports Verdier duality.
Source: blueprint sec-six-functors/sk-prop-sf-rf-shriek-preservation, order 2084
(blueprint: lem-weil-finite-duality-site-comparison).

Proof:
1. Exact comparison identifies constant rings and preserves tensor products. Resolve the
   tensor arguments by K-flat complexes and the target by a K-injective complex. The
   Hom-complex tensor-total adjunction descends to derived tensor-Hom adjunction. Define
   beta by transposing pullback of evaluation through this tensor comparison.
2. Apply lem-weil-finite-duality-closed-comparison to a closed immersion and bounded
   constructible M. It identifies the bounded-below exceptional restrictions and counits.
3. Factor a locally closed immersion into an open and a closed immersion. Apply
   lem-weil-finite-duality-locally-closed-comparison, retaining the same counit equation.
4. thm-sf-preservation-class makes the transported exceptional restriction constructible.
   By lem-sf-proetale-constructible-origin it has a bounded constructible etale origin.
   Full faithfulness on bounded-below complexes lifts the isomorphism and its inverse;
   hence the etale exceptional restriction itself is bounded constructible.
5. Use lem-trf-devissage-generation on the pro-etale side. Lisse descent, comparison of
   Tor intervals and extension by zero lift its finite-flat generators and their thick
   generation to the etale side. For a stratum factor s=g*j=v*c, closed direct image is
   exact and lem-sfb-etale-locally-closed-extension-comparison identifies g*j! with v!c*.
6. For fixed M, invertibility of beta is thick in K: Hom sends a cone to the shifted
   cone of the reversed Hom map. The comparison is a morphism of these triangles.
   Cohomology and the five lemma handle cones; naturality handles shifts and retracts.
7. On each stratum a finite flat module over the finite local ring A is finite free,
   by lem-weil-bounded-finite-tor-perfect. Apply lem-sf-hom-comparison-finite-free locally.
   K-injectives and Hom complexes restrict to slices, the weakly etale localization
   identifies these sites, and pro-etale covering conservativity detects the isomorphism.
8. lem-weil-stratum-ambient-hom expresses the generator comparison as direct-image
   comparison, the finite-free Hom comparison and exceptional restriction comparison.
   The internal Hom on the stratum is bounded below, so direct-image comparison applies.
   Uncurrying and the exceptional-counit equations identify this composite with beta;
   the direct-image comparison is the canonical mate. Every factor is invertible.
9. The pro-etale exceptional object is F a^times Rnu_* A. The constant-unit comparison
   and the bounded-below comparison adjunction unit give the specified omega isomorphism.
   lem-weil-verdier-preservation-strata shows that omega_et and the dual of K are
   finite-Tor constructible, so the Hom comparison applies again to the dual of K.
10. Compose beta at omega_et with Hom(FK,omega) to obtain c_K. Its evaluation equation
    is the defining adjunction equation. Apply the same construction to DK. Uncurrying
    F(delta_K), followed by c_DK and D'(c_K inverse), gives the same interchanged
    evaluation that defines delta'_FK; hence the transposes agree. Constructible origin
    and Tor comparison give the equivalence on the two full subcategories. The separate
    thm-weil-etale-geometric-biduality makes the canonical pro-etale transpose invertible
    and transports the etale anti-equivalence to the specified pro-etale dual functor.
-/
theorem finite_duality_site_comparison
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] :
    FiniteDualitySiteComparison D l hl E n hn X := by
  sorry

end WeilConjectures
