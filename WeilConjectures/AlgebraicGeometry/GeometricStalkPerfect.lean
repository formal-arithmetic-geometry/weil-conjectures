/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFiniteTorConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.PointedEtaleStalk
public import WeilConjectures.AlgebraicGeometry.CondensedCoefficientPoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.GeometricStalk
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.LocalRing.Module
import WeilConjectures.AlgebraicGeometry.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Algebra.Homology.FieldComplexCohomologySplitting
import WeilConjectures.AlgebraicGeometry.IntrinsicFiniteStalkComparison
import WeilConjectures.AlgebraicGeometry.ProEtalePullbackStalkCoherence
import WeilConjectures.AlgebraicGeometry.IntrinsicTorAmplitudeTransport
import WeilConjectures.AlgebraicGeometry.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.EtaleStalkTorTest
import WeilConjectures.AlgebraicGeometry.Z8GeometricFieldPoint
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison

/-! # Perfect geometric stalks at finite and condensed field coefficients

Source: current blueprint, sec-six-functors/sk-thm-sf-pf-proetale,
fix-lem-finite-tor-perfect.md and fix-lem-finite-tor-perfect.proof.md
(blueprint: fix-lem-finite-tor-perfect).

The finite clauses use constant finite coefficients on the two small sites.
The field clause uses the ordinary derived category over the pulled-back condensed
ring and the published direct evaluation at an algebraically closed point.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

private lemma boundedConstructible_of_isBoundedConstructible
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (K : Etale.DerivedCategoryModule A X) :
    Etale.DerivedCategory.isBoundedConstructible A X K →
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X K := by
  intro h
  rcases h with ⟨hc, a, b, hab, hz⟩
  refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun i ↦ ?_⟩
  · exact (DerivedCategory.isGE_iff K a).2 fun i hi ↦ hz i (.inl hi)
  · exact (DerivedCategory.isLE_iff K b).2 fun i hi ↦ hz i (.inr hi)
  · exact (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc i)

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

set_option maxHeartbeats 2000000 in
-- The intrinsic derived comparison unfolds both coefficient presentations.
/-- The finite-coefficient pro-etale stalk has a bounded finite-free representative.
Source: current blueprint fix-lem-finite-tor-perfect, finite-site assertion
(blueprint: fix-lem-finite-tor-perfect).

Proof: descend the intrinsically bounded constructible complex to an etale
complex using finiteRing_constructibleDerived_origin. The intrinsic Tor predicate
is invariant under the representing isomorphism, and the canonical coefficient
realization transports it to fixed-scalar Tor amplitude. Exact site comparison
reflects that interval to the etale origin. Test it at the geometric etale stalk
against every scalar module. Exact stalks identify cohomology with the finite
stalks of the constructible cohomology sheaves. The coefficient DVR quotient is
finite, hence Noetherian, and local; scalar perfectness therefore gives a bounded
finite-free model. Finally the natural intrinsic stalk comparison and ordinary
derived localization identify this model with the specified termwise stalk -/
theorem finiteTorConstructible_proEtale_stalk_finiteFree
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) (hn : 1 ≤ n) (y : Spec (.of Ω) ⟶ Y)
    (K : CochainComplex (SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj
          (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))))) ℤ)
    (hK : WeilConjectures.finiteTorConstructible l E n hn Y (DerivedCategory.Q.obj K)) :
    ∃ (P : CochainComplex
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) ℤ)
      (a b : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
        (P.X i) ∧ Module.Finite (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
        (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj
        ((Functor.mapHomologicalComplex
          (finiteCoefficientModuleStalkFunctor y (Padic.coefficientExtensionRing l E n))
          (ComplexShape.up ℤ)).obj K) ≅ DerivedCategory.Q.obj P) := by
  classical
  let : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  let hO := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (by
      unfold Padic.coefficientExtensionAbsoluteValue
      exact spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  let : IsLocalRing (Padic.coefficientExtensionIntegers l E) := hO.2.2.2.1
  have hm : (Padic.coefficientExtensionMaximalIdeal l E).IsMaximal := by
    unfold Padic.coefficientExtensionMaximalIdeal Padic.coefficientExtensionIntegers
    exact hO.2.2.2.2.1
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E := by
    unfold Padic.coefficientExtensionUniformizer Padic.coefficientExtensionMaximalIdeal
      Padic.coefficientExtensionIntegers
    exact hO.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hle : Padic.coefficientExtensionIdeal l E n ≤
      Padic.coefficientExtensionMaximalIdeal l E := by
    unfold Padic.coefficientExtensionIdeal
    rw [hgen]
    exact Ideal.pow_le_self (Nat.ne_of_gt hn)
  let : Nontrivial (Padic.coefficientExtensionRing l E n) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top hm.ne_top hle)
  let : IsLocalRing (Padic.coefficientExtensionRing l E n) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  let A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)
  let : IsLocalRing A := ULift.ringEquiv.symm.isLocalRing
  let B := Padic.coefficientExtensionRing l E n
  let H := finiteCoefficientModuleStalkFunctor y B
  let R := ProEtale.finiteCoefficientIntrinsicRealization Y B
  let C := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y
  let F := (pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} A)
  have hfinite : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules Y (proEtaleConstantRing Y B)) i).obj
        (DerivedCategory.Q.obj K))} := hK.1.1
  obtain ⟨c, hc⟩ := hfinite.bddBelow
  obtain ⟨d, hd⟩ := hfinite.bddAbove
  have hvan : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Y (proEtaleConstantRing Y B)) i).obj
          (DerivedCategory.Q.obj K)) := by
    refine ⟨min c d, max c d, min_le_max, fun i hi ↦ ?_⟩
    by_contra hz
    have hci := hc hz
    have hdi := hd hz
    rcases hi with hi | hi <;> omega
  obtain ⟨G, ⟨eG⟩⟩ :=
    ((finiteRing_constructibleDerived_origin Y B).2.2.1 (DerivedCategory.Q.obj K)).2
      ⟨hK.1.2, hvan⟩
  let eR : R.mapDerivedCategory.obj (C.mapDerivedCategory.obj G.obj) ≅
      DerivedCategory.Q.obj K :=
    ((Functor.mapDerivedCategoryCompIso C R).app G.obj).symm ≪≫ eG
  obtain ⟨a, b, ht⟩ := hK.2
  have hT : HasProEtaleTorAmplitude Y B
      (R.mapDerivedCategory.obj (C.mapDerivedCategory.obj G.obj)) a b := by
    refine ⟨ht.1, ?_⟩
    intro L P heL f hf hP M i hi
    exact ht.2 L P ⟨heL.some ≪≫ eR⟩ f hf hP M i hi
  have hEt : Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) Y a b G.obj :=
    ProEtale.DerivedCategory.torAmplitudeIn_of_mapDerivedCategory A
      ((ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
        B Y a b ht.1 (C.mapDerivedCategory.obj G.obj)).1 hT)
  have htest := (Etale.geometricStalk_torAmplitude_test A Y G.obj a b ht.1).1.1
    ((Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn
      (Λ := A) (X := Y) (a := a) (b := b) (K := G.obj)).2 hEt)
  have hScalar : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) a b
      (F.mapDerivedCategory.obj G.obj) := by
    intro M
    exact ⟨(DerivedCategory.isGE_iff _ a).2
        (fun i hi ↦ htest Ω y M i (Or.inl hi)),
      (DerivedCategory.isLE_iff _ b).2
        (fun i hi ↦ htest Ω y M i (Or.inr hi))⟩
  have hbc := boundedConstructible_of_isBoundedConstructible A Y G.obj G.property
  have hfin : ∀ i, Module.Finite A ((DerivedCategory.homologyFunctor
      (ModuleCat.{u + 1} A) i).obj (F.mapDerivedCategory.obj G.obj)) := by
    intro i
    have hfg := (IsConstructibleSheaf.isFiniteSheaf (hbc.2 i)).isFinitelyGenerated_sheafFiber
      Ω y
    have hfi : Module.Finite A
        (F.obj ((DerivedCategory.homologyFunctor _ i).obj G.obj)) :=
      (ModuleCat.isFinitelyGenerated_iff _).1 hfg
    exact (Module.Finite.equiv_iff
      ((F.mapDerivedCategoryHomologyFunctorIso i).app G.obj).toLinearEquiv).1 hfi
  have hp := DerivedCategory.isPerfect_of_finiteTorAmplitude
    (F.bounded_mapDerivedCategory_obj hbc.1) hfin ⟨a, b, hScalar⟩
  obtain ⟨P, a', b', ha, hb, hP, ⟨eP⟩⟩ := hp.exists_free
  let eS : (ProEtale.finiteCoefficientIntrinsicDerivedComparison Y B) ⋙
      H.mapDerivedCategory ≅ F.mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso (ProEtale.finiteCoefficientIntrinsicComparison Y B)
      H).symm ≪≫
      Functor.mapDerivedCategoryNatIso (exists_intrinsicFiniteCoefficientStalkComparison y B).some
  exact ⟨P, a', b', ha, hb, hP, ⟨(H.mapDerivedCategoryFactors.app K).symm ≪≫
    H.mapDerivedCategory.mapIso eG.symm ≪≫ eS.app G.obj ≪≫ eP⟩⟩

/-- The same finite-free conclusion holds on the small etale site.
Source: current blueprint fix-lem-finite-tor-perfect, small-etale clause
(blueprint: fix-lem-finite-tor-perfect).

Proof: the coefficient quotient `O_E/(π_E^n)` is finite, and it is local and
nontrivial because `(π_E^n) ⊆ (π_E)`, the maximal ideal of the DVR `O_E`
(lem-weil-l-adic-extension-integers-dvr). Convert the hypothesis
`finiteTorConstructibleEtale`: its bounded-constructibility component gives
`boundedConstructible` via lem-weil-pbc-constructible-etale-module-sheaf-comparison,
and its Tor bound `hasTorAmplitudeIn` is `torAmplitudeIn`. The finite-free model is
then the published small-etale geometric-stalk theorem
`AlgebraicGeometry.Etale.exists_free_geometricStalk`. -/
theorem finiteTorConstructible_etale_stalk_finiteFree
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) (hn : 1 ≤ n) (y : Spec (.of Ω) ⟶ Y)
    (K : Etale.DerivedCategoryModule
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) Y)
    (hK : WeilConjectures.finiteTorConstructibleEtale l E n hn Y K) :
    ∃ (P : CochainComplex
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) ℤ)
      (a b : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
        (P.X i) ∧ Module.Finite (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
        (P.X i)) ∧
      Nonempty ((Etale.rightDerivedGlobalSections
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))
        (Spec (.of Ω))).obj
          ((L(Etale.upperStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))
            y)).obj K) ≅ DerivedCategory.Q.obj P) := by
  let : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  let hO := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (by
      unfold Padic.coefficientExtensionAbsoluteValue
      exact spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  let : IsLocalRing (Padic.coefficientExtensionIntegers l E) := hO.2.2.2.1
  have hm : (Padic.coefficientExtensionMaximalIdeal l E).IsMaximal := by
    unfold Padic.coefficientExtensionMaximalIdeal Padic.coefficientExtensionIntegers
    exact hO.2.2.2.2.1
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E := by
    unfold Padic.coefficientExtensionUniformizer Padic.coefficientExtensionMaximalIdeal
      Padic.coefficientExtensionIntegers
    exact hO.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hle : Padic.coefficientExtensionIdeal l E n ≤
      Padic.coefficientExtensionMaximalIdeal l E := by
    unfold Padic.coefficientExtensionIdeal
    rw [hgen]
    exact Ideal.pow_le_self (Nat.ne_of_gt hn)
  let : Nontrivial (Padic.coefficientExtensionRing l E n) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top hm.ne_top hle)
  let : IsLocalRing (Padic.coefficientExtensionRing l E n) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  let A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)
  let : IsLocalRing A := ULift.ringEquiv.symm.isLocalRing
  have hK' : Etale.DerivedCategory.boundedConstructibleFiniteTor A Y K := by
    dsimp [WeilConjectures.finiteTorConstructibleEtale] at hK
    refine ⟨boundedConstructible_of_isBoundedConstructible A Y K hK.1, ?_⟩
    obtain ⟨a, b, hab, ht⟩ := hK.2
    exact ⟨a, b, (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn
      (Λ := A) (X := Y) (a := a) (b := b) (K := K)).1 ht⟩
  simpa [A] using Etale.exists_free_geometricStalk A y K hK'


end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.CondensedGeometricPoint

open Z8

private theorem field_scalar_model
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hfield : IsField (condensedScalarRing Λ))
    (C : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ)))
    (hC : scalarFiniteCohomology Λ C) :
    (∃ (P : CochainComplex (ModuleCat.{u + 1} (condensedScalarRing Λ)) ℤ)
      (a b : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free (condensedScalarRing Λ) (P.X i) ∧
        Module.Finite (condensedScalarRing Λ) (P.X i)) ∧
      Nonempty (C ≅ DerivedCategory.Q.obj P)) ∧
    DerivedCategory.IsPerfectRingComplex C := by
  let : Field (condensedScalarRing Λ) := hfield.toField
  obtain ⟨⟨P, a, b, _, _, ha, hb, hP, e⟩, hp⟩ :=
    (DerivedCategory.field_complex_cohomology_splitting (condensedScalarRing Λ)).2.2.2.1 C hC
  refine ⟨⟨P, a, b, ha, hb, fun i ↦ ?_, e⟩, hp⟩
  have := hP i
  exact ⟨inferInstance, inferInstance⟩

private theorem geometric_pullback_boundedConstructible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (hK : boundedConstructible (condensedRingObj Λ Y) K) :
    boundedConstructible (condensedRingObj Λ (Spec (.of Ω)))
      ((CondensedRing.upperStar Λ y).mapDerivedCategory.obj K) := by
  refine ⟨(CondensedRing.upperStar Λ y).bounded_mapDerivedCategory_obj hK.1, fun i ↦ ?_⟩
  exact constructible_of_iso
    (((CondensedRing.upperStar Λ y).mapDerivedCategoryHomologyFunctorIso i).app K)
    (CondensedRing.isConstructibleModuleObject_upperStar Λ y _ (hK.2 i))

set_option maxHeartbeats 2000000 in
-- The coefficient-point comparison expands several exact functor presentations.
/-- The direct geometric fibre at either condensed field coefficient is a bounded
complex of finite-dimensional scalar vector spaces, hence perfect.
Source: current blueprint fix-lem-finite-tor-perfect, condensed-field clause
(blueprint: fix-lem-finite-tor-perfect).

Proof: cartesian coefficients make geometric pullback exact. Pull back the finite
constructible stratification, and use sk-lem-coefficient-heart to obtain lisse
finite-rank cohomology on the point. A nonempty member of a trivializing cover has
a section by lem-fix-weakly-etale-algclosed-section, hence the sheaves are globally
finite free there. The condensed-point sections formula identifies the scalar
ring with the coefficient field. Exact evaluation gives bounded finite-dimensional
cohomology, as in def-weil-finite-coefficient-point. Split the quotient of cycles by
boundaries in every degree. The resulting zero-differential cohomology complex is
bounded finite-dimensional and maps quasi-isomorphically to the fibre. This uses
the actual algebraically closed coefficient field directly, without descent. -/
theorem finiteField_geometricStalk_finiteFree
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj.{u} E) Y)))
    (hK : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj.{u} E) Y) K) :
    scalarFiniteCohomology (Profinite.continuousMapRingObj.{u} E)
      ((fiber (Profinite.continuousMapRingObj.{u} E) Ω).obj
        ((CondensedRing.upperStar (Profinite.continuousMapRingObj.{u} E) y).mapDerivedCategory.obj
          K)) ∧
    (∃ (P : CochainComplex
      (ModuleCat.{u + 1} (condensedScalarRing (Profinite.continuousMapRingObj.{u} E))) ℤ)
      (a b : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free (condensedScalarRing (Profinite.continuousMapRingObj.{u} E)) (P.X i) ∧
        Module.Finite (condensedScalarRing (Profinite.continuousMapRingObj.{u} E)) (P.X i)) ∧
      Nonempty ((fiber (Profinite.continuousMapRingObj.{u} E) Ω).obj
        ((CondensedRing.upperStar (Profinite.continuousMapRingObj.{u} E) y).mapDerivedCategory.obj
          K) ≅
          DerivedCategory.Q.obj P)) ∧
    DerivedCategory.IsPerfectRingComplex
      ((fiber (Profinite.continuousMapRingObj.{u} E) Ω).obj
        ((CondensedRing.upperStar (Profinite.continuousMapRingObj.{u} E) y).mapDerivedCategory.obj
          K)) := by
  let Λ := Profinite.continuousMapRingObj.{u} E
  obtain ⟨hfield, hp⟩ :=
    Z8.continuousField_direct_coefficient_point E Ω
  obtain ⟨_, _, _, _, _, _, _, _, hF, _⟩ := hp
  have hbc := geometric_pullback_boundedConstructible Λ y K hK
  have hcmp := (adicConstructibilityPredicateComparison ℓ (Spec (.of Ω)) Λ
    (.continuous E)).2
  have hC := hF ⟨(CondensedRing.upperStar Λ y).mapDerivedCategory.obj K, hcmp ▸ hbc⟩
  exact ⟨hC, field_scalar_model Λ hfield _ hC⟩

set_option maxHeartbeats 2000000 in
-- The coefficient-point comparison expands several exact functor presentations.
/-- The same direct condensed geometric-fibre assertion for the algebraic closure.
Source: current blueprint fix-lem-finite-tor-perfect, final field clause
(blueprint: fix-lem-finite-tor-perfect).

Proof: exact cartesian pullback and finite-rank lisse strata give bounded
constructible cohomology on Spec Ω. Split a nonempty trivializing pro-etale cover
using lem-fix-weakly-etale-algclosed-section. The direct coefficient-point sections
formula and exact evaluation give finite-dimensional scalar cohomology. Split
cycles and boundaries over the actual algebraically closed scalar field; the
finite cohomology complex is a bounded finite-free representative, hence perfect.
No common-stage object, rationalization or descent to a finite field is used. -/
theorem padicAlgCl_geometricStalk_finiteFree
    (ℓ : ℕ) [Fact ℓ.Prime]
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) Y)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) Y) K) :
    scalarFiniteCohomology (Profinite.padicAlgClRingObj.{u} ℓ)
      ((fiber (Profinite.padicAlgClRingObj.{u} ℓ) Ω).obj
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj.{u} ℓ) y).mapDerivedCategory.obj
          K)) ∧
    (∃ (P : CochainComplex
      (ModuleCat.{u + 1} (condensedScalarRing (Profinite.padicAlgClRingObj.{u} ℓ))) ℤ)
      (a b : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free (condensedScalarRing (Profinite.padicAlgClRingObj.{u} ℓ)) (P.X i) ∧
        Module.Finite (condensedScalarRing (Profinite.padicAlgClRingObj.{u} ℓ)) (P.X i)) ∧
      Nonempty ((fiber (Profinite.padicAlgClRingObj.{u} ℓ) Ω).obj
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj.{u} ℓ) y).mapDerivedCategory.obj
          K) ≅
          DerivedCategory.Q.obj P)) ∧
    DerivedCategory.IsPerfectRingComplex
      ((fiber (Profinite.padicAlgClRingObj.{u} ℓ) Ω).obj
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj.{u} ℓ) y).mapDerivedCategory.obj
          K)) := by
  let Λ := Profinite.padicAlgClRingObj.{u} ℓ
  obtain ⟨hfield, hp⟩ :=
    Z8.padicAlgCl_direct_coefficient_point ℓ Ω
  obtain ⟨_, _, _, _, _, _, _, _, hF, _⟩ := hp
  have hbc := geometric_pullback_boundedConstructible Λ y K hK
  have hcmp := (adicConstructibilityPredicateComparison ℓ (Spec (.of Ω)) Λ
    .algebraicClosure).2
  have hC := hF ⟨(CondensedRing.upperStar Λ y).mapDerivedCategory.obj K, hcmp ▸ hbc⟩
  exact ⟨hC, field_scalar_model Λ hfield _ hC⟩

end AlgebraicGeometry.ProEtale.CondensedGeometricPoint
