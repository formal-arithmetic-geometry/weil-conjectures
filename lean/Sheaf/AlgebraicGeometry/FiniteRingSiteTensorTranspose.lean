/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTransposeData
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.FiniteComparisonLocalizing
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import Sheaf.Paper.LocalizingExceptionalAdjoint
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Sheaf.AlgebraicGeometry.ProperProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import Sheaf.Paper.FiniteComparisonFaithful
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.Algebra.ZMod
import Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleGeneration
import Sheaf.AlgebraicGeometry.FiniteRingTensorTransposeAssembly
import Sheaf.AlgebraicGeometry.FiniteRingProjectionSquare
import Sheaf.AlgebraicGeometry.FiniteRingTensorCoherence

/-!
# Finite-ring transport of projection maps and integration transposes

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-smooth-purity/
sk-thm-smooth-purity-general-ring.proof.md, Proof (3), and
lem-pur-finite-ring-site-tensor-transpose, assertions 1--3
(blueprint: lem-pur-finite-ring-site-tensor-transpose).

All categories below are ordinary unbounded categories with constant finite coefficients.
The pro-etale closure is the recorded closure transported by the finite-discrete ring
identification. The auxiliary abbreviations expose the specified functors and canonical maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u uA v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem finiteEtaleClosure_all
    (B : Type) [CommRing B] [Finite B]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ℓ ≠ D.p) (hB : ∃ n : ℕ, (ℓ : B) ^ n = 0)
    (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))]
    (K : Etale.DerivedCategoryModule (ULift.{u + 1} B) T) :
    finiteComparisonEtaleClosure B T K := by
  have hnil : ∃ n : ℕ, (ℓ : ULift.{u + 1} B) ^ n = 0 := by
    obtain ⟨n, hn⟩ := hB
    refine ⟨n, (ULift.ringEquiv : ULift.{u + 1} B ≃+* B).injective ?_⟩
    simpa only [map_pow, map_natCast, map_zero] using hn
  intro P hP hgen
  let := hP.1
  let := hP.2.1
  have hsumsBig (I : Type (u + 2)) : P.IsClosedUnderColimitsOfShape (Discrete I) := by
    constructor
    rintro L ⟨hL⟩
    let : HasColimit hL.diag := ⟨_, hL.isColimit⟩
    exact P.prop_of_iso ((colimit.isColimit hL.diag).coconePointUniqueUpToIso hL.isColimit)
      (hP.2.2 hL.diag inferInstance (fun i ↦ hL.prop_diag_obj (Discrete.mk i)))
  have hsums (I : Type (u + 1)) : P.IsClosedUnderColimitsOfShape (Discrete I) := by
    exact (P.isClosedUnderColimitsOfShape_iff_of_equivalence
      (Discrete.equivalence (Equiv.ulift : ULift.{u + 2} I ≃ I))).1 (hsumsBig _)
  have hall := Etale.finiteTorConstructible_etale_localizing_eq_top
    D ℓ (Fact.out) hℓ T (ULift.{u + 1} B) hnil
  have hK : (sInf {Q : ObjectProperty (Etale.DerivedCategoryModule (ULift.{u + 1} B) T) |
      (∀ L, Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} B) T L →
        (∃ a b : ℤ, a ≤ b ∧
          Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} B) T a b L) → Q L) ∧
      Q.IsClosedUnderIsomorphisms ∧ Q.IsTriangulated ∧
      ∀ I : Type (u + 1), Nonempty (Q.IsClosedUnderColimitsOfShape (Discrete I))}) K := by
    rw [hall]
    trivial
  apply (sInf_le ?_ : _ ≤ P) K hK
  refine ⟨?_, inferInstance, inferInstance, fun I ↦ ⟨hsums I⟩⟩
  intro L hbc htor
  apply hgen L
  obtain ⟨a, b, _, ht⟩ := htor
  exact ⟨hbc, a, b, Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 ht⟩

variable (B : Type) [CommRing B] [Finite B] [TopologicalSpace B]
  [DiscreteTopology B] [IsTopologicalRing B]
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
    ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
      Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom]

/-- Transport of the compact-support projection maps and integration transposes for
arbitrary finite primary rings. Right adjoints and their adjunctions are arbitrary choices
of the adjoints specified in the statement. Membership proofs only type the restrictions.
The isomorphisms `b`, `pe`, `pp` are pinned to the named canonical maps by their hom equations.

Source: blueprint main-20261015, sk-thm-smooth-purity-general-ring.proof.md, Proof (3),
and the full statement of lem-pur-finite-ring-site-tensor-transpose
(blueprint: lem-pur-finite-ring-site-tensor-transpose).

Proof:
1. Apply the existing finite-Tor constructible etale generation theorem. Transport
   coproduct size along a discrete-category equivalence and identify its Tor-amplitude
   predicate with the generator predicate to put every object in the etale closure.
2. Use the finite comparison equivalence on closures and ordinary full faithfulness.
   Repleteness identifies the ambient essential image with the pro-etale closure.
   This applies separately to X and Y. The compact-support comparison is invertible
   by the same finite comparison theorem; proper-mate and open-comparison naturality
   assemble its specified components into a natural isomorphism.
3. The finite-coefficient unbounded proper projection formula, together with the
   canonical open and pullback isomorphisms, makes the etale projection invertible.
4. Apply finiteRingProjectionSquare and finiteRingTensorCoherence. Their remaining
   proofs are the canonical-map calculations in original steps 5--9 and 11.
5. finiteRingTensorTransposeAssembly transports arbitrary chosen adjunctions across
   the image equivalences, proves uniqueness from the counit equation, obtains pro
   projection invertibility from the square, and computes both integration transposes.
   These categorical arguments are proved separately without geometric assumptions. -/
theorem finiteRingSiteTensorTranspose
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ℓ ≠ D.p) (hB : ∃ n : ℕ, (ℓ : B) ^ n = 0)
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] (c : Compactification f)
    [c.Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (c.Z ↘ Spec (.of D.k))] [QuasiCompact (c.Z ↘ Spec (.of D.k))]
    [IsSeparated (c.Z ↘ Spec (.of D.k))]
    [c.i.IsOver (Spec (.of D.k))] [c.g.IsOver (Spec (.of D.k))] :
    finiteRingSiteTensorTransposeWithCoefficients
      (ModuleCat.{u + 1} (ULift.{u + 1} B)) c
      (finiteComparisonProEtaleClosure B eR X) (finiteComparisonProEtaleClosure B eR Y)
      (finiteComparisonCompactSupportMap B c.i c.g)
      (unboundedDirectImagePullbackIso (ULift.{u + 1} B) f) := by
  classical
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card, D.card_base, D.cardinality_eq])
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let : Algebra (ZMod D.p) D.k₀ := ZMod.algebra _ _
  let : Algebra (ZMod D.p) D.k := ZMod.algebra _ _
  let : IsScalarTower (ZMod D.p) D.k₀ D.k := inferInstance
  let : Algebra.IsAlgebraic (ZMod D.p) D.k := Algebra.IsAlgebraic.trans _ D.k₀ _
  let : IsAlgClosure (ZMod D.p) D.k := ⟨inferInstance, inferInstance⟩
  have hunit : IsUnit (ℓ : D.k) :=
    isUnit_iff_ne_zero.mpr (CharP.cast_ne_zero_of_ne_of_prime D.k (Fact.out) hℓ.symm)
  have hnil : ∃ n : ℕ, (ℓ : ULift.{u + 1} B) ^ n = 0 := by
    obtain ⟨n, hn⟩ := hB
    refine ⟨n, (ULift.ringEquiv : ULift.{u + 1} B ≃+* B).injective ?_⟩
    simpa only [map_pow, map_natCast, map_zero] using hn
  let A := ModuleCat.{u + 1} (ULift.{u + 1} B)
  have hcomp (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
      [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
      [QuasiCompact (T ↘ Spec (.of D.k))] :
      ∀ N, (comparisonUpperStar A T).mapDerivedCategory.essImage N ↔
        finiteComparisonProEtaleClosure B eR T N := by
    intro N
    obtain ⟨hp, heq, _⟩ := finiteComparisonLocalizing B eR D.p D.k ℓ hℓ hB T
    let F := (finiteComparisonProEtaleClosure B eR T).lift
      ((finiteComparisonEtaleClosure B T).ι ⋙
        (comparisonUpperStar A T).mapDerivedCategory)
      (fun M ↦ hp M.obj M.property)
    let := heq
    constructor
    · rintro ⟨M, ⟨e⟩⟩
      have hloc : (finiteComparisonProEtaleClosure B eR T).IsClosedUnderIsomorphisms := by
        constructor
        intro U V i hU P hP hgen
        let := hP.2.1
        exact P.prop_of_iso i (hU P hP hgen)
      let := hloc
      exact ObjectProperty.prop_of_iso _ e (hp M (finiteEtaleClosure_all B D ℓ hℓ hB T M))
    · intro hN
      let N' : (finiteComparisonProEtaleClosure B eR T).FullSubcategory := ⟨N, hN⟩
      exact ⟨(F.objPreimage N').obj, ⟨(ObjectProperty.ι _).mapIso
        (F.objObjPreimageIso N')⟩⟩
  obtain ⟨hffX⟩ := finiteComparisonOrdinary_fullyFaithful (ULift.{u + 1} B) D.k
    (Or.inr inferInstance) (by simpa using hunit) hnil X
  obtain ⟨hffY⟩ := finiteComparisonOrdinary_fullyFaithful (ULift.{u + 1} B) D.k
    (Or.inr inferInstance) (by simpa using hunit) hnil Y
  let := hffX.full
  let := hffX.faithful
  let := hffY.full
  let := hffY.faithful
  have hi (M : Etale.DerivedCategoryModule (ULift.{u + 1} B) X) :
      IsIso (finiteComparisonCompactSupportMap B c.i c.g M) := by
    obtain ⟨_, _, _, _, _, _, hcs⟩ := finiteComparisonLocalizing B eR D.p D.k ℓ hℓ hB X
    exact hcs c.Z Y c.i c.g M (finiteEtaleClosure_all B D ℓ hℓ hB X M)
  let b : Etale.rightDerivedLowerShriekOfCompactification A c ⋙
      (comparisonUpperStar A Y).mapDerivedCategory ≅
      (comparisonUpperStar A X).mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification A c :=
    NatIso.ofComponents (fun M ↦ asIso (finiteComparisonCompactSupportMap B c.i c.g M)) (by
      intro M N v
      change _ ≫ (finiteComparisonCompactSupportMap B c.i c.g N) =
        finiteComparisonCompactSupportMap B c.i c.g M ≫ _
      unfold finiteComparisonCompactSupportMap
      dsimp only [Etale.rightDerivedLowerShriekOfCompactification,
        rightDerivedLowerShriekOfCompactification, Functor.comp_map]
      rw [← Category.assoc, unboundedDirectImageComparisonMap_naturality]
      simp only [Category.assoc]
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      exact congrArg
        ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) c.g).rightDerivedFunctor.map)
        ((finiteComparisonOpenIso B c.i).hom.naturality v))
  let : BraidedCategory (DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
    DerivedCategory.braidedCategory' _
  let : BraidedCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :=
    DerivedCategory.braidedCategory' _
  unfold finiteRingSiteTensorTransposeWithCoefficients
    finiteRingSiteTensorTransposeCanonicalSymmetry finiteRingSiteTensorTransposeCanonicalTensor
    finiteRingSiteTensorTransposeSiteFunctors
  have h := finiteRingTensorTransposeAssembly
    (comparisonUpperStar A X).mapDerivedCategory (comparisonUpperStar A Y).mapDerivedCategory
    (Etale.rightDerivedLowerShriekOfCompactification A c)
    (rightDerivedLowerShriekOfCompactification A c)
    (Etale.upperStar A f).leftDerivedFunctor (upperStar A f).leftDerivedFunctor
    (finiteComparisonProEtaleClosure B eR X) (finiteComparisonProEtaleClosure B eR Y)
    (fun M ↦ (hcomp X _).1 ⟨M, ⟨Iso.refl _⟩⟩)
    (fun M ↦ (hcomp Y _).1 ⟨M, ⟨Iso.refl _⟩⟩) (hcomp X) (hcomp Y) b
    (finiteRingSiteTensor A X) (finiteRingSiteTensor A Y) (finiteRingSiteUnit A Y)
    (finiteRingSitePullback A f (unboundedDirectImagePullbackIso (ULift.{u + 1} B) f))
    (finiteRingEtalePF A c) (finiteRingProPF A c)
    (fun M K ↦ by
      have := Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite (ULift.{u + 1} B) c.g
      unfold finiteRingEtalePF
      rw [Etale.projectionMapOfCompactification_app_app]
      infer_instance)
    (finiteRingProjectionSquare B c)
    (finiteRingTensorCoherence B Y).1 (finiteRingTensorCoherence B X).2
  exact h

end AlgebraicGeometry.ProEtale
