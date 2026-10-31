/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.Algebra.Homology.DerivedInternalHomMixedUniverses
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.EtaleTorAmplitude
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent

import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.VerdierPreservation
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel

/-! # Finite-coefficient Verdier preservation and its uniform Tor bound

Source: `WeilConjectures/SixFunctors/Etale/Derived/VerdierBiduality.lean`,
`constructibleFiniteTor_verdierDual` and `torAmplitudeIn_verdierDual`;
latest blueprint `lem-weil-verdier-preservation-strata.proof.md`, paragraphs 1--2,
and `prop-coef-integral-dualizing.proof.md`, paragraph 1
(blueprint: lem-route-finite-verdier-tor-bound).

All categories are ordinary small-etale module derived categories. The right adjoint
is presented by its adjunction to the compactification functor, so no choice of
compactification or right adjoint restricts the assertion. No new notion is defined.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

private theorem finiteVerdier_boundedConstructible_iff
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (K : DerivedCategoryModule A X) :
    DerivedCategory.isBoundedConstructible A X K ↔
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X K := by
  constructor
  · rintro ⟨hc, a, b, _, hz⟩
    refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun i ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc i)⟩
    · exact (_root_.DerivedCategory.isGE_iff K a).2 (fun i hi ↦ hz i (.inl hi))
    · exact (_root_.DerivedCategory.isLE_iff K b).2 (fun i hi ↦ hz i (.inr hi))
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨fun i ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc i),
      min a b, b, min_le_right _ _, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact (_root_.DerivedCategory.isGE_iff K a).1 ha i
        (hi.trans_le (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff K b).1 hb i hi

/-- Finite-coefficient Verdier duality preserves bounded constructible finite-Tor
complexes, takes the Tor interval `[a,b]` to `[-b-2d,-a]`, and places the dualizing
object in the interval `[-2d,0]`. Internal Hom from the constant unit identifies
its Verdier dual with that dualizing object.

Source: `VerdierBiduality.lean`, `constructibleFiniteTor_verdierDual` and
`torAmplitudeIn_verdierDual`; latest blueprint
`lem-weil-verdier-preservation-strata.proof.md`, paragraphs 1--2, and
`prop-coef-integral-dualizing.proof.md`, paragraph 1
(blueprint: lem-route-finite-verdier-tor-bound).

Proof:
1. The recorded predicate `isBoundedConstructible` agrees with the source predicate
   `boundedConstructible`: cohomology sheaves are compared by
   lem-weil-pbc-constructible-etale-module-sheaf-comparison, and the finite vanishing range is
   the pair of canonical t-structure bounds (`isGE_iff`, `isLE_iff`), a lower bound `a` being
   replaced by `min a b` to give an ordered range. Tor amplitude is compared by
   `hasTorAmplitudeIn_iff_torAmplitudeIn` (def-kun-tor-amplitude).
2. The compactification `c` gives `HasCompactification f`. Transport the source adjunction
   `Rf_! ⊣ Rf^!` along the compactification-independence isomorphism `Rf_!^c ≅ Rf_!`
   (lem-sf-unbounded-compact-support-proper-composition, thm-amb-etale-exceptional-adjoint);
   uniqueness of right adjoints gives `Rf^! ≅ F`, hence `dualizingComplex A f ≅ F(A)`.
3. For `dim X ≤ d` and `K` bounded constructible of Tor amplitude `[a,b]`, the proved source
   theorem `constructibleFiniteTor_and_torAmplitudeIn_verdierDual_of_perfectField`
   (an algebraically closed field is perfect; it implements the smooth-stratum argument of the
   latest blueprint lem-weil-verdier-preservation-strata) makes `RHom(K, dualizingComplex A f)`
   bounded constructible of Tor amplitude `[-b-2d,-a]`; transport along `RHom(K,-)` of step 2.
4. For the qualitative clause choose `a,b` from the hypothesis and `d` by
   lem-kun-dimension-finite-type, and apply step 3.
5. The constant complex is the tensor unit (lem-kun-tensor-unit): it is bounded constructible
   and, being dualizable hence flat, of Tor amplitude `[0,0]`. Step 3 at `a = b = 0` and the
   isomorphism `RHom(A_X, F(A)) ≅ F(A)` of internal Hom from the unit give that `F(A)` is
   bounded constructible of Tor amplitude `[-2d,0]`; that isomorphism is the last clause. -/
theorem finiteVerdier_preservation_and_torBound
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {k : Type u} [Field k] [IsAlgClosed k]
    [HasInvertibleExponent A (Spec (.of k))]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (F : DerivedCategoryModule A (Spec (.of k)) ⥤ DerivedCategoryModule A X)
    (_adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ F) :
    (∀ K : DerivedCategoryModule A X,
      DerivedCategory.isBoundedConstructible A X K →
      (∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A X a b K) →
      DerivedCategory.isBoundedConstructible A X
          (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj
            (F.obj (constantComplex A (Spec (.of k))))) ∧
        ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A X a b
          (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj
            (F.obj (constantComplex A (Spec (.of k)))))) ∧
    (∀ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞) →
      (∀ (a b : ℤ) (K : DerivedCategoryModule A X),
        DerivedCategory.isBoundedConstructible A X K →
        DerivedCategory.hasTorAmplitudeIn A X a b K →
        DerivedCategory.hasTorAmplitudeIn A X (-b - 2 * (d : ℤ)) (-a)
          (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj
            (F.obj (constantComplex A (Spec (.of k)))))) ∧
      DerivedCategory.isBoundedConstructible A X
          (F.obj (constantComplex A (Spec (.of k)))) ∧
      DerivedCategory.hasTorAmplitudeIn A X (-2 * (d : ℤ)) 0
          (F.obj (constantComplex A (Spec (.of k)))) ∧
      Nonempty
        ((((derivedHom (ModuleCat.{u + 1} A) X).obj (op (constantComplex A X))).obj
          (F.obj (constantComplex A (Spec (.of k))))) ≅
            F.obj (constantComplex A (Spec (.of k))))) := by
  let : HasCompactification f := c.hasCompactification
  let eF : rightDerivedUpperShriek A f ≅ F :=
    ((rightDerivedUpperShriekAdjunction A f).ofNatIsoLeft
      (rightDerivedLowerShriekIso A c).symm).rightAdjointUniq _adj
  let eω : dualizingComplex A f ≅ F.obj (constantComplex A (Spec (.of k))) :=
    eF.app (constantComplex A (Spec (.of k)))
  have calculation (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
      (a b : ℤ) (K : DerivedCategoryModule A X)
      (hc : DerivedCategory.isBoundedConstructible A X K)
      (ht : DerivedCategory.hasTorAmplitudeIn A X a b K) :
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X
          (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj
            (F.obj (constantComplex A (Spec (.of k))))) ∧
        DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) X
          (-b - 2 * (d : ℤ)) (-a)
          (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj
            (F.obj (constantComplex A (Spec (.of k))))) := by
    obtain ⟨hbc, htor⟩ :=
      constructibleFiniteTor_and_torAmplitudeIn_verdierDual_of_perfectField A f d hd a b
        ((finiteVerdier_boundedConstructible_iff A X K).1 hc)
        (DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 ht)
    let e := ((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).mapIso eω
    exact ⟨(DerivedCategory.boundedConstructible _ X).prop_of_iso e hbc.1,
      (DerivedCategory.torAmplitudeIn _ X _ _).prop_of_iso e htor⟩
  constructor
  · intro K hc ht
    obtain ⟨a, b, ht⟩ := ht
    obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le f
    obtain ⟨hbc, htor⟩ := calculation d hd a b K hc ht
    exact ⟨(finiteVerdier_boundedConstructible_iff A X _).2 hbc,
      -b - 2 * (d : ℤ), -a, DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2 htor⟩
  · intro d hd
    have hu : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X
        (constantComplex A X) :=
      (DerivedCategory.boundedConstructible _ X).prop_of_iso
        (_root_.DerivedCategory.singleFunctorObjUnitIso _)
        (DerivedCategory.boundedConstructible_singleFunctor_obj _ 0)
    have hut : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) X 0 0
        (constantComplex A X) :=
      (DerivedCategory.torAmplitudeIn _ X 0 0).prop_of_iso
        (_root_.DerivedCategory.singleFunctorObjUnitIso _)
        (_root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
          (ObjectProperty.flat_of_isDualizable isDualizable_unit))
    obtain ⟨hbc, htor⟩ := calculation d hd 0 0 (constantComplex A X)
      ((finiteVerdier_boundedConstructible_iff A X _).2 hu)
      (DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2 hut)
    let eu : (((derivedHom (ModuleCat.{u + 1} A) X).obj
        (op (constantComplex A X))).obj (F.obj (constantComplex A (Spec (.of k))))) ≅
          F.obj (constantComplex A (Spec (.of k))) :=
      (MonoidalClosed.unitNatIso.app _).symm
    refine ⟨?_, (finiteVerdier_boundedConstructible_iff A X _).2
      ((DerivedCategory.boundedConstructible _ X).prop_of_iso eu hbc), ?_, ⟨eu⟩⟩
    · intro a b K hc ht
      exact DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
        (calculation d hd a b K hc ht).2
    · apply DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
      simpa only [neg_zero, zero_sub, neg_mul] using
        (DerivedCategory.torAmplitudeIn _ X _ _).prop_of_iso eu htor

end AlgebraicGeometry.Etale
