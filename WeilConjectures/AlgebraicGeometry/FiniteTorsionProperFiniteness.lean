/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientModelComparison
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientModelComparison
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingPullbackFixed
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTorsionProperFiniteness
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect

/-! # Proper finiteness for finite discrete condensed field coefficients

Source: Bhatt--Scholze, The pro-etale topology for schemes, Theorem 6.7.1,
proper alternative, and Lemmas 5.4.3 and 6.7.2
(blueprint: lem-fd-finite-torsion-proper-finiteness).

The direct image is the total right derived functor on internal coefficient modules.
Bounded constructibility uses finite constant local models and imposes no Tor condition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Exact coefficient encoding identifies the bounded constructible predicates.
The finite-coefficient model comparison and bounded etale-origin criterion are applied
cohomology by cohomology, with the same normalized encoding. -/
private theorem fixedBoundedCriterion
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [Finite A]
    (T : Scheme.{u}) (e : FiniteDiscreteOrdinary.Encoding A T)
    (he : FiniteDiscreteOrdinary.FiniteCoefficientModelComparison A T e)
    (K : DerivedCategory (FiniteDiscreteOrdinary.Internal A T)) :
    constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) T K ↔
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (ULift.{u + 1} A)) T
        (e.fixedDerived.functor.obj K) := by
  let F := e.ordinary.functor ⋙ e.fixed.functor
  have hc (q : ℤ) :
      Scheme.IsConstructibleProEtaleModuleSheaf T A
        ((DerivedCategory.homologyFunctor _ q).obj (e.ordinaryDerived.functor.obj K)) ↔
      IsConstructible (ULift.{u + 1} A)
        ((DerivedCategory.homologyFunctor _ q).obj (F.mapDerivedCategory.obj K)) := by
    let d := (FiniteDiscreteOrdinary.fixedIso A T e
      ((DerivedCategory.homologyFunctor _ q).obj (e.ordinaryDerived.functor.obj K))).symm
    let j := (e.ordinary.functor.mapDerivedCategoryHomologyFunctorIso q).app K
    let k := (F.mapDerivedCategoryHomologyFunctorIso q).app K
    let z := d ≪≫ e.fixed.functor.mapIso j.symm ≪≫ k
    exact (Scheme.proEtaleModuleRestriction_constructible_iff T A _).trans
      ⟨isConstructible_of_iso z, isConstructible_of_iso z.symm⟩
  rw [he.boundedConstructible K]
  constructor
  · intro hK
    exact DerivedCategory.boundedConstructible_of_homology (ULift.{u + 1} A)
      (F.bounded_mapDerivedCategory_obj
        (e.ordinary.functor.bounded_of_bounded_mapDerivedCategory_obj hK.1))
      (fun q ↦ exists_isConstructibleSheaf_iso_comparisonUpperStar_obj _
        ((hc q).mp (hK.2 q)))
  · rintro ⟨L, hL, ⟨z⟩⟩
    let C := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T
    have hb : _root_.DerivedCategory.TStructure.t.bounded (F.mapDerivedCategory.obj K) :=
      _root_.DerivedCategory.TStructure.t.bounded.prop_of_iso z
        (C.bounded_mapDerivedCategory_obj hL.1)
    refine ⟨e.ordinary.functor.bounded_mapDerivedCategory_obj
      (F.bounded_of_bounded_mapDerivedCategory_obj hb), fun q ↦ (hc q).mpr ?_⟩
    let H := (_root_.DerivedCategory.homologyFunctor _ q).obj L
    have : Scheme.IsConstructibleSheaf H := hL.2 q
    let j := (C.mapDerivedCategoryHomologyFunctorIso q).app L
    exact isConstructible_of_iso
      (j ≪≫ (_root_.DerivedCategory.homologyFunctor _ q).mapIso z)
      (isConstructible_comparisonUpperStar_obj H)

/-- Finite truncation devissage extends uniform heart-level proper finiteness
(Bhatt--Scholze 6.7.1) to bounded constructible etale complexes. -/
private theorem etaleBoundedPushforward
    (ℓ : ℕ) [Fact ℓ.Prime] (A : Type (u + 1)) [Field A] [Finite A] [CharP A ℓ]
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    (h : Z ⟶ Y) [IsProper h]
    (K : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) Z K) :
    Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) Y
      ((Etale.lowerStar (ModuleCat.{u + 1} A) h).rightDerivedFunctor.obj K) := by
  let H := Etale.lowerStar (ModuleCat.{u + 1} A) h
  let P := Etale.constructibleSheaf (ModuleCat.{u + 1} A) Z
  let Q := (Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) Y).inverseImage
    H.rightDerivedFunctor
  obtain ⟨d, hd⟩ :=
    Etale.exists_uniform_bound_constructible_higherDirectImage_of_isProper_finite_field ℓ A h
  have hsingle (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) (hF : P F) :
      Q ((_root_.DerivedCategory.singleFunctor _ 0).obj F) := by
    have hf := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).mpr hF
    let X := (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F
    let e := H.rightDerivedFunctorPlusCompatibility.app X
    have hc (q : ℤ) : Scheme.IsConstructibleSheaf
        ((_root_.DerivedCategory.homologyFunctor _ q).obj
          (H.rightDerivedFunctor.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) := by
      have : Scheme.IsConstructibleSheaf (Etale.higherDirectImage A h q F) :=
        (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hd F hf q).1
      exact Scheme.IsConstructibleSheaf.of_iso (F := Etale.higherDirectImage A h q F)
        ((_root_.DerivedCategory.homologyFunctor _ q).mapIso e)
    have hz (q : ℤ) (hq : q < 0 ∨ (d : ℤ) < q) : IsZero
        ((_root_.DerivedCategory.homologyFunctor _ q).obj
          (H.rightDerivedFunctor.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) :=
      ((hd F hf q).2 hq).of_iso
        ((_root_.DerivedCategory.homologyFunctor _ q).mapIso e).symm
    exact ⟨⟨⟨0, (_root_.DerivedCategory.isGE_iff _ 0).mpr
      (fun q hq ↦ hz q (.inl hq))⟩,
      ⟨d, (_root_.DerivedCategory.isLE_iff _ d).mpr (fun q hq ↦ hz q (.inr hq))⟩⟩, hc⟩
  exact _root_.DerivedCategory.prop_of_bounded Q P hsingle K hK.1 hK.2

/-- The qcqs direct-image comparison transports etale proper finiteness to
bounded constructible pro-etale complexes of etale origin (Stacks 099R). -/
private theorem proEtaleBoundedPushforward
    (ℓ : ℕ) [Fact ℓ.Prime] (A : Type (u + 1)) [Field A] [Finite A] [CharP A ℓ]
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    (h : Z ⟶ Y) [IsProper h]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) Z K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) Y
      ((lowerStar (ModuleCat.{u + 1} A) h).rightDerivedFunctor.obj K) := by
  obtain ⟨L, hL, ⟨e⟩⟩ := hK
  refine (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) Y).prop_of_iso
    (((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.mapIso
        ((Etale.lowerStar (ModuleCat.{u + 1} A) h).rightDerivedFunctorPlusCompatibility.app
          ⟨L, hL.1.1⟩)).symm ≪≫
      (rightDerivedLowerStarComparisonIso' h (ModuleCat.{u + 1} A)).app ⟨L, hL.1.1⟩ ≪≫
      (lowerStar (ModuleCat.{u + 1} A) h).rightDerivedFunctor.mapIso e) ?_
  exact DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj
    (etaleBoundedPushforward ℓ A h L hL)

/-- Proper direct image preserves bounded constructibility for a finite field with its
specified discrete topology, over arbitrary Noetherian schemes.

Source: Bhatt--Scholze, Theorem 6.7.1 (proper alternative), with residue field A;
compare Lemmas 5.4.3 and 6.7.2 and Stacks Tag 08J5
(blueprint: lem-fd-finite-torsion-proper-finiteness).

Proof: use the normalized finite-coefficient equivalence and its exact cohomology
comparison to identify finite constant-model bounded constructibility with bounded
constructible etale origin. For etale sheaves in degree zero, the uniform higher-direct-image
finiteness theorem gives constructible homology and bounds [0,d]. The inverse image of the
triangulated bounded constructible property under the total right derived direct image is
triangulated, so finite truncation devissage extends this assertion to bounded constructible
etale complexes. The qcqs etale/pro-etale direct-image comparison then proves the assertion
for fixed-coefficient pro-etale complexes of etale origin. Finally the normalized sectionwise
pushforward isomorphism, derived through the exact encoding equivalences, identifies this
fixed-coefficient direct image with the specified internal one. No Tor bound is used. -/
theorem constantModelBoundedConstructible_derivedPushforward_of_isProper_finite_field
    (ℓ : ℕ) [Fact ℓ.Prime] (A : Type u) [Field A] [Finite A] [CharP A ℓ]
    [TopologicalSpace A] [DiscreteTopology A]
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    (h : Z ⟶ Y) [IsProper h]
    (K : DerivedCategory (FiniteDiscreteOrdinary.Internal A Z))
    (hK : constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) Z K) :
    constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) Y
      ((CondensedRing.moduleObjectDerivedPushforward
        (FiniteDiscreteOrdinary.coefficient A) h).obj K) := by
  obtain ⟨eZ, heZ⟩ := FiniteDiscreteOrdinary.finiteCoefficientModelComparison A Z
  obtain ⟨eY, heY⟩ := FiniteDiscreteOrdinary.finiteCoefficientModelComparison A Y
  apply (fixedBoundedCriterion A Y eY heY _).mpr
  have hk := (fixedBoundedCriterion A Z eZ heZ K).mp hK
  have hp := proEtaleBoundedPushforward ℓ (ULift.{u + 1} A) h _ hk
  let F := CondensedRing.lowerStar (FiniteDiscreteOrdinary.coefficient A) h
  let G := lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) h
  let ET := eY.ordinary.trans eY.fixed
  let EU := eZ.ordinary.trans eZ.fixed
  have : ET.functor.Additive := inferInstanceAs
    (eY.ordinary.functor ⋙ eY.fixed.functor).Additive
  have : EU.functor.Additive := inferInstanceAs
    (eZ.ordinary.functor ⋙ eZ.fixed.functor).Additive
  let d : F.rightDerivedFunctor ⋙ eY.fixedDerived.functor ≅
      eZ.fixedDerived.functor ⋙ G.rightDerivedFunctor :=
    (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F ET.functor).symm ≪≫
      Functor.rightDerivedFunctorNatIso
        (FiniteDiscreteOrdinary.encodingPushforwardNatIso A Y Z h eY eZ) ≪≫
      Functor.mapDerivedCategoryCompRightDerivedFunctorIso EU.functor G
  exact (DerivedCategory.boundedConstructible
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) Y).prop_of_iso
      (d.app K).symm hp

end AlgebraicGeometry.ProEtale
