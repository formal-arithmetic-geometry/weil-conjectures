/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleAmbientRingedExchange
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison
public import Sheaf.SixFunctors.ClassicalDefinition
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty
import Sheaf.AlgebraicGeometry.ClassicalDerivedEquivalence
import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedEncoding
import Sheaf.AlgebraicGeometry.ComparisonReflectsTorsion
import Sheaf.AlgebraicGeometry.ProEtaleConstantExchangeEncoding
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange

/-!
# Proper base change on classical pro-etale complexes

Source: literature/blueprint/main-20261015/blueprint/sec-proper-base-change/
sk-thm-properbasechange/_section.md, order 1062
(blueprint: sk-thm-properbasechange).

The exchange below is the published ambient ringed exchange specialized to arbitrary
constant coefficients and their constant-section identifications. The conclusion records
both endpoints in the bounded-below classical full subcategory and invertibility of the
specified ambient morphism; fullness then places its inverse in that subcategory.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The canonical uncompleted constant-coefficient exchange: the published ambient ringed
exchange `proEtaleAmbientRingedExchange` (def-weil-pbc-ambient-ringed-exchange) on the four
constant ring sheaves with their constant-section identifications. It is the
unit--square--counit mate of the canonical composition comparisons. The two composite
coefficient identifications agree because both are the constant comparison for the same
composite arrow (`proEtaleConstantRingCompositeCoefficients_eq` and the square equation).
Source: blueprint proper-base-change theorem, displayed exchange, and Stacks Tag 07A7
(blueprint: sk-thm-properbasechange). No torsion or classicality enters this construction. -/
abbrev classicalProEtaleExchange (Λ : Type u) [CommRing Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g) :
    proEtaleRingDerivedDirectImage f (proEtaleConstantRing Y Λ) (proEtaleConstantRing X Λ)
        (proEtaleConstantRingComparison f Λ) ⋙ proEtaleConstantRingDerivedPullback Λ g ⟶
      proEtaleConstantRingDerivedPullback Λ g' ⋙
        proEtaleRingDerivedDirectImage f' (proEtaleConstantRing Y' Λ)
          (proEtaleConstantRing X' Λ) (proEtaleConstantRingComparison f' Λ) :=
  proEtaleAmbientRingedExchange sq
    (proEtaleConstantRing X Λ) (proEtaleConstantRing Y Λ)
    (proEtaleConstantRing X' Λ) (proEtaleConstantRing Y' Λ)
    (proEtaleConstantRingComparison f Λ) (proEtaleConstantRingComparison g Λ)
    (proEtaleConstantRingComparison g' Λ) (proEtaleConstantRingComparison f' Λ)
    ((heq_of_eq (proEtaleConstantRingCompositeCoefficients_eq g' f Λ)).trans
      ((congr_arg_heq (fun q : X' ⟶ Y ↦ proEtaleConstantRingComparison q Λ) sq.w).trans
        (heq_of_eq (proEtaleConstantRingCompositeCoefficients_eq f' g Λ)).symm))

private theorem localTorsion_of_iso {C : Type*} [Category C]
    {J : GrothendieckTopology C} {F G : Sheaf J AddCommGrpCat.{u + 1}}
    (e : F ≅ G) (hG : G.IsTorsion) : F.IsTorsion := by
  intro U s
  obtain ⟨S, hS, h⟩ := hG (e.hom.hom.app U s)
  refine ⟨S, hS, ?_⟩
  intro V f hf
  have ht := h hf
  have hn := ConcreteCategory.congr_hom (e.inv.hom.naturality f.op)
    (e.hom.hom.app U s)
  have he : e.inv.hom.app U (e.hom.hom.app U s) = s := by
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (congrArg (fun t : F ⟶ F ↦ t.hom) e.hom_inv_id) U) s
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, he] at hn
  rw [← hn]
  obtain ⟨n, hn, hkill⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp ht
  apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
  refine ⟨n, hn, ?_⟩
  rw [← map_nsmul, hkill, map_zero]

private theorem exists_torsion_etale_origin (A : Type u) [CommRing A]
    (X : Scheme.{u}) (K : proEtaleDerivedCategory X A)
    (hb : ∃ n : ℤ, DerivedCategory.IsGE K n)
    (hc : ProEtale.IsClassicalModuleComplex K)
    (ht : ∀ q : ℤ, ((SheafOfModules.toSheaf _).obj
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X A)) q).obj K)).IsTorsion) :
    ∃ L : DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))),
      Etale.DerivedCategory.Plus.moduleTorsionHomology (ULift.{u + 1, u} A) X L ∧
      Nonempty ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory.obj L.obj ≅
          (proEtaleDerivedModuleRestriction X A).obj K) := by
  let B := ULift.{u + 1, u} A
  let : TopologicalSpace B := ⊥
  let : DiscreteTopology B := ⟨rfl⟩
  let N := (proEtaleDerivedModuleRestriction X A).obj K
  have hbN : ∃ n : ℤ, DerivedCategory.IsGE N n := by
    obtain ⟨n, hn⟩ := hb
    exact ⟨n, (proEtaleDerivedModuleRestriction_isGE_iff X A K n).mpr hn⟩
  let Np : DerivedCategory.Plus (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} B)) :=
    ⟨N, hbN⟩
  have hcN : ProEtale.ClassicalPlus X B Np :=
    (proEtaleDerivedModuleRestriction_classical_iff X A K).mp hc
  have hu := (ProEtale.boundedBelowComparison X B).1
  have he := ProEtale.classicalDerivedEquivalence X B
    (fun L ↦ by let := hu; infer_instance)
  have hε := he.2.1 Np hcN
  let L := (ProEtale.comparisonLowerStar
    (ModuleCat.{u + 1} B) X).rightDerivedFunctorPlus.obj Np
  let e : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} B) X).mapDerivedCategory.obj L.obj ≅ N :=
    ((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} B) X).mapDerivedCategoryPlusCompatibility.app L).symm ≪≫
        DerivedCategory.Plus.ι.mapIso
          (asIso ((ProEtale.comparisonAdjunction
            (ModuleCat.{u + 1} B) X).derivedPlus.counit.app Np))
  refine ⟨L, ?_, ⟨e⟩⟩
  intro q
  apply ProEtale.comparisonUpperStar_reflects_local_torsion X B
  let d := ((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} B) X).mapDerivedCategoryHomologyFunctorIso q).app L.obj ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso e ≪≫
    (proEtaleDerivedModuleRestrictionHomologyIso X A q K).symm
  exact localTorsion_of_iso
    ((sheafCompose (ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1})).mapIso d) (ht q)

/-- Proper base change for bounded-below classical complexes with locally torsion
underlying abelian cohomology, for arbitrary constant commutative coefficients.
Source: blueprint main-20261015, sk-thm-properbasechange, order 1062
(blueprint: sk-thm-properbasechange).

Proof: exact restriction to constant scalar sections identifies cohomology, lower bounds
and classicality in the ringed and fixed-coefficient presentations. The bounded-below
comparison unit and classical derived equivalence give an etale origin L for K. The
comparison on geometric stalks reflects local torsion, so L has torsion cohomology.
The existing arbitrary-ring etale proper-base-change theorem applies to L. Its proof
retains the unit's projective-line, proper-reduction and torsion-assembly route.
Properness supplies the qcqs hypotheses for the etale/pro-etale exchange comparison.
The constant-coefficient encoding identifies that map with the specified ambient mate.
Reflect invertibility through the exact equivalence. Its source is isomorphic to the
comparison pullback of a bounded-below etale complex, hence bounded below and classical.
Its target has the same properties by the now invertible exchange. No uniform torsion
annihilator, finite coefficient ring, or completed derived category is used.
-/
theorem isIso_classicalProEtaleExchange_of_isProper (Λ : Type u) [CommRing Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} [IsProper f]
    (sq : ChosenCartesianSquare g' f' f g) (K : proEtaleDerivedCategory X Λ)
    (hbounded : ∃ n : ℤ, DerivedCategory.IsGE K n)
    (hclassical : ProEtale.IsClassicalModuleComplex K)
    (htorsion : ∀ q : ℤ,
      ((SheafOfModules.toSheaf _).obj
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules X (proEtaleConstantRing X Λ)) q).obj K)).IsTorsion) :
    (∃ n : ℤ, DerivedCategory.IsGE
      ((proEtaleRingDerivedDirectImage f (proEtaleConstantRing Y Λ)
        (proEtaleConstantRing X Λ) (proEtaleConstantRingComparison f Λ) ⋙
      proEtaleConstantRingDerivedPullback Λ g).obj K) n) ∧
    ProEtale.IsClassicalModuleComplex ((proEtaleRingDerivedDirectImage f (proEtaleConstantRing Y Λ)
        (proEtaleConstantRing X Λ) (proEtaleConstantRingComparison f Λ) ⋙
      proEtaleConstantRingDerivedPullback Λ g).obj K) ∧
    (∃ n : ℤ, DerivedCategory.IsGE
      ((proEtaleConstantRingDerivedPullback Λ g' ⋙
      proEtaleRingDerivedDirectImage f' (proEtaleConstantRing Y' Λ)
        (proEtaleConstantRing X' Λ) (proEtaleConstantRingComparison f' Λ)).obj K) n) ∧
    ProEtale.IsClassicalModuleComplex ((proEtaleConstantRingDerivedPullback Λ g' ⋙
      proEtaleRingDerivedDirectImage f' (proEtaleConstantRing Y' Λ)
        (proEtaleConstantRing X' Λ) (proEtaleConstantRingComparison f' Λ)).obj K) ∧
    IsIso ((classicalProEtaleExchange Λ sq).app K) := by
  let B := ULift.{u + 1, u} Λ
  let : TopologicalSpace B := ⊥
  let : DiscreteTopology B := ⟨rfl⟩
  have hp : IsPullback g' f' f g :=
    IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  have : IsProper f' := MorphismProperty.of_isPullback hp inferInstance
  obtain ⟨L, hL, ⟨eK⟩⟩ := exists_torsion_etale_origin Λ X K
    hbounded hclassical htorsion
  let N := (proEtaleDerivedModuleRestriction X Λ).obj K
  let α := ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} B) sq.toCommSq
  have hα : IsIso (α.app N) := by
    rw [← NatTrans.isIso_app_iff_of_iso α eK]
    have hBC : IsIso ((AlgebraicGeometry.Etale.baseChange
        (ModuleCat.{u + 1} B) sq.toCommSq).app L) := by
      rw [Etale.baseChange_eq_derivedBaseChangeMapPlus]
      exact Etale.isIso_baseChange_of_isProper_of_torsionHomology B hp L hL
    have heq := ProEtale.comparison_derivedBaseChangeMap B hp L
    have hmap : IsIso ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} B) Y').mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map ((AlgebraicGeometry.Etale.baseChange
          (ModuleCat.{u + 1} B) sq.toCommSq).app L))) := inferInstance
    exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      (Arrow.isoMk ((ProEtale.baseChangeSourceComparisonIso f g B).app L)
        ((ProEtale.baseChangeTargetComparisonIso g' f' B).app L) heq.symm)).1 hmap
  obtain ⟨eα⟩ := proEtaleConstantExchange_encoding Λ sq _ K
  have hringmap : IsIso ((proEtaleDerivedModuleRestriction Y' Λ).map
      ((classicalProEtaleExchange Λ sq).app K)) :=
    ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff eα).2 hα
  have hring : IsIso ((classicalProEtaleExchange Λ sq).app K) :=
    isIso_of_reflects_iso _ (proEtaleDerivedModuleRestriction Y' Λ)
  let S := ((Etale.lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctorPlus ⋙
    (Etale.upperStar (ModuleCat.{u + 1} B) g).mapDerivedCategoryPlus).obj L
  let eS := (ProEtale.baseChangeSourceComparisonIso f g B).app L ≪≫
    ((ProEtale.lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctor ⋙
      (ProEtale.upperStar (ModuleCat.{u + 1} B) g).leftDerivedFunctor).mapIso eK
  let eleft := (Arrow.leftFunc.mapIso eα) ≪≫ eS.symm
  have hbS : ∃ n : ℤ, DerivedCategory.IsGE
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) Y').mapDerivedCategory.obj S.obj) n := by
    obtain ⟨n, hn⟩ := S.property
    let := hn
    exact ⟨n, (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) Y').isGE_mapDerivedCategory_obj
      S.obj n⟩
  have hu := (ProEtale.boundedBelowComparison Y' B).1
  have hcS : ProEtale.IsClassicalComplexFor Y' B
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) Y').mapDerivedCategory.obj S.obj) := by
    have hc := (ProEtale.classicalDerivedEquivalence Y' B
      (fun M ↦ by let := hu; infer_instance)).1 S
    exact (proEtaleFixedClassical_iso_iff Y' B
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} B) Y').mapDerivedCategoryPlusCompatibility.app S)).mp hc
  have hbleft : ∃ n : ℤ, DerivedCategory.IsGE
      ((proEtaleDerivedModuleRestriction Y' Λ).obj
        ((Arrow.mk ((classicalProEtaleExchange Λ sq).app K)).left)) n := by
    obtain ⟨n, hn⟩ := hbS
    let := hn
    refine ⟨n, (DerivedCategory.isGE_iff _ n).mpr (fun q hq ↦ ?_)⟩
    exact ((DerivedCategory.isGE_iff _ n).mp hn q hq).of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso eleft)
  have hcleft : ProEtale.IsClassicalComplexFor Y' B
      ((proEtaleDerivedModuleRestriction Y' Λ).obj
        ((Arrow.mk ((classicalProEtaleExchange Λ sq).app K)).left)) :=
    (proEtaleFixedClassical_iso_iff Y' B eleft).mpr hcS
  let ering := (proEtaleDerivedModuleRestriction Y' Λ).mapIso
    (asIso ((classicalProEtaleExchange Λ sq).app K))
  refine ⟨?_, ?_, ?_, ?_, hring⟩
  · obtain ⟨n, hn⟩ := hbleft
    exact ⟨n, (proEtaleDerivedModuleRestriction_isGE_iff Y' Λ _ n).mp hn⟩
  · exact (proEtaleDerivedModuleRestriction_classical_iff Y' Λ _).mpr hcleft
  · obtain ⟨n, hn⟩ := hbleft
    let := hn
    refine ⟨n, (proEtaleDerivedModuleRestriction_isGE_iff Y' Λ _ n).mp
      ((DerivedCategory.isGE_iff _ n).mpr (fun q hq ↦ ?_))⟩
    exact ((DerivedCategory.isGE_iff _ n).mp hn q hq).of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso ering.symm)
  · exact (proEtaleDerivedModuleRestriction_classical_iff Y' Λ _).mpr
      ((proEtaleFixedClassical_iso_iff Y' B ering).mp hcleft)

end AlgebraicGeometry.Scheme
