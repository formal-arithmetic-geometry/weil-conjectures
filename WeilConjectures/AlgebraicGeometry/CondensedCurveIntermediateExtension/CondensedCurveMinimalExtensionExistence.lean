/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage
public import WeilConjectures.AlgebraicGeometry.CurveMiddleExtension
public import WeilConjectures.AlgebraicGeometry.CurvePerverseHeartStatement.CurvePerverseHeartStatement
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import WeilConjectures.AlgebraicGeometry.CondensedCurveIntermediateExtension.CondensedCurveMinimalConcentration
import WeilConjectures.AlgebraicGeometry.CondensedCurveIntermediateExtension.CondensedCurveMinimalSheafComparison
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.Regular

/-! # Geometric intermediate-extension proof step -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open AlgebraicGeometry.ProEtale.CurvePerverseHeartStatement
open AlgebraicGeometry.ProEtale.CondensedRing
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.CondensedCurveIntermediateExtension

private theorem punctual_of_iso (ell : ℕ) [Fact ell.Prime] (C : Scheme.{u})
    {M N : CurvePerverseHeartStatement.Modules ell C} (e : M ≅ N)
    (h : Punctual ell C M) : Punctual ell C N := by
  have hs : condensedModuleSupport (condensedRingObj (coeff ell) C) N =
      condensedModuleSupport (condensedRingObj (coeff ell) C) M := by
    unfold condensedModuleSupport
    congr 1
    ext x
    let S := sheafToPresheaf (Scheme.ProEt.topology C) Ab.{u + 1} ⋙
      (Functor.whiskeringLeft (Scheme.ProEtaleGeometricNeighbourhood (C.algClosurePoint x))ᵒᵖ
        C.ProEtᵒᵖ Ab.{u + 1}).obj
          (Scheme.proEtaleGeometricNeighbourhoodForget (C.algClosurePoint x)).op ⋙ colim
    exact not_congr ((S.mapIso ((Mod.forget _).mapIso e)).isZero_iff.symm)
  exact ⟨h.1.of_iso e, hs ▸ h.2.1, fun x hx ↦ h.2.2 x (hs ▸ hx)⟩

private theorem constructible_of_zero (ell : ℕ) [Fact ell.Prime] (C : Scheme.{u})
    (M : CurvePerverseHeartStatement.Modules ell C) (hM : IsZero M) :
    IsConstructibleModuleObject (condensedRingObj (coeff ell) C) M := by
  obtain ⟨K, hK, hc⟩ := ObjectProperty.exists_prop_of_containsZero
    (boundedConstructible (condensedRingObj (coeff ell) C))
  exact (hc.2 0).of_iso (((DerivedCategory.homologyFunctor _ 0).map_isZero hK).iso hM)

private theorem single_bounded_constructible (ell : ℕ) [Fact ell.Prime] (C : Scheme.{u})
    (M : CurvePerverseHeartStatement.Modules ell C)
    (hM : IsConstructibleModuleObject (condensedRingObj (coeff ell) C) M) :
    boundedConstructible (condensedRingObj (coeff ell) C)
      ((DerivedCategory.singleFunctor _ 0).obj M) := by
  refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, ?_⟩
  intro i
  by_cases hi : i = 0
  · subst i
    exact hM.of_iso ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M).symm
  · apply constructible_of_zero
    rcases lt_or_gt_of_ne hi with hi | hi
    · exact DerivedCategory.isZero_of_isGE _ 0 i hi
    · exact DerivedCategory.isZero_of_isLE _ 0 i hi

set_option maxHeartbeats 2000000 in
-- Elaborating geometric base-change instances and derived comparisons needs extra heartbeats.
/-- A boundary-minimal perverse extension is isomorphic to the shifted ordinary image.
Source: rem-dl-a1-conventions, intermediate-extension assertion, proof steps 5--6.
Proof: exact pullback and the open identification kill the restriction of H^0(P).
Its degree-zero single is a boundary heart object. The perverse truncation short
exact sequence ends in this single; the boundary-Hom condition makes its epi
zero, hence kills H^0(P). Concentration identifies P with M[1], where M is
constructible and has no nonzero punctual subsheaf. Single-and-shift full
faithfulness turns the open identification into j^*M isomorphic to F. The
ordinary adjunction gives u:M→j_*F whose restriction is invertible. Exact
pullback and constructible closure make its kernel and cokernel punctual. The
kernel is zero by the lower heart condition on M. The connecting map from the
cokernel to M[1] is zero by boundary minimality, so the cokernel projection
splits. The cokernel is then a punctual subsheaf of j_*F; its lower heart
condition kills it. Thus u is invertible. Shift u and compose with the first
concentration comparison. This statement makes no normalization or uniqueness
claim and asserts no Weil compatibility.
(blueprint: lem-dl-a1-condensed-curve-minimal-extension-existence). -/
theorem boundary_minimal_extension_exists_iso
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (c : Scheme.MiddleExtensionCurve D) (hEll : ell ≠ D.p)
    [GeometricallyConnected c.C.hom]
    (F : StrictWeilCondensed.WeilModule (coeff ell) (frobU D c))
    (_hCons : IsConstantModelConstructible (coeff ell) (geomU D c) F.carrier)
    (hLisse : IsLisseCoefficientModule (coeff ell) F.carrier)
    (P : DerivedCategory (Modules D ell (geomC D c)))
    (hP : perverseHeart D ell c hEll P)
    (α : (restriction D ell c).obj P ≅ (shiftedSheaf D ell c).obj F.carrier)
    (hMin : BoundaryMinimal D ell c F P hEll)
    (hCounit : IsIso ((CondensedRing.upperStarLowerStarAdjunction
      (coeff ell) (geomJ D c)).counit.app F.carrier)) :
    Nonempty (P ≅ shiftedImage D ell c F) := by
  classical
  let : ConnectedSpace c.C.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton c.C.hom
  have : IsLocallyNoetherian c.C.left := LocallyOfFiniteType.isLocallyNoetherian c.C.hom
  have : IsRegular c.C.left := IsRegular.of_smooth c.C.hom
  have : IrreducibleSpace c.C.left := IsRegular.irreducibleSpace c.C.left
  have hd₀ : topologicalKrullDim c.C.left = (1 : WithBot ℕ∞) := by
    have h := c.pureDimension Set.univ (by simp [irreducibleComponents_eq_singleton])
    rw [IsHomeomorph.topologicalKrullDim_eq _
      (Homeomorph.Set.univ c.C.left).isHomeomorph] at h
    exact h
  have : SmoothOfRelativeDimension 1 c.C.hom :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq c.C.hom 1).mpr hd₀
  let a := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  have : LocallyOfFiniteType (D.geometricFiber c.C).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd c.C.hom a))
  have : QuasiCompact (D.geometricFiber c.C).hom :=
    inferInstanceAs (QuasiCompact (pullback.snd c.C.hom a))
  have : IsSeparated (D.geometricFiber c.C).hom :=
    inferInstanceAs (IsSeparated (pullback.snd c.C.hom a))
  have : Smooth (D.geometricFiber c.C).hom :=
    inferInstanceAs (Smooth (pullback.snd c.C.hom a))
  have : SmoothOfRelativeDimension 1 (D.geometricFiber c.C).hom :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (pullback.snd c.C.hom a))
  have : ConnectedSpace (geomC D c) :=
    inferInstanceAs (ConnectedSpace (↑(pullback c.C.hom a) : Type u))
  have : IsLocallyNoetherian (geomC D c) :=
    LocallyOfFiniteType.isLocallyNoetherian (D.geometricFiber c.C).hom
  have : IsRegular (geomC D c) := IsRegular.of_smooth (D.geometricFiber c.C).hom
  have : IrreducibleSpace (geomC D c) := IsRegular.irreducibleSpace (geomC D c)
  have hd : (geomC D c).IsPureDimension 1 := by
    intro Z hZ
    have hZeq : Z = Set.univ := by
      simp only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ
      exact hZ
    subst Z
    exact (IsHomeomorph.topologicalKrullDim_eq _
      (Homeomorph.Set.univ (geomC D c)).isHomeomorph).trans
        (topologicalKrullDim_eq_of_smoothOfRelativeDimension (D.geometricFiber c.C).hom 1)
  have hj : IsOpenImmersion (geomJ D c) :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) a c.j inferInstance
  have hden : DenseRange (geomJ D c) := by
    change Dense (Set.range ((Over.pullback a).map c.j).left)
    change Dense (Set.range (pullback.map c.U.hom a c.C.hom a
      c.j.left (𝟙 _) (𝟙 _) (by simp) (by simp)))
    rw [Scheme.Pullback.range_map]
    simpa using c.dense.preimage (pullback.fst c.C.hom a).isOpenMap
  let : Fact (ringChar D.k).Prime := ⟨closure_ringChar_prime D⟩
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans (D.card_base.trans D.cardinality_eq))
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  let : Fact (ringChar D.k ≠ ell) := ⟨(ringChar.eq D.k D.p).symm ▸ hEll.symm⟩
  let : Invertible (ell : D.k) := invertibleOfNonzero (by
    intro h
    have hd : D.p ∣ ell := (CharP.cast_eq_zero_iff D.k D.p ell).mp h
    exact hEll ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : ell.Prime)).mp hd).symm)
  have hg := curve_perverse_heart_statement ell (closure_baseField D)
    (D.geometricFiber c.C) hd
  obtain ⟨M, hMc, hNoM, ⟨e⟩⟩ := boundary_minimal_concentration D ell c hEll F P hP α hMin
  let L := CondensedRing.upperStar (coeff ell) (geomJ D c)
  let S := DerivedCategory.singleFunctor (Modules D ell (geomU D c)) 0 ⋙
    shiftFunctor _ (1 : ℤ)
  let d : (restriction D ell c).obj
      ((shiftFunctor _ (1 : ℤ)).obj ((DerivedCategory.singleFunctor _ 0).obj M)) ≅
      S.obj (L.obj M) :=
    ((restriction D ell c).commShiftIso (1 : ℤ)).app
        ((DerivedCategory.singleFunctor _ 0).obj M) ≪≫
      (shiftFunctor _ (1 : ℤ)).mapIso ((L.mapDerivedCategorySingleFunctor 0).app M)
  let αM : L.obj M ≅ F.carrier := S.preimageIso
    (d.symm ≪≫ ((restriction D ell c).mapIso e).symm ≪≫ α)
  have hA := hg.2.1 (geomU D c) (geomJ D c) hj hden F.carrier hLisse
  obtain ⟨hAc, hAle, hAge⟩ := hA
  have hAdesc := (hg.1.2.2.2.1 ⟨shiftedImage D ell c F, hAc⟩).mp ⟨hAle, hAge⟩
  let eAs : shiftedImage D ell c F ≅
      (DerivedCategory.singleFunctor _ (-1)).obj (image D ell c F) :=
    ((DerivedCategory.singleFunctors _).shiftIso (1 : ℤ) (-1) 0 (by lia)).app _
  let eAH := (DerivedCategory.homologyFunctor _ (-1)).mapIso eAs ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ (-1)).app (image D ell c F)
  have hAcons := (hAc.2 (-1)).of_iso eAH
  have hNoA : NoPunctualSubobject (Punctual ell (geomC D c)) (image D ell c F) := by
    intro N i hi hN
    exact hAdesc.2.2 N (i ≫ eAH.inv) inferInstance hN
  have hSingle (B : Modules D ell (geomC D c)) (hB : Punctual ell (geomC D c) B) :
      perverseHeart D ell c hEll ((DerivedCategory.singleFunctor _ 0).obj B) := by
    let K := (DerivedCategory.singleFunctor (Modules D ell (geomC D c)) 0).obj B
    have hc := single_bounded_constructible ell (geomC D c) B hB.1
    have hdesc := hg.1.2.2.2.1 ⟨K, hc⟩
    have hd : (∀ n : ℤ, n ≠ -1 → n ≠ 0 →
        IsZero ((DerivedCategory.homologyFunctor _ n).obj K)) ∧
        Punctual ell (geomC D c) ((DerivedCategory.homologyFunctor _ 0).obj K) ∧
        NoPunctualSubobject (Punctual ell (geomC D c))
          ((DerivedCategory.homologyFunctor _ (-1)).obj K) := by
      refine ⟨?_, ?_, ?_⟩
      · intro n hn hn0
        rcases lt_or_gt_of_ne hn0 with hn0 | hn0
        · exact DerivedCategory.isZero_of_isGE K 0 n hn0
        · exact DerivedCategory.isZero_of_isLE K 0 n hn0
      · exact punctual_of_iso ell (geomC D c)
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app B).symm hB
      · intro N i hi hN
        exact IsZero.of_mono i (DerivedCategory.isZero_of_isGE K 0 (-1) (by lia))
    exact ⟨hc, hdesc.mpr hd⟩
  have hδ (B : Modules D ell (geomC D c)) (hB : Punctual ell (geomC D c) B)
      (hzB : IsZero (L.obj B))
      (δ : (DerivedCategory.singleFunctor _ 0).obj B ⟶
        (shiftFunctor _ (1 : ℤ)).obj ((DerivedCategory.singleFunctor _ 0).obj M)) : δ = 0 := by
    have hz : IsZero ((restriction D ell c).obj
        ((DerivedCategory.singleFunctor _ 0).obj B)) :=
      ((DerivedCategory.singleFunctor _ 0).map_isZero hzB).of_iso
        ((L.mapDerivedCategorySingleFunctor 0).app B)
    have hd := (hMin _ (hSingle B hB) hz).1 (δ ≫ e.inv)
    exact (cancel_mono e.inv).1 (by simpa using hd)
  have hf := boundary_minimal_sheaf_comparison D ell c F M hMc hAcons hNoM hNoA αM hδ hCounit
  let f := (CondensedRing.upperStarLowerStarAdjunction (coeff ell) (geomJ D c)).homEquiv
    M F.carrier αM.hom
  exact ⟨e ≪≫ (shiftFunctor _ (1 : ℤ)).mapIso
    ((DerivedCategory.singleFunctor _ 0).mapIso (asIso f))⟩

end AlgebraicGeometry.ProEtale.CondensedCurveIntermediateExtension
