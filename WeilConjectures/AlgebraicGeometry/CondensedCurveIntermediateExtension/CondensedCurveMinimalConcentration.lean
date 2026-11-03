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
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Geometric intermediate-extension proof step -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open scoped CategoryTheory.Obj
open AlgebraicGeometry.ProEtale.CondensedRing
open WeilConjectures
open AlgebraicGeometry.ProEtale.CurvePerverseHeartStatement
namespace AlgebraicGeometry.ProEtale.CondensedCurveIntermediateExtension

set_option maxHeartbeats 2000000 in
-- Geometric instance synthesis and derived comparisons require a larger elaboration budget.
/-- A boundary-minimal extension is concentrated in ordinary degree minus one.
Source: rem-dl-a1-conventions, intermediate-extension argument, step 5.
Proof: the heart truncation sequence has quotient H^0(P)[0]. Exact pullback
and the identification with F[1] make that quotient a boundary object.
Minimality kills the quotient projection; its epimorphism makes the quotient
zero. The heart amplitude then concentrates P in degree minus one. The
single-complex comparison and shift identify P with H^-1(P)[1], retaining
constructibility and the lower heart condition.
(blueprint: lem-dl-a1-condensed-curve-minimal-concentration). -/
theorem boundary_minimal_concentration
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (c : Scheme.MiddleExtensionCurve D) (hEll : ell ≠ D.p)
    [GeometricallyConnected c.C.hom]
    (F : StrictWeilCondensed.WeilModule (coeff ell) (frobU D c))
    (P : DerivedCategory (Modules D ell (geomC D c)))
    (hP : perverseHeart D ell c hEll P)
    (α : (restriction D ell c).obj P ≅ (shiftedSheaf D ell c).obj F.carrier)
    (hMin : BoundaryMinimal D ell c F P hEll) :
    ∃ M : Modules D ell (geomC D c),
      IsConstructibleModuleObject (condensedRingObj (coeff ell) (geomC D c)) M ∧
      NoPunctualSubobject (Punctual ell (geomC D c)) M ∧
      Nonempty (P ≅ (shiftFunctor _ (1 : ℤ)).obj ((DerivedCategory.singleFunctor _ 0).obj M)) := by
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
  obtain ⟨hPc, hPle, hPge⟩ := hP
  let Q := boundedConstructible (condensedRingObj (coeff ell) (geomC D c))
  let le := CondensedPerverseLEZero ell (closure_baseField D) (D.geometricFiber c.C)
  let ge := CondensedPerverseGEZero ell (closure_baseField D) (D.geometricFiber c.C)
  let Ph : (le ⊓ ge).FullSubcategory := ⟨⟨P, hPc⟩, hPle, hPge⟩
  obtain ⟨B, C, f, g, hfg, hse, b, ce, hf, hgmap, eb, ec⟩ := hg.1.2.2.2.2.1 Ph
  have hCd : perverseHeart D ell c hEll C.obj.obj :=
    ⟨C.obj.property, C.property.1, C.property.2⟩
  have hShiftLE : DerivedCategory.TStructure.t.IsLE
      ((shiftedSheaf D ell c).obj F.carrier) (-1) := by
    exact DerivedCategory.TStructure.t.isLE_shift _ 0 1 (-1) (by lia)
  have hRP : ((restriction D ell c).obj P).IsLE (-1) :=
    DerivedCategory.TStructure.t.isLE_of_iso α.symm (-1)
  have hRC : IsZero ((restriction D ell c).obj C.obj.obj) := by
    have hz := DerivedCategory.TStructure.t.isZero_truncGE_obj_of_isLE
      (-1) 0 (by lia) ((restriction D ell c).obj P)
    exact hz.of_iso ((restriction D ell c).mapIso ce ≪≫
      ((CondensedRing.upperStar (coeff ell) (geomJ D c)).mapDerivedCategoryTruncGEIso
        0).app P)
  have hgz : g.hom.hom = 0 := (hMin C.obj.obj hCd hRC).2 g.hom.hom
  have hgz' : g = 0 := by
    apply ObjectProperty.hom_ext _
    exact ObjectProperty.hom_ext _ hgz
  have : Epi g := hse.epi_g
  have hzC := IsZero.of_epi_eq_zero g hgz'
  have hzH : IsZero ((DerivedCategory.homologyFunctor _ 0).obj P) := by
    obtain ⟨eC⟩ := ec
    let I := (le ⊓ ge).ι ⋙ Q.ι
    have hz := (I.map_isZero hzC).of_iso eC.symm
    exact ((DerivedCategory.homologyFunctor _ 0).map_isZero hz).of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app
        ((DerivedCategory.homologyFunctor _ 0).obj P)).symm
  have hdesc := (hg.1.2.2.2.1 ⟨P, hPc⟩).mp ⟨hPle, hPge⟩
  have : P.IsLE (-1) := (DerivedCategory.isLE_iff P (-1)).mpr (by
    intro n hn
    by_cases he : n = 0
    · simpa only [he] using hzH
    · exact hdesc.1 n (by lia) he)
  have : P.IsGE (-1) := (DerivedCategory.isGE_iff P (-1)).mpr (by
    intro n hn
    exact hdesc.1 n (by lia) (by lia))
  obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE P (-1)
  let eM := ((DerivedCategory.homologyFunctor _ (-1)).mapIso e) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ (-1)).app M
  refine ⟨M, ?_, ?_, ?_⟩
  · exact IsConstructibleModuleObject.of_iso eM (hPc.2 (-1))
  · intro N i hi hN
    exact hdesc.2.2 N (i ≫ eM.inv) inferInstance hN
  · exact ⟨e ≪≫ (((DerivedCategory.singleFunctors _).shiftIso
      (1 : ℤ) (-1) 0 (by lia)).app M).symm⟩

end AlgebraicGeometry.ProEtale.CondensedCurveIntermediateExtension
