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
import WeilConjectures.AlgebraicGeometry.CondensedCurveIntermediateExtension.CondensedCurveBoundarySupport
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Geometric intermediate-extension proof step -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj
open AlgebraicGeometry.ProEtale.CondensedRing
open WeilConjectures
open AlgebraicGeometry.ProEtale.CurvePerverseHeartStatement
namespace AlgebraicGeometry.ProEtale.CondensedCurveIntermediateExtension

set_option maxHeartbeats 2000000 in
-- Geometric instance synthesis and derived comparisons require a larger elaboration budget.
/-- The geometric basic object and concentration of boundary heart objects.
Source: rem-dl-a1-conventions, intermediate-extension assertion, proof steps 1--3.
Proof: base change preserves finite type, separatedness, smoothness, connectedness,
and dimension one. The geometric open is dense and its complement is finite closed.
Apply the curve-heart basic-object clause to the lisse sheaf F. For a boundary
heart object Q, exact pullback commutes with cohomology, so its H^-1 and H^0
restrict to zero. Constructibility and the finite closed complement make them
punctual. The no-punctual-subobject condition kills H^-1 by applying it to the
identity. The remaining amplitude [0,0] identifies Q with its degree-zero
cohomology B, whose pullback is zero. Empty boundary and the zero sheaf require
no nonemptiness assumptions.
(blueprint: lem-dl-a1-condensed-curve-boundary-concentration). -/
theorem geometric_basic_and_boundary_concentration
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (c : Scheme.MiddleExtensionCurve D) (hEll : ell ≠ D.p)
    [GeometricallyConnected c.C.hom]
    (F : StrictWeilCondensed.WeilModule (coeff ell) (frobU D c))
    (_hCons : IsConstantModelConstructible (coeff ell) (geomU D c) F.carrier)
    (hLisse : IsLisseCoefficientModule (coeff ell) F.carrier) :
    perverseHeart D ell c hEll (shiftedImage D ell c F) ∧
      ∀ Q : DerivedCategory (Modules D ell (geomC D c)),
        perverseHeart D ell c hEll Q → IsZero ((restriction D ell c).obj Q) →
        ∃ B : Modules D ell (geomC D c),
          IsZero ((CondensedRing.upperStar (coeff ell) (geomJ D c)).obj B) ∧
          Nonempty (Q ≅ (DerivedCategory.singleFunctor _ 0).obj B) := by
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
  refine ⟨hg.2.1 (geomU D c) (geomJ D c) hj hden F.carrier hLisse, ?_⟩
  intro Q hQ hZero
  obtain ⟨hQc, hle, hge⟩ := hQ
  have hdesc := (hg.1.2.2.2.1 ⟨Q, hQc⟩).mp ⟨hle, hge⟩
  let L := CondensedRing.upperStar (coeff ell) (geomJ D c)
  have hcoh (n : ℤ) : IsZero (L.obj ((DerivedCategory.homologyFunctor _ n).obj Q)) :=
    ((DerivedCategory.homologyFunctor _ n).map_isZero hZero).of_iso
      ((L.mapDerivedCategoryHomologyFunctorIso n).app Q)
  have hm : IsZero ((DerivedCategory.homologyFunctor _ (-1)).obj Q) :=
    hdesc.2.2 _ (𝟙 _) inferInstance
      (boundary_support_punctual D ell c _ (hQc.2 (-1)) (hcoh (-1)))
  have hge0 : Q.IsGE 0 := (DerivedCategory.isGE_iff Q 0).mpr (by
    intro n hn
    by_cases he : n = -1
    · simpa only [he] using hm
    · exact hdesc.1 n he (by lia))
  have hle0 : Q.IsLE 0 := (DerivedCategory.isLE_iff Q 0).mpr (by
    intro n hn
    exact hdesc.1 n (by lia) (by lia))
  obtain ⟨B, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE Q 0
  refine ⟨B, ?_, ⟨e⟩⟩
  have hz : IsZero ((DerivedCategory.singleFunctor _ 0).obj (L.obj B)) :=
    hZero.of_iso ((L.mapDerivedCategory.mapIso e) ≪≫
      (L.mapDerivedCategorySingleFunctor 0).app B).symm
  exact ((DerivedCategory.homologyFunctor _ 0).map_isZero hz).of_iso
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app (L.obj B)).symm

end AlgebraicGeometry.ProEtale.CondensedCurveIntermediateExtension
