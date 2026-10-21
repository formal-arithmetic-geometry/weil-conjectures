/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.Paper.TAdmissibleCoefficientModels
import Mathlib.CategoryTheory.Triangulated.TStructure.Induced
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import WeilConjectures.RingTheory.CoherentRingPerfectComplexCohomology
import Sheaf.CategoryTheory.DerivedCategory.PerfectRingClassicalGenerator
import Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels
import Sheaf.Paper.CondensedScalarFinitePresentation
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Truncations and the heart for t-admissible condensed coefficients

Source: Hemo--Richarz--Scholbach, Definition 6.1 and Theorem 6.2(2)
(blueprint: lem-zl-t-admissible-dualizable-truncations).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open scoped ZeroObject in
private theorem dualizable_triangulated
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u}) :
    (dualizableProperty Λ X).IsTriangulated := by
  let P := dualizableProperty Λ X
  obtain ⟨hzero, hiso, hshift, hcone⟩ := condensed_dualizable_stable Λ.X X
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦ hiso _ _ ⟨e⟩ h⟩
  have : P.ContainsZero := ⟨0, CategoryTheory.Limits.isZero_zero _, hzero⟩
  have : P.IsStableUnderShift ℤ := ⟨fun n ↦ ⟨fun K h ↦ hshift K n h⟩⟩
  have : P.IsTriangulatedClosed₃ := .mk' (fun T hT h₁ h₂ ↦ hcone T hT h₁ h₂)
  have : P.IsTriangulatedClosed₂ :=
    ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃
  exact ⟨⟩

private theorem restricted_standard_of_truncations
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u})
    (htrunc : ∀ K : LisseAmbient Λ X, dualizableProperty Λ X K → ∀ n : ℤ,
      dualizableProperty Λ X ((DerivedCategory.TStructure.t.truncLE n).obj K) ∧
      dualizableProperty Λ X ((DerivedCategory.TStructure.t.truncGE n).obj K)) :
    ∃ h : (dualizableProperty Λ X).IsTriangulated,
      HasRestrictedStandardTStructure Λ X h := by
  have h := dualizable_triangulated Λ X
  have : (dualizableProperty Λ X).HasInducedTStructure DerivedCategory.TStructure.t :=
    ObjectProperty.HasInducedTStructure.mk' htrunc
  exact ⟨h, (dualizableProperty Λ X).tStructure DerivedCategory.TStructure.t,
    fun _ _ ↦ Iff.rfl, fun _ _ ↦ Iff.rfl⟩

private theorem perfect_cohomology_finitePresentation
    {R : Type*} [CommRing R] [HasDerivedCategory (ModuleCat R)]
    (hR : ∀ I : Ideal R, I.FG → Module.FinitePresentation R I)
    {K : DerivedCategory (ModuleCat R)} (hK : DerivedCategory.IsPerfectRingComplex K)
    (q : ℤ) :
    Module.FinitePresentation R ((DerivedCategory.homologyFunctor (ModuleCat R) q).obj K) := by
  obtain ⟨P, a, b, ha, hb, hP, ⟨e⟩⟩ := hK
  have hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n →
      CategoryTheory.Limits.IsZero (P.X n) := by
    refine ⟨a, b, fun n hn ↦ ?_⟩
    rcases hn with hn | hn
    · exact P.isZero_of_isStrictlyGE a n hn
    · exact P.isZero_of_isStrictlyLE b n hn
  have hfp := CochainComplex.finitePresentation_homology_of_coherent hR P hbounded
    (fun n ↦ ⟨(hP n).2, (hP n).1⟩) q
  have : Module.FinitePresentation R
      ((HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℤ) q).obj P) := hfp
  exact Module.FinitePresentation.of_equiv
    (((DerivedCategory.homologyFunctor _ q).mapIso e) ≪≫
      (DerivedCategory.homologyFunctorFactors _ q).app P).toLinearEquiv.symm

open scoped ZeroObject in
private theorem perfect_of_bounded_cohomology
    {R : Type*} [CommRing R] [HasDerivedCategory (ModuleCat R)]
    (hregular : ∀ N : ModuleCat R, Module.FinitePresentation R N →
      DerivedCategory.IsPerfectRingComplex ((DerivedCategory.singleFunctor _ 0).obj N))
    (K : DerivedCategory (ModuleCat R)) (a b : ℤ) [K.IsGE a] [K.IsLE b]
    (hfp : ∀ q : ℤ,
      Module.FinitePresentation R ((DerivedCategory.homologyFunctor (ModuleCat R) q).obj K)) :
    DerivedCategory.IsPerfectRingComplex K := by
  let P : ObjectProperty (DerivedCategory (ModuleCat R)) :=
    DerivedCategory.IsPerfectRingComplex
  have hPeq := DerivedCategory.isPerfectRingComplex_eq_triangEnvelope_singleton R
  have : P.IsTriangulated := by dsimp only [P]; rw [hPeq]; infer_instance
  have : P.IsClosedUnderIsomorphisms := by dsimp only [P]; rw [hPeq]; infer_instance
  let F : ObjectProperty (ModuleCat R) := fun N ↦ Module.FinitePresentation R N
  have : F.IsClosedUnderIsomorphisms := ⟨fun {X Y} e h ↦ by
    have : Module.FinitePresentation R X := h
    exact Module.FinitePresentation.of_equiv e.toLinearEquiv⟩
  have : F.ContainsZero := by
    have : Subsingleton (0 : ModuleCat R) :=
      ModuleCat.isZero_iff_subsingleton.mp (CategoryTheory.Limits.isZero_zero _)
    exact ⟨0, CategoryTheory.Limits.isZero_zero _, inferInstance⟩
  have single (L : DerivedCategory (ModuleCat R)) (q : ℤ)
      [L.IsGE q] [L.IsLE q] (hL : DerivedCategory.homologyProperty F L) : P L := by
    obtain ⟨N, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE L q
    have hN : F N := F.prop_of_iso
      (((DerivedCategory.homologyFunctor _ q).mapIso e) ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso _ q).app N) (hL q)
    have hp : P ((DerivedCategory.singleFunctor _ 0).obj N) := hregular N hN
    exact P.prop_of_iso
      ((((DerivedCategory.singleFunctors (ModuleCat R)).shiftIso (-q) q 0
        (by omega)).app N) ≪≫ e.symm) (P.le_shift (-q) _ hp)
  suffices h : ∀ (k : ℕ) (L : DerivedCategory (ModuleCat R)) (a b : ℤ),
      b - a ≤ k → L.IsGE a → L.IsLE b → DerivedCategory.homologyProperty F L → P L by
    exact h (b - a).toNat K a b (by omega) inferInstance inferInstance hfp
  intro k
  induction k with
  | zero =>
    intro L a b hab hge hle hL
    have := hge
    have := hle
    by_cases hba : b < a
    · exact P.prop_of_isZero (DerivedCategory.TStructure.t.isZero L b a hba)
    · have : L.IsGE b := DerivedCategory.TStructure.t.isGE_of_ge L b a (by omega)
      exact single L b hL
  | succ k ih =>
    intro L a b hab hge hle hL
    have := hge
    have := hle
    let T := (DerivedCategory.TStructure.t.triangleLTGE b).obj L
    have h₁ : P T.obj₁ := by
      have : T.obj₁.IsGE a :=
        inferInstanceAs (DerivedCategory.TStructure.t.IsGE
          ((DerivedCategory.TStructure.t.truncLT b).obj L) a)
      have : T.obj₁.IsLE (b - 1) := inferInstance
      exact ih _ a (b - 1) (by omega) inferInstance inferInstance
        ((DerivedCategory.homologyProperty F).prop_of_iso
          ((DerivedCategory.TStructure.t.truncLEIsoTruncLT (b - 1) b (by omega)).app L)
          (DerivedCategory.homologyProperty_truncLE hL (b - 1)))
    have h₃ : P T.obj₃ := by
      have : T.obj₃.IsGE b := inferInstance
      have : T.obj₃.IsLE b :=
        inferInstanceAs (DerivedCategory.TStructure.t.IsLE
          ((DerivedCategory.TStructure.t.truncGE b).obj L) b)
      exact single _ b (DerivedCategory.homologyProperty_truncGE hL b)
    exact P.ext_of_isTriangulatedClosed₂ T
      (DerivedCategory.TStructure.t.triangleLTGE_distinguished b L) h₁ h₃

open scoped ZeroObject in
private theorem perfect_truncations
    {R : Type*} [CommRing R] [HasDerivedCategory (ModuleCat R)]
    (hR : ∀ I : Ideal R, I.FG → Module.FinitePresentation R I)
    (hregular : ∀ N : ModuleCat R, Module.FinitePresentation R N →
      DerivedCategory.IsPerfectRingComplex ((DerivedCategory.singleFunctor _ 0).obj N))
    (K : DerivedCategory (ModuleCat R)) (hK : DerivedCategory.IsPerfectRingComplex K)
    (n : ℤ) :
    DerivedCategory.IsPerfectRingComplex ((DerivedCategory.TStructure.t.truncLE n).obj K) ∧
    DerivedCategory.IsPerfectRingComplex ((DerivedCategory.TStructure.t.truncGE n).obj K) := by
  have hfp := perfect_cohomology_finitePresentation hR hK
  obtain ⟨P, a, b, ha, hb, hP, ⟨e⟩⟩ := hK
  have : K.IsGE a := DerivedCategory.TStructure.t.isGE_of_iso e.symm a
  have : K.IsLE b := DerivedCategory.TStructure.t.isLE_of_iso e.symm b
  let F : ObjectProperty (ModuleCat R) := fun N ↦ Module.FinitePresentation R N
  have : F.IsClosedUnderIsomorphisms := ⟨fun {X Y} e h ↦ by
    have : Module.FinitePresentation R X := h
    exact Module.FinitePresentation.of_equiv e.toLinearEquiv⟩
  have : F.ContainsZero := by
    have : Subsingleton (0 : ModuleCat R) :=
      ModuleCat.isZero_iff_subsingleton.mp (CategoryTheory.Limits.isZero_zero _)
    exact ⟨0, CategoryTheory.Limits.isZero_zero _, inferInstance⟩
  exact ⟨perfect_of_bounded_cohomology hregular _ a n
      (DerivedCategory.homologyProperty_truncLE (P := F) hfp n),
    perfect_of_bounded_cohomology hregular _ n b
      (DerivedCategory.homologyProperty_truncGE (P := F) hfp n)⟩

/-- Standard truncations preserve dualizability, the standard t-structure restricts,
and its heart is exactly the scalar local models. Every cohomology sheaf of a
dualizable object has such models, with no uniform module or amplitude required.

Source: Hemo--Richarz--Scholbach, Definition 6.1 and Theorem 6.2(2)
(blueprint: lem-zl-t-admissible-dualizable-truncations).

Proof: coherence gives finitely presented cohomology of scalar perfect complexes.
The finite-resolution hypothesis makes these cohomology modules perfect in degree
zero. The classical-generator characterization gives shift and cone closure; a
finite Postnikov induction then makes every bounded complex with finitely presented
cohomology perfect. Apply this to both scalar truncations, including degrees outside
the support.

Flat extremally disconnected evaluations make ordinary scalar realization exact,
and `flat_ordinaryScalarRealization` identifies its derived functor with the prescribed
realization. Exact realization and exact inverse image commute with truncations and
cohomology. The local-perfect-model criterion therefore transports the scalar
truncation result to the dualizable objects. Their triangulated stability and
truncation stability give the induced standard t-structure.

For cohomology, take local perfect scalar models and apply the exact comparisons.
Their cohomology modules are finitely presented. The ordinary/internal finite scalar
presentation comparison converts them to precisely the required scalar local models.
This gives the heart implication by taking degree-zero cohomology of M[0]. Conversely,
convert the scalar local models to ordinary finitely presented modules, use the
finite-resolution hypothesis to make them perfect in degree zero, and use the exact
realization comparison and reverse local-perfect-model criterion. No uniform ranks,
amplitudes or choice of module across cover members is required. -/
theorem tAdmissible_dualizable_truncations
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (hΛ : IsTAdmissible Λ)
    (X : Scheme.{u}) (hX : HasLocallyFiniteIrreducibleComponents X) :
    (∀ K : LisseAmbient Λ X, dualizableProperty Λ X K → ∀ n : ℤ,
      dualizableProperty Λ X ((DerivedCategory.TStructure.t.truncLE n).obj K) ∧
      dualizableProperty Λ X ((DerivedCategory.TStructure.t.truncGE n).obj K)) ∧
    (∃ h : (dualizableProperty Λ X).IsTriangulated,
      HasRestrictedStandardTStructure Λ X h) ∧
    (∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X),
      dualizableProperty Λ X ((DerivedCategory.singleFunctor _ 0).obj M) ↔
        HasScalarLocalModels Λ X M) ∧
    (∀ K : LisseAmbient Λ X, dualizableProperty Λ X K → ∀ q : ℤ,
      HasScalarLocalModels Λ X ((DerivedCategory.homologyFunctor _ q).obj K)) := by
  have htrunc (K : LisseAmbient Λ X) (hK : dualizableProperty Λ X K) (n : ℤ) :
      dualizableProperty Λ X ((DerivedCategory.TStructure.t.truncLE n).obj K) ∧
      dualizableProperty Λ X ((DerivedCategory.TStructure.t.truncGE n).obj K) := by
    obtain ⟨U, hU⟩ := (condensed_dualizable_iff_local_perfect Λ.X X hX K).mp hK
    constructor
    · apply (condensed_dualizable_iff_local_perfect Λ.X X hX _).mpr
      refine ⟨U, fun i ↦ ?_⟩
      obtain ⟨P, hP, ⟨e⟩⟩ := hU i
      obtain ⟨ha, hl, hr, ⟨eF⟩⟩ := flat_ordinaryScalarRealization Λ hΛ.2.2 (U.X i)
      let F := ordinaryScalarRealization Λ (U.X i)
      let G := upperStar Λ.X (U.f i)
      refine ⟨(DerivedCategory.TStructure.t.truncLE n).obj P,
        (perfect_truncations hΛ.1 hΛ.2.1 P hP n).1, ⟨?_⟩⟩
      exact (G.mapDerivedCategoryTruncLEIso n).app K ≪≫
        (DerivedCategory.TStructure.t.truncLE n).mapIso e ≪≫
        (DerivedCategory.TStructure.t.truncLE n).mapIso (eF.app P).symm ≪≫
        ((F.mapDerivedCategoryTruncLEIso n).app P).symm ≪≫ eF.app _
    · apply (condensed_dualizable_iff_local_perfect Λ.X X hX _).mpr
      refine ⟨U, fun i ↦ ?_⟩
      obtain ⟨P, hP, ⟨e⟩⟩ := hU i
      obtain ⟨ha, hl, hr, ⟨eF⟩⟩ := flat_ordinaryScalarRealization Λ hΛ.2.2 (U.X i)
      let F := ordinaryScalarRealization Λ (U.X i)
      let G := upperStar Λ.X (U.f i)
      refine ⟨(DerivedCategory.TStructure.t.truncGE n).obj P,
        (perfect_truncations hΛ.1 hΛ.2.1 P hP n).2, ⟨?_⟩⟩
      exact (G.mapDerivedCategoryTruncGEIso n).app K ≪≫
        (DerivedCategory.TStructure.t.truncGE n).mapIso e ≪≫
        (DerivedCategory.TStructure.t.truncGE n).mapIso (eF.app P).symm ≪≫
        ((F.mapDerivedCategoryTruncGEIso n).app P).symm ≪≫ eF.app _
  have hcohom (K : LisseAmbient Λ X) (hK : dualizableProperty Λ X K) (q : ℤ) :
      HasScalarLocalModels Λ X ((DerivedCategory.homologyFunctor _ q).obj K) := by
    obtain ⟨U, hU⟩ := (condensed_dualizable_iff_local_perfect Λ.X X hX K).mp hK
    refine ⟨U, fun i ↦ ?_⟩
    obtain ⟨P, hP, ⟨e⟩⟩ := hU i
    obtain ⟨ha, hl, hr, ⟨eF⟩⟩ := flat_ordinaryScalarRealization Λ hΛ.2.2 (U.X i)
    let F := ordinaryScalarRealization Λ (U.X i)
    let G := upperStar Λ.X (U.f i)
    apply (ordinaryScalarRealization_finitePresentation Λ (U.X i) _).mp
    refine ⟨(DerivedCategory.homologyFunctor _ q).obj P,
      perfect_cohomology_finitePresentation hΛ.1 hP q, ⟨?_⟩⟩
    exact (G.mapDerivedCategoryHomologyFunctorIso q).app K ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso e ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso (eF.app P).symm ≪≫
      ((F.mapDerivedCategoryHomologyFunctorIso q).app P).symm
  refine ⟨htrunc, restricted_standard_of_truncations Λ X htrunc, ?_, hcohom⟩
  intro M
  constructor
  · intro hM
    obtain ⟨U, hU⟩ := hcohom ((DerivedCategory.singleFunctor _ 0).obj M) hM 0
    refine ⟨U, fun i ↦ ?_⟩
    obtain ⟨N, hN, ⟨e⟩⟩ := hU i
    refine ⟨N, hN, ⟨?_⟩⟩
    exact (upperStar Λ.X (U.f i)).mapIso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M).symm ≪≫ e
  · rintro ⟨U, hU⟩
    apply (condensed_dualizable_iff_local_perfect Λ.X X hX _).mpr
    refine ⟨U, fun i ↦ ?_⟩
    obtain ⟨N, hN, ⟨e⟩⟩ := (ordinaryScalarRealization_finitePresentation Λ (U.X i) _).mpr
      (hU i)
    obtain ⟨ha, hl, hr, ⟨eF⟩⟩ := flat_ordinaryScalarRealization Λ hΛ.2.2 (U.X i)
    let F := ordinaryScalarRealization Λ (U.X i)
    let G := upperStar Λ.X (U.f i)
    refine ⟨(DerivedCategory.singleFunctor _ 0).obj N, hΛ.2.1 N hN, ⟨?_⟩⟩
    exact (G.mapDerivedCategorySingleFunctor 0).app M ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso e ≪≫
      ((F.mapDerivedCategorySingleFunctor 0).app N).symm ≪≫ eF.app _

end AlgebraicGeometry.ProEtale.CondensedRing
