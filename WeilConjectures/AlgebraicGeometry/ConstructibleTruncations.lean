/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedConstructibleTruncations
public import WeilConjectures.AlgebraicGeometry.SfConstructibleHeart
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
import WeilConjectures.CategoryTheory.Triangulated.TExactTruncationComparison
import WeilConjectures.AlgebraicGeometry.IsomorphismFieldTransport
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Constructible truncations and the retained localization compatibility API

The current ordinary condensed-coefficient proposition is proved in
`WeilConjectures.AlgebraicGeometry.CondensedConstructibleTruncations`, publicly reexported here.

The declarations below retain the previously proved rational/common-stage API for its
existing consumers. Their coefficient categories come from the historical 2026-10-15
blueprint, and they are not the realization of the current ordinary-category proposition.
No historical declaration or proof is removed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v uC vC uB vB
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated AlgebraicGeometry
namespace WeilConjectures

private theorem compatibility_of_tExact
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    {B : Type uB} [Category.{vB} B] [Preadditive B] [HasZeroObject B] [HasShift B ℤ]
    [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B] [IsTriangulated B]
    (t : TStructure C) (s : TStructure B) (ht : ∀ K, t.bounded K)
    (hs : ∀ K, s.bounded K) (F : C ⥤ B)
    [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact t s] :
    ConstructibleTruncationCompatibility t s F := by
  have ht' : t.bounded = ⊤ := top_unique (fun K _ ↦ ht K)
  have hs' : s.bounded = ⊤ := top_unique (fun K _ ↦ hs K)
  constructor
  · intro m
    have h := t.texact_truncation_comparison.{uC, vC, uB, vB, uB, vB} s ht' hs' F m
    exact ⟨⟨F.eTruncLTIso t s (m + 1 : ℤ), fun K ↦ (h.1 K).1,
      fun a ha ↦ h.2.1 a ha⟩,
      ⟨F.eTruncGEIso t s m, fun K ↦ (h.1 K).2, fun a ha ↦ h.2.2.1 a ha⟩⟩
  · intro i
    exact ⟨Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (F.commShiftIso i) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft _ (F.eTruncGEIso t s i) ≪≫
          (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (F.eTruncLTIso t s (i + 1 : ℤ)) _ ≪≫
          Functor.associator _ _ _) _ ≪≫
      Functor.associator _ _ _⟩

private theorem standardClass_scalar
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (Y : Scheme.{u})
    (b : Bool) (n : ℤ) (K : sfRationalConstructibleCategory l E Y)
    (hK : sfRationalStandardClass l E Y b n K) :
    sfRationalStandardClass l L Y b n
      ((sfRationalScalarExtension l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))
        L ι).obj K) := by
  let hp := Nat.Prime.ne_zero (Fact.out : l.Prime)
  let F := sfRationalScalarExtension l E Y 0 hp L ι
  let I := sfConstructibleIntegralScalarExtension 0 l hp E L ι Y
  obtain ⟨M, hM, ⟨e⟩⟩ := hK
  refine ⟨I.obj M, ?_, ⟨F.mapIso e ≪≫ eqToIso
    ((sfRationalScalarExtension_existsUnique l E Y 0 hp L ι).exists.choose_spec.2.1 _)⟩⟩
  intro i hi
  let G := integralOrdinaryScalar l E L ι Y
  have hz := G.isZero_homologyFunctor_mapDerivedCategory_obj (hM i hi)
  exact hz.of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso
      ((sfIntegralOrdinaryComparison l E L ι Y).symm.app M))

private theorem standardClass_pullback
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {Y : Scheme.{u}} (g : Y ⟶ Y) [IsIso g]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hX hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (S : IsomorphismFieldTransportStage l E g hX hY)
    (b : Bool) (n : ℤ) (K : sfRationalConstructibleCategory l E Y)
    (hK : sfRationalStandardClass l E Y b n K) :
    sfRationalStandardClass l E Y b n ((rationalDerivedPullback l E g).obj K) := by
  let F := rationalDerivedPullback l E g
  have : F.Additive := S.rationalAdditive
  have := S.moduleAdditive
  have := S.moduleLimits
  have := S.moduleColimits
  obtain ⟨M, hM, ⟨e⟩⟩ := hK
  refine ⟨(constructibleIntegralPullback l E g).obj M, ?_,
    ⟨F.mapIso e ≪≫ eqToIso (S.rational_object _)⟩⟩
  intro i hi
  let G := ProEtale.inverseImageIntegralModules l E g
  have hz := G.isZero_homologyFunctor_mapDerivedCategory_obj (hM i hi)
  exact hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso (S.lambda.app M))

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Y : Scheme.{u}) [base : Y.Over (Spec (.of D.k))]
  [hft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [hqc : QuasiCompact (Y ↘ Spec (.of D.k))]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage stageTransition inclusion)

/-- The complete collection of standard, bounded, scalar-compatible truncations and
scheme-automorphism comparisons on the categories in the proposition. Prime-invertibility
is a conclusion witness, not an added hypothesis on the finite-type scheme.
Source: blueprint prop-constructible-truncations, all clauses
(blueprint: prop-constructible-truncations). -/
def ConstructibleTruncations
    (t : ∀ E : Index l Ω, TStructure (Stage l Ω Y E))
    (s : TStructure (generalAlgebraicallyClosedConstructibleCategory l Ω Y))
    (units : ∀ y : Y, Invertible (l : Y.residueField y)) : Prop :=
  letI := units
  (∀ (E : Index l Ω) (n : ℤ),
    (t E).le n = sfRationalStandardClass l (Coefficient.{u} l Ω E) Y true n ∧
    (t E).ge n = sfRationalStandardClass l (Coefficient.{u} l Ω E) Y false n) ∧
  (∀ n : ℤ, s.le n = sfCommonStageStandardClass l Y Ω true n ∧
    s.ge n = sfCommonStageStandardClass l Y Ω false n) ∧
  (∀ (E : Index l Ω) (K : Stage l Ω Y E), (t E).bounded K) ∧
  (∀ K, s.bounded K) ∧
  (∀ (E L : Index l Ω) (h : E ≤ L),
    ConstructibleTruncationCompatibility (t E) (t L) (stageTransition l Ω Y E L h)) ∧
  (∀ E : Index l Ω,
    ConstructibleTruncationCompatibility (t E) s
      (inclusion (l := l) (Ω := Ω) (Y := Y) E)) ∧
  (∀ (h : Y ≅ Y) (E : Index l Ω),
    ConstructibleTruncationCompatibility (t E) (t E)
      (rationalDerivedPullback l (Coefficient.{u} l Ω E) h.hom)) ∧
  (∀ h : Y ≅ Y, ConstructibleTruncationCompatibility s s
    (commonStageDerivedPullback l Ω h.hom))

include D hl base hft hqc

/-- There are the standard truncations, their canonical maps and distinguished triangles,
bounded t-structures, cohomology functors, scalar-tower and automorphism comparisons.
Source: blueprint prop-constructible-truncations, main-20261015
(blueprint: prop-constructible-truncations).

Proof:
1. lem-pod-intrinsic-standard-tstructures gives the unique bounded rational and
   common-stage t-structures with the standard classes; these are the first four clauses.
   The residue-field units come from lem-pod-isomorphism-field-transport at 𝟙 Y.
2. Finite scalar extension preserves the rational standard classes: on an integral
   representative, exact ordinary extension preserves zero homology and
   sfIntegralOrdinaryComparison identifies it with completed extension. The stage
   transitions are these scalar functors, and inclusions preserve the existential
   common-stage classes. So transitions and inclusions are t-exact.
3. For an automorphism h, lem-pod-isomorphism-field-transport gives the exact module
   inverse image with its integral comparison; it preserves both classes at finite and
   common stages, so the rational and common-stage pullbacks are t-exact.
4. For each t-exact triangulated functor, lem-pod-texact-truncation-comparison gives the
   unique truncation comparisons; whiskering them with the shift comparison gives the
   cohomology comparison. -/
theorem constructibleTruncations_exists :
    ∃ (t : ∀ E : Index l Ω, TStructure (Stage l Ω Y E))
      (s : TStructure (generalAlgebraicallyClosedConstructibleCategory l Ω Y))
      (units : ∀ y : Y, Invertible (l : Y.residueField y)),
      ConstructibleTruncations l Y Ω t s units := by
  classical
  obtain ⟨units, units', hunit⟩ := isomorphismFieldTransport D l hl Ω (𝟙 Y)
  let := units
  let t (E : Index l Ω) : TStructure (Stage l Ω Y E) :=
    sfRationalStandardTStructure l (Coefficient.{u} l Ω E) Y D hl
  let s := sfCommonStageStandardTStructure l Y Ω D hl
  have ht (E : Index l Ω) :
      (∀ n : ℤ, (t E).le n = sfRationalStandardClass l (Coefficient.{u} l Ω E) Y true n ∧
        (t E).ge n = sfRationalStandardClass l (Coefficient.{u} l Ω E) Y false n) ∧
      (∀ K, (t E).bounded K) :=
    (sfRationalStandardTStructure_existsUnique l (Coefficient.{u} l Ω E) Y D hl).exists.choose_spec
  have hs :
      (∀ n : ℤ, s.le n = sfCommonStageStandardClass l Y Ω true n ∧
        s.ge n = sfCommonStageStandardClass l Y Ω false n) ∧
      (∀ K, s.bounded K) :=
    (sfCommonStageStandardTStructure_existsUnique l Y Ω D hl).exists.choose_spec
  refine ⟨t, s, units, ?_⟩
  refine ⟨fun E ↦ (ht E).1, hs.1, fun E ↦ (ht E).2, hs.2, ?_, ?_, ?_, ?_⟩
  · intro E L h
    have hp (b : Bool) (n : ℤ) (K : Stage l Ω Y E)
        (hK : sfRationalStandardClass l (Coefficient.{u} l Ω E) Y b n K) :
        sfRationalStandardClass l (Coefficient.{u} l Ω L) Y b n
          ((stageTransition l Ω Y E L h).obj K) := by
      have he : stageTransition l Ω Y E L h =
          GeneralAlgebraicallyClosedCoefficients.transition l Ω Y E L h :=
        (GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
          l Ω Y).exists.choose_spec.1 E L h
      have ho := congrArg (fun F : Stage l Ω Y E ⥤ Stage l Ω Y L ↦ F.obj K) he
      exact ho.symm ▸ standardClass_scalar l _ _
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) Y b n K hK
    have : (stageTransition l Ω Y E L h).IsTExact (t E) (t L) := by
      constructor
      · intro K n hK
        constructor
        rw [((ht L).1 n).1]
        exact hp true n K (by simpa only [← ((ht E).1 n).1] using hK.le)
      · intro K n hK
        constructor
        rw [((ht L).1 n).2]
        exact hp false n K (by simpa only [← ((ht E).1 n).2] using hK.ge)
    exact compatibility_of_tExact (t E) (t L) (ht E).2 (ht L).2 _
  · intro E
    let J := inclusion (l := l) (Ω := Ω) (Y := Y) E
    have : J.IsTExact (t E) s := by
      constructor
      · intro K n hK
        constructor
        rw [(hs.1 n).1]
        exact ⟨E, K, (by simpa only [← ((ht E).1 n).1] using hK.le), ⟨Iso.refl _⟩⟩
      · intro K n hK
        constructor
        rw [(hs.1 n).2]
        exact ⟨E, K, (by simpa only [← ((ht E).1 n).2] using hK.ge), ⟨Iso.refl _⟩⟩
    exact compatibility_of_tExact (t E) s (ht E).2 hs.2 J
  · intro h E
    obtain ⟨iX, iY, H⟩ := isomorphismFieldTransport D l hl Ω h.hom
    have hx : iX = units := Subsingleton.elim _ _
    have hy : iY = units := Subsingleton.elim _ _
    subst iX
    subst iY
    obtain ⟨hX, hY, H, _⟩ := H
    let S := (H (Coefficient.{u} l Ω E)).1.some
    let := S.rationalShift
    have := S.rationalExact
    have : (rationalDerivedPullback l (Coefficient.{u} l Ω E) h.hom).IsTExact (t E) (t E) := by
      constructor
      · intro K n hK
        constructor
        rw [((ht E).1 n).1]
        exact standardClass_pullback l _ h.hom hX hY S true n K
          (by simpa only [← ((ht E).1 n).1] using hK.le)
      · intro K n hK
        constructor
        rw [((ht E).1 n).2]
        exact standardClass_pullback l _ h.hom hX hY S false n K
          (by simpa only [← ((ht E).1 n).2] using hK.ge)
    exact compatibility_of_tExact (t E) (t E) (ht E).2 (ht E).2 _
  · intro h
    obtain ⟨iX, iY, H⟩ := isomorphismFieldTransport D l hl Ω h.hom
    have hx : iX = units := Subsingleton.elim _ _
    have hy : iY = units := Subsingleton.elim _ _
    subst iX
    subst iY
    obtain ⟨hX, hY, _, _, S, _, _, ⟨C⟩, _⟩ := H
    let F := commonStageDerivedPullback l Ω h.hom
    let := C.shift
    have := C.exact
    have hp (b : Bool) (n : ℤ)
        (K : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
        (hK : sfCommonStageStandardClass l Y Ω b n K) :
        sfCommonStageStandardClass l Y Ω b n (F.obj K) := by
      obtain ⟨E, M, hM, ⟨e⟩⟩ := hK
      refine ⟨E, (rationalDerivedPullback l (Coefficient.{u} l Ω E) h.hom).obj M,
        standardClass_pullback l _ h.hom hX hY (S E) b n M hM, ?_⟩
      exact ⟨F.mapIso e ≪≫ (C.stageComparison E).app M⟩
    have : F.IsTExact s s := by
      constructor
      · intro K n hK
        constructor
        rw [(hs.1 n).1]
        exact hp true n K (by simpa only [← (hs.1 n).1] using hK.le)
      · intro K n hK
        constructor
        rw [(hs.1 n).2]
        exact hp false n K (by simpa only [← (hs.1 n).2] using hK.ge)
    exact compatibility_of_tExact s s hs.2 hs.2 F

end WeilConjectures
