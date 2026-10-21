/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.CompactSupportCoefficientAction
public import Sheaf.Paper.ConstructibleTruncations
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.Paper.PbcRationalTransport
import Sheaf.Paper.SfConstructibleHeart
import Sheaf.Paper.CommonStageCompactSupportExactness
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology

/-! # Exactness and lower bounds for field-coefficient compact support

Source: Bhatt--Scholze, Definition 6.7.6 and Lemma 6.7.7, Lemmas 6.1.11--6.1.13;
Stacks Project, Tag 0G2A, part (3)
(blueprint: lem-zl-field-shriek-lower-bound).

Both coefficient categories and all morphism actions are the recorded constructions.
The common-stage assertion applies to every normalized compact-support coefficient action.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients

open CategoryTheory.Triangulated

universe uC vC

private theorem lowerBound_of_cohomology_vanishing
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    (t : TStructure C) (K : C) (c : ℤ) (hK : t.plus K)
    (h : ∀ i : ℤ, i < c → IsZero ((constructibleTruncationCohomology t i).obj K)) :
    t.IsGE K c := by
  obtain ⟨a, ha⟩ := hK
  by_cases hac : a ≤ c
  · have aux : ∀ (b : ℤ), a ≤ b → b ≤ c → t.IsGE K b := by
      intro b hab
      induction b, hab using Int.leInduction with
      | base => exact fun _ ↦ ha
      | succ b hab ih =>
          intro hbc
          let := ih (by omega)
          have hz : IsZero ((shiftFunctor C b).obj
              ((t.truncGE b).obj ((t.truncLE b).obj K))) := h b (by omega)
          have hz' : IsZero ((t.truncGE b).obj ((t.truncLE b).obj K)) := by
            rw [IsZero.iff_id_eq_zero] at hz ⊢
            apply (shiftFunctor C b).map_injective
            rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
            exact hz
          have hzero : IsZero ((t.truncLE b).obj K) :=
            hz'.of_iso (asIso ((t.truncGEπ b).app ((t.truncLE b).obj K)))
          exact (t.isGE_iff_isZero_truncLE_obj b (b + 1) rfl K).2 hzero
    exact aux c hac le_rfl
  · let := ha
    exact t.isGE_of_ge K c a (by omega)

open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.PurCompactSupport


private theorem ambientImage_preserves_lower
    (R : Coefficients.{u}) {X Y : Scheme.{u}} {f : X ⟶ Y} (d : Compactification f)
    (K : DerivedCategory (proEtaleRingModules X (R.ring X))) (c : ℤ) [K.IsGE c] :
    ((image R d).obj K).IsGE c := by
  have := (openExtension R d.i).isGE_mapDerivedCategory_obj K c
  let P := proEtaleRingModulePullback d.g (R.ring Y) (R.ring d.Z) (R.pull d.g)
  let A := proEtaleRingDerivedAdjunction d.g (R.ring Y) (R.ring d.Z) (R.pull d.g)
  apply (DerivedCategory.TStructure.t.isGE_iff_orthogonal
    (c - 1) c (by omega) _).2
  intro L h hL
  have := hL
  have := P.isLE_mapDerivedCategory_obj L (c - 1)
  have h0 : (A.homEquiv _ _).symm h = 0 :=
    DerivedCategory.TStructure.t.zero _ (c - 1) c (by omega)
  rw [← (A.homEquiv _ _).apply_symm_apply h, h0, A.homEquiv_unit,
    CategoryTheory.Functor.map_zero, Limits.comp_zero]


private theorem cohomology_vanishing_of_lowerBound
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (t : TStructure C) (K : C) (c : ℤ) [hK : t.IsGE K c] (i : ℤ) (hi : i < c) :
    IsZero ((constructibleTruncationCohomology t i).obj K) := by
  have : t.IsGE K (i + 1) := t.isGE_of_ge K (i + 1) c (by omega)
  have h : IsZero ((t.truncLE i).obj K) :=
    t.isZero_truncLE_obj_of_isGE i (i + 1) rfl K
  exact (shiftFunctor C i).map_isZero ((t.truncGE i).map_isZero h)

private theorem finite_preserves_lower
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : Compactification f) (c : ℤ) (K : sfRationalConstructibleCategory l E X)
    [hK : (sfRationalStandardTStructure l E X D hl).IsGE K c] :
    (sfRationalStandardTStructure l E Y D hl).IsGE
      ((sfCompactSupportFiniteFunctor l D.k (coefficientPrimeUnit l D hl) d E).obj K) c := by
  have hX := (sfRationalStandardTStructure_existsUnique l E X D hl).exists.choose_spec.1
  have hY := (sfRationalStandardTStructure_existsUnique l E Y D hl).exists.choose_spec.1
  change ∀ n : ℤ,
    (sfRationalStandardTStructure l E X D hl).le n = _ ∧
      (sfRationalStandardTStructure l E X D hl).ge n = _ at hX
  change ∀ n : ℤ,
    (sfRationalStandardTStructure l E Y D hl).le n = _ ∧
      (sfRationalStandardTStructure l E Y D hl).ge n = _ at hY
  have hrep : sfRationalStandardClass l E X false c K := by
    rw [← (hX c).2, (sfRationalStandardTStructure l E X D hl).ge_iff_isGE]
    exact hK
  obtain ⟨M, hM, ⟨e⟩⟩ := hrep
  have : M.obj.IsGE c := (DerivedCategory.isGE_iff _ c).2 hM
  have hAmb := ambientImage_preserves_lower (completed l E) d M.obj c
  have : DerivedCategory.TStructure.t.IsGE
      (((sfIntegralConstructible l E X).ι ⋙ image (completed l E) d).obj M) c := hAmb
  have : ((sfCompactSupportFiniteIntegralFunctor l D.k
      (coefficientPrimeUnit l D hl) d E).obj M).obj.IsGE c :=
    DerivedCategory.TStructure.t.isGE_of_iso
      ((sfQcqsCompactSupportRealization l E D.k (coefficientPrimeUnit l D hl) d).app M) c
  rw [← (sfRationalStandardTStructure l E Y D hl).ge_iff_isGE, (hY c).2]
  refine ⟨(sfCompactSupportFiniteIntegralFunctor l D.k
    (coefficientPrimeUnit l D hl) d E).obj M, ?_, ⟨?_⟩⟩
  · exact (DerivedCategory.isGE_iff _ c).1 inferInstance
  · exact (sfCompactSupportFiniteFunctor l D.k (coefficientPrimeUnit l D hl) d E).mapIso e


private theorem finite_exact
    (l : ℕ) [Fact l.Prime] (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
    [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : Compactification f) :
    ∃ comm : (sfCompactSupportFiniteFunctor l K₀ hl d E).CommShift ℤ,
      (fun [_commInst : (sfCompactSupportFiniteFunctor l K₀ hl d E).CommShift ℤ] ↦
        (sfCompactSupportFiniteFunctor l K₀ hl d E).IsTriangulated) (_commInst := comm) := by
  let F := sfCompactSupportFiniteIntegralFunctor l K₀ hl d E
  let e := (sfQcqsCompactSupportRealization l E K₀ hl d).symm
  let : (image (completed l E) d).CommShift ℤ := imageCommShift (completed l E) d
  have : (image (completed l E) d).IsTriangulated := by
    unfold PurCompactSupport.image
    infer_instance
  let : F.CommShift ℤ := Functor.CommShift.ofComp e ℤ
  have : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofComp_compatibility e ℤ
  have : F.IsTriangulated := (Functor.isTriangulated_iff_comp_right e).2 inferInstance
  have := (sfCompactSupportFiniteIntegralFunctor_linear l K₀ hl d E).1
  have := (sfCompactSupportFiniteIntegralFunctor_linear l K₀ hl d E).2
  have h := (ScalarLocalization.transport_exact
    (Padic.coefficientExtensionIntegers l E)
    (Padic.coefficientExtensionUniformizer l E) F).2.2.2.1
  change ∃ comm : (ScalarLocalization.transport
      (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionUniformizer l E) F).CommShift ℤ, _
  obtain ⟨comm, hcomm, hnorm⟩ := h
  exact ⟨comm, hcomm⟩


private theorem common_preserves_lower
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : Compactification f)
    (S : SfCompactSupportCoefficientAction l D.k (coefficientPrimeUnit l D hl) Ω d)
    (c : ℤ) (K : generalAlgebraicallyClosedConstructibleCategory l Ω X)
    [hK : (sfCommonStageStandardTStructure l X Ω D hl).IsGE K c] :
    (sfCommonStageStandardTStructure l Y Ω D hl).IsGE (S.system.functor.obj K) c := by
  have hX := (sfCommonStageStandardTStructure_existsUnique l X Ω D hl).exists.choose_spec.1
  have hY := (sfCommonStageStandardTStructure_existsUnique l Y Ω D hl).exists.choose_spec.1
  change ∀ n : ℤ, (sfCommonStageStandardTStructure l X Ω D hl).le n = _ ∧
    (sfCommonStageStandardTStructure l X Ω D hl).ge n = _ at hX
  change ∀ n : ℤ, (sfCommonStageStandardTStructure l Y Ω D hl).le n = _ ∧
    (sfCommonStageStandardTStructure l Y Ω D hl).ge n = _ at hY
  have hrep : sfCommonStageStandardClass l X Ω false c K := by
    rw [← (hX c).2, (sfCommonStageStandardTStructure l X Ω D hl).ge_iff_isGE]
    exact hK
  obtain ⟨E, M, hM, ⟨e⟩⟩ := hrep
  let : Field (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) := inferInstance
  let : Algebra (Padic l) (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) :=
    inferInstance
  let : FiniteDimensional (Padic l)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) :=
    AlgebraicallyClosedCoefficients.coefficientFinite l Ω E
  have hE := (sfRationalStandardTStructure_existsUnique l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) X D hl).exists.choose_spec.1
  have hF := (sfRationalStandardTStructure_existsUnique l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) Y D hl).exists.choose_spec.1
  let t := sfRationalStandardTStructure l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) X D hl
  let t' := sfRationalStandardTStructure l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) Y D hl
  change ∀ n : ℤ, t.le n = _ ∧ t.ge n = _ at hE
  change ∀ n : ℤ, t'.le n = _ ∧ t'.ge n = _ at hF
  have : t.IsGE M c := by
    rw [← t.ge_iff_isGE, (hE c).2]
    exact hM
  have hbound := finite_preserves_lower D l hl
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f d c M
  rw [← (sfCommonStageStandardTStructure l Y Ω D hl).ge_iff_isGE, (hY c).2]
  refine ⟨E, (S.system.Φ E).obj M, ?_, ⟨?_⟩⟩
  · rw [S.finite_eq E, ← (hF c).2, t'.ge_iff_isGE]
    exact hbound
  · exact S.system.functor.mapIso e ≪≫ (S.system.ιCompFunctorIso E).app M



private theorem rational_bounded
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (K : sfRationalConstructibleCategory l E X) :
    (sfRationalStandardTStructure l E X D hl).bounded K :=
  (sfRationalStandardTStructure_existsUnique l E X D hl).exists.choose_spec.2 K

private theorem common_bounded
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω X) :
    (sfCommonStageStandardTStructure l X Ω D hl).bounded K :=
  (sfCommonStageStandardTStructure_existsUnique l X Ω D hl).exists.choose_spec.2 K

attribute [local irreducible] sfRationalStandardTStructure sfCommonStageStandardTStructure

-- Retain the published names of the dependent instance binders in this statement.
set_option linter.unusedVariables false in
/-- Compact support is triangulated, with coherent natural comparisons for every integer
shift, and preserves every lower cohomological bound at both field-coefficient levels.
No separatedness of the structure morphisms is required.

Source: Bhatt--Scholze, Definition 6.7.6 and Lemma 6.7.7, Lemmas 6.1.11--6.1.13;
Stacks Project, Tag 0G2A, part (3)
(blueprint: lem-zl-field-shriek-lower-bound).

Proof: the ambient compactification functor is exact open extension followed by
right derived proper image.  Its right adjoint description preserves the lower
standard t-structure bound.  The projection-normalized realization transports
this to integral constructible complexes.  Rational standard classes are the
isomorphism closure of integral representatives, and common-stage standard
classes are the isomorphism closure of finite-stage representatives.  These two
descriptions transport the bound directly to both field coefficient categories.
Boundedness and induction on the truncation degree identify vanishing below c
with the t-structure lower bound.  Exactness at a finite field stage follows by
transport through the ambient inclusion and raw scalar localization.  The
separate common-stage exactness theorem supplies coherent shift descent. -/
theorem fieldShriek_lowerBound
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [QuasiSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [QuasiSeparated (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : Compactification f) :
    (∀ E : Padic.FiniteCoefficientFields l Ω,
      (∃ comm : (sfCompactSupportFiniteFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) d
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).CommShift ℤ,
        (fun [commInst : (sfCompactSupportFiniteFunctor l D.k
            (PurCompactSupport.coefficientPrimeUnit l D hl) d
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).CommShift ℤ] ↦
          (sfCompactSupportFiniteFunctor l D.k
            (PurCompactSupport.coefficientPrimeUnit l D hl) d
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).IsTriangulated)
          (commInst := comm)) ∧
      ∀ (c : ℤ) (K : Stage l Ω X E),
        (∀ i : ℤ, i < c → IsZero ((constructibleTruncationCohomology
          (sfRationalStandardTStructure l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) X D hl) i).obj K)) →
        ∀ i : ℤ, i < c → IsZero ((constructibleTruncationCohomology
          (sfRationalStandardTStructure l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) Y D hl) i).obj
              ((sfCompactSupportFiniteFunctor l D.k
                (PurCompactSupport.coefficientPrimeUnit l D hl) d
                (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).obj K))) ∧
    (∀ S : SfCompactSupportCoefficientAction l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) Ω d,
      (∃ comm : S.system.functor.CommShift ℤ,
        (fun [commInst : S.system.functor.CommShift ℤ] ↦
          S.system.functor.IsTriangulated) (commInst := comm)) ∧
      ∀ (c : ℤ) (K : generalAlgebraicallyClosedConstructibleCategory l Ω X),
        (∀ i : ℤ, i < c → IsZero ((constructibleTruncationCohomology
          (sfCommonStageStandardTStructure l X Ω D hl) i).obj K)) →
        ∀ i : ℤ, i < c → IsZero ((constructibleTruncationCohomology
          (sfCommonStageStandardTStructure l Y Ω D hl) i).obj
            (S.system.functor.obj K))) := by
  constructor
  · intro E
    let : Field (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) := inferInstance
    let : Algebra (Padic l) (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) :=
      inferInstance
    let : FiniteDimensional (Padic l)
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) :=
      AlgebraicallyClosedCoefficients.coefficientFinite l Ω E
    refine ⟨finite_exact l D.k (coefficientPrimeUnit l D hl)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f d, ?_⟩
    intro c K hK i hi
    have hbounded := rational_bounded D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) X K
    have hge := lowerBound_of_cohomology_vanishing
        (sfRationalStandardTStructure l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) X D hl)
        K c hbounded.1 hK
    have hge' := finite_preserves_lower D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f d c K (hK := hge)
    exact cohomology_vanishing_of_lowerBound
      (sfRationalStandardTStructure l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) Y D hl) _ c i hi (hK := hge')
  · intro S
    refine ⟨sfCommonStageCompactSupport_exactness D l hl Ω f d S, ?_⟩
    · intro c K hK i hi
      have hbounded := common_bounded D l hl Ω X K
      have hge := lowerBound_of_cohomology_vanishing
        (sfCommonStageStandardTStructure l X Ω D hl) K c hbounded.1 hK
      have hge' := common_preserves_lower D l hl Ω f d S c K (hK := hge)
      exact cohomology_vanishing_of_lowerBound
        (sfCommonStageStandardTStructure l Y Ω D hl) _ c i hi (hK := hge')

end WeilConjectures
