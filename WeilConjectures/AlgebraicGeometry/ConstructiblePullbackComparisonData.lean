/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.ConstructibleTruncations
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientPoint
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.FieldDerivedScalarTower

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.SfConstructibleHeart
public import WeilConjectures.AlgebraicGeometry.GeneralAlgebraicallyClosedCoefficients
import Mathlib.Algebra.CharP.CharAndCard

/-! # Constructible pullback comparison data

The unchanged comparison structures and scalar predicate, separated from their proofs
for compilation. Source: Bhatt--Scholze 6.8.11(3), 6.8.14(2), 6.8.15
(blueprint: def-a1-constructible-pullback-comparison-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v uC vC uB vB uD vD uA vA

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated AlgebraicGeometry

namespace WeilConjectures

-- Keep the point targets in their published small derived Hom universe when the chart API
-- imports the residue-lisse standard-size localization instance. This preference is file-local.
attribute [local instance 2000] HasDerivedCategory.ofIsGrothendieckAbelian

attribute [local irreducible] sfRationalStandardTStructure sfCommonStageStandardTStructure
  pointRationalFibre
  DerivedCategory.TStructure.t ModuleCat.extendScalars

/-- Clause package: preservation of both standard halves, the exact restriction to
specified full hearts, and the canonical truncation and cohomology comparisons.
Source: Bhatt--Scholze 6.8.11(3), 6.8.15; BBD 1.3.3--1.3.6
(blueprint: lem-a1-constructible-pullback-t-exact). -/
structure ConstructiblePullbackComparison
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {B : Type uB} [Category.{vB} B] [Preadditive B] [HasZeroObject B] [HasShift B ℤ]
    [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B]
    (t : TStructure C) (s : TStructure B)
    (P : ObjectProperty C) (Q : ObjectProperty B) (F : C ⥤ B) where
  tExact : F.IsTExact t s
  heart : P.FullSubcategory ⥤ Q.FullSubcategory
  heart_fac : heart ⋙ Q.ι = P.ι ⋙ F
  heart_limits : PreservesFiniteLimits heart
  heart_colimits : PreservesFiniteColimits heart
  commShift : F.CommShift ℤ
  truncLE : ∀ n : ℤ, t.truncLE n ⋙ F ≅ F ⋙ s.truncLE n
  truncLE_counit : ∀ (n : ℤ) (K : C),
    (truncLE n).hom.app K ≫ (s.truncLEι n).app (F.obj K) =
      F.map ((t.truncLEι n).app K)
  truncGE : ∀ n : ℤ, t.truncGE n ⋙ F ≅ F ⋙ s.truncGE n
  truncGE_unit : ∀ (n : ℤ) (K : C),
    F.map ((t.truncGEπ n).app K) ≫ (truncGE n).hom.app K =
      (s.truncGEπ n).app (F.obj K)
  cohomology : ∀ j : ℤ, constructibleTruncationCohomology t j ⋙ F ≅
    F ⋙ constructibleTruncationCohomology s j
  cohomology_formula : ∀ (j : ℤ) (K : C),
    (cohomology j).app K =
      (fun [_cs : F.CommShift ℤ] ↦ (F.commShiftIso j).app
          ((t.truncGE j).obj ((t.truncLE j).obj K))) (_cs := commShift) ≪≫
        (shiftFunctor B j).mapIso
          ((truncGE j).app ((t.truncLE j).obj K) ≪≫
            (s.truncGE j).mapIso ((truncLE j).app K))

/-- The scalar compatibility equation for cohomology in a naturally commuting square.
Both routes start with T(F(H^j K)) and end with H^j(G(S K)).
Source: Bhatt--Scholze 6.8.14(2), common-stage convention
(blueprint: lem-a1-constructible-pullback-t-exact). -/
def ConstructiblePullbackScalarSquare
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {B : Type uB} [Category.{vB} B] [Preadditive B] [HasZeroObject B] [HasShift B ℤ]
    [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B]
    {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {A : Type uA} [Category.{vA} A] [Preadditive A] [HasZeroObject A] [HasShift A ℤ]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
    {t : TStructure C} {s : TStructure B} {r : TStructure D} {a : TStructure A}
    {P : ObjectProperty C} {Q : ObjectProperty B}
    {R : ObjectProperty D} {U : ObjectProperty A}
    {F : C ⥤ B} {G : D ⥤ A} {S : C ⥤ D} {T : B ⥤ A}
    (dF : ConstructiblePullbackComparison t s P Q F)
    (dG : ConstructiblePullbackComparison r a R U G)
    (dS : ConstructiblePullbackComparison t r P R S)
    (dT : ConstructiblePullbackComparison s a Q U T)
    (β : F ⋙ T ≅ S ⋙ G) : Prop :=
  ∀ (j : ℤ) (K : C),
    T.map ((dF.cohomology j).hom.app K) ≫
        (dT.cohomology j).hom.app (F.obj K) ≫
          (constructibleTruncationCohomology a j).map (β.hom.app K) =
      β.hom.app ((constructibleTruncationCohomology t j).obj K) ≫
        G.map ((dS.cohomology j).hom.app K) ≫
          (dG.cohomology j).hom.app (S.obj K)

/-- A prime different from the finite-field characteristic is a unit in every residue
field over its algebraic closure. Source: finite-field convention, elementary
characteristic calculation (blueprint: lem-a4-constructible-residue-prime-unit).

Proof: the cardinality of the finite base field gives characteristic p. Since l and p
are distinct primes, l is nonzero and hence a unit there. Map this unit along the
algebraic-closure inclusion, the structure morphism on global sections, and evaluation
in the residue field. Ring maps preserve natural numbers and units. No nonemptiness
or finite-type hypothesis on the scheme is needed. -/
theorem constructiblePullbackResidue_isUnit
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y : Scheme.{u}) [Y.Over (Spec (.of D.k))] (y : Y) :
    IsUnit (l : Y.residueField y) := by
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
  have hunit : IsUnit (l : D.k₀) :=
    (CharP.cast_ne_zero_of_ne_of_prime D.k₀ (Fact.out : l.Prime) hl.symm).isUnit
  let g := (Y ↘ Spec (.of D.k)) ≫ Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  simpa only [map_natCast] using
    hunit.map ((Scheme.ΓSpecIso (CommRingCat.of D.k₀)).inv ≫ g.appTop ≫
      Y.Γevaluation y).hom


variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)

-- This cached inverse intentionally stays folded during repeated instance comparisons.
set_option warn.classDefReducibility false in
/-- The residue-field inverse required by the recorded pullback interface. It is
constructed from the finite-field characteristic calculation, without extracting the
entire constructible-truncation package. Inverse structures are subsingletons, so
this is the same normalized inverse as in the previous interface.
Source: finite-field convention and Bhatt--Scholze 6.8.15
(blueprint: def-a1-constructible-pullback-residue-units). -/
def constructiblePullbackResidueUnits (Y : Scheme.{u})
    [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))] :
    ∀ y : Y, Invertible (l : Y.residueField y) :=
  fun y ↦ (constructiblePullbackResidue_isUnit D l hl Y y).invertible

attribute [local irreducible] constructiblePullbackResidueUnits

/-- The comparison clause at a finite coefficient field, using exactly the recorded
standard t-structures and full constructible hearts.
Source: Bhatt--Scholze 6.8.11(3), 6.8.14(2), 6.8.15
(blueprint: lem-a1-constructible-pullback-t-exact). -/
abbrev ConstructibleRationalPullbackComparison
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {W X : Scheme.{u}} [W.Over (Spec (.of D.k))] [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (h : W ⟶ X) :=
  letI := constructiblePullbackResidueUnits D l hl W
  letI := constructiblePullbackResidueUnits D l hl X
  ConstructiblePullbackComparison
    (sfRationalStandardTStructure l E X D hl) (sfRationalStandardTStructure l E W D hl)
    (sfRationalHeartProperty l E X) (sfRationalHeartProperty l E W)
    (rationalDerivedPullback l E h)

/-- The same clauses at the common-stage algebraically closed coefficient category.
The closure universe is independent of the scheme universe.
Source: Bhatt--Scholze 6.8.14(2), 6.8.15 and the common-stage convention
(blueprint: lem-a1-constructible-pullback-t-exact). -/
abbrev ConstructibleCommonStagePullbackComparison
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {W X : Scheme.{u}} [W.Over (Spec (.of D.k))] [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (h : W ⟶ X) :=
  letI := constructiblePullbackResidueUnits D l hl W
  letI := constructiblePullbackResidueUnits D l hl X
  ConstructiblePullbackComparison
    (sfCommonStageStandardTStructure l X Ω D hl)
    (sfCommonStageStandardTStructure l W Ω D hl)
    (sfCommonStageHeartProperty l X Ω) (sfCommonStageHeartProperty l W Ω)
    (commonStageDerivedPullback l Ω h)

open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion stageTransition)

/-- The complete finite-scalar and common-stage compatibility clause for the
pullback comparisons. The beta at a common-stage inclusion has the object equality
specified by the recorded pullback, so it cannot be replaced by an arbitrary map.
Source: Bhatt--Scholze 6.8.14(2), 6.8.15; common-stage coefficients
(blueprint: lem-a1-constructible-pullback-t-exact). -/
def ConstructiblePullbackScalarCompatibility
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {W X : Scheme.{u}} [W.Over (Spec (.of D.k))] [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (h : W ⟶ X) : Prop :=
  letI := constructiblePullbackResidueUnits D l hl W
  letI := constructiblePullbackResidueUnits D l hl X
  ∃ (d : ∀ E : Index l Ω,
      ConstructibleRationalPullbackComparison D l hl (Coefficient.{u} l Ω E) h)
    (e : ConstructibleCommonStagePullbackComparison D l hl Ω h),
    (∀ (E L : Index l Ω) (a : E ≤ L),
      ∃ (sX : ConstructiblePullbackComparison
          (sfRationalStandardTStructure l (Coefficient.{u} l Ω E) X D hl)
          (sfRationalStandardTStructure l (Coefficient.{u} l Ω L) X D hl)
          (sfRationalHeartProperty l (Coefficient.{u} l Ω E) X)
          (sfRationalHeartProperty l (Coefficient.{u} l Ω L) X)
          (sfRationalScalarExtension l (Coefficient.{u} l Ω E) X 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
            (coefficientInclusion l Ω E L a)))
        (sW : ConstructiblePullbackComparison
          (sfRationalStandardTStructure l (Coefficient.{u} l Ω E) W D hl)
          (sfRationalStandardTStructure l (Coefficient.{u} l Ω L) W D hl)
          (sfRationalHeartProperty l (Coefficient.{u} l Ω E) W)
          (sfRationalHeartProperty l (Coefficient.{u} l Ω L) W)
          (sfRationalScalarExtension l (Coefficient.{u} l Ω E) W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
            (coefficientInclusion l Ω E L a))),
        ConstructiblePullbackScalarSquare (d E) (d L) sX sW
          (rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
            (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L a) h)) ∧
    (∀ E : Index l Ω,
      ∃ (iX : ConstructiblePullbackComparison
          (sfRationalStandardTStructure l (Coefficient.{u} l Ω E) X D hl)
          (sfCommonStageStandardTStructure l X Ω D hl)
          (sfRationalHeartProperty l (Coefficient.{u} l Ω E) X)
          (sfCommonStageHeartProperty l X Ω)
          (inclusion (l := l) (Ω := Ω) (Y := X) E))
        (iW : ConstructiblePullbackComparison
          (sfRationalStandardTStructure l (Coefficient.{u} l Ω E) W D hl)
          (sfCommonStageStandardTStructure l W Ω D hl)
          (sfRationalHeartProperty l (Coefficient.{u} l Ω E) W)
          (sfCommonStageHeartProperty l W Ω)
          (inclusion (l := l) (Ω := Ω) (Y := W) E))
        (β : rationalDerivedPullback l (Coefficient.{u} l Ω E) h ⋙
            inclusion (l := l) (Ω := Ω) (Y := W) E ≅
          inclusion (l := l) (Ω := Ω) (Y := X) E ⋙ commonStageDerivedPullback l Ω h),
        (∀ K : Stage l Ω X E,
          β.symm.app K = eqToIso
            ((commonStageDerivedPullback_existsUnique l Ω h).exists.choose_spec.1
              ((inclusion (l := l) (Ω := Ω) (Y := X) E).obj K))) ∧
        ConstructiblePullbackScalarSquare (d E) e iX iW β)


end WeilConjectures
