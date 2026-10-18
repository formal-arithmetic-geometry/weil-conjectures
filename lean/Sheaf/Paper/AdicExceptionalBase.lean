/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.FieldWeilShriekShiftData
public import Sheaf.SixFunctors.IntegralOperationShiftData
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SfCommonStageDirectImage
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.SfIntegralConstructibleLinear
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriek
public import Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic
public import Sheaf.Paper.SfProEtaleProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.InducedCategory

/-! # Adic exceptional adjunction and compact-support projection

Source: Bhatt--Scholze, Lemmas 6.7.2, 6.7.7, 6.7.14, 6.7.16--6.7.19,
Remark 6.8.15 (blueprint: def-per-adic-exceptional-context).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures.AdicExceptionalProjection

/-- The geometric hypotheses, bundled only to index the coherent conclusions.
Source: Bhatt--Scholze, Section 6.7 (blueprint: def-per-adic-exceptional-context). -/
structure Space (k : Type u) [Field k] where
  base : Over (Spec (.of k))
  [finiteType : LocallyOfFiniteType base.hom]
  [compact : QuasiCompact base.hom]
  [separated : IsSeparated base.hom]

attribute [instance] Space.finiteType Space.compact Space.separated

/-- The ordinary category of these schemes over the base field.
Source: Bhatt--Scholze, Section 6.7 (blueprint: def-per-adic-exceptional-context). -/
abbrev Spaces (k : Type u) [Field k] := InducedCategory (Over (Spec (.of k))) (Space.base (k := k))

variable {k : Type u} [Field k]

/-- Underlying scheme of a bundled geometric hypothesis.
Source: Section 6.7 (blueprint: def-per-adic-exceptional-context). -/
abbrev Space.scheme (X : Space k) := X.base.left

/-- The bundled scheme retains its given map to the field.
Source: Section 6.7 (blueprint: def-per-adic-exceptional-context). -/
instance spaceOver (X : Spaces k) : X.scheme.Over (Spec (.of k)) := ⟨X.base.hom⟩

/-- The underlying arrow of schemes.
Source: Section 6.7 (blueprint: def-per-adic-exceptional-context). -/
abbrev arrow {X Y : Spaces k} (f : X ⟶ Y) : X.scheme ⟶ Y.scheme := f.hom.left

/-- The arrow is over the base field.
Source: Section 6.7 (blueprint: def-per-adic-exceptional-context). -/
instance arrowOver {X Y : Spaces k} (f : X ⟶ Y) : (arrow f).IsOver (Spec (.of k)) :=
  ⟨f.hom.w⟩

/-- The finite-type structure morphism, unchanged by bundling.
Source: Section 6.7 (blueprint: def-per-adic-exceptional-context). -/
instance finiteType (X : Spaces k) : LocallyOfFiniteType (X.scheme ↘ Spec (.of k)) :=
  X.finiteType

/-- The quasi-compact structure morphism, unchanged by bundling.
Source: Section 6.7 (blueprint: def-per-adic-exceptional-context). -/
instance compact (X : Spaces k) : QuasiCompact (X.scheme ↘ Spec (.of k)) := X.compact

/-- The separated structure morphism, unchanged by bundling.
Source: Section 6.7 (blueprint: def-per-adic-exceptional-context). -/
instance separated (X : Spaces k) : IsSeparated (X.scheme ↘ Spec (.of k)) := X.separated

/-- Every base-field arrow has the required finite-type property.
Source: Section 6.7 (blueprint: def-per-adic-exceptional-context). -/
instance arrowFiniteType {X Y : Spaces k} (f : X ⟶ Y) : LocallyOfFiniteType (arrow f) :=
  @locallyOfFiniteType_of_comp _ _ _ (arrow f) (Y.scheme ↘ Spec (.of k))
    (by rw [comp_over]; infer_instance)

/-- Every base-field arrow is separated.
Source: Section 6.7 (blueprint: def-per-adic-exceptional-context). -/
instance arrowSeparated {X Y : Spaces k} (f : X ⟶ Y) : IsSeparated (arrow f) :=
  @IsSeparated.of_comp _ _ _ (arrow f) (Y.scheme ↘ Spec (.of k))
    (by rw [comp_over]; infer_instance)

/-- Every base-field arrow is quasi-compact.
Source: Section 6.7 (blueprint: def-per-adic-exceptional-context). -/
instance arrowCompact {X Y : Spaces k} (f : X ⟶ Y) : QuasiCompact (arrow f) :=
  @QuasiCompact.of_comp _ _ _ (arrow f) (Y.scheme ↘ Spec (.of k))
    (by rw [comp_over]; infer_instance) inferInstance

/-- The coefficient field hypotheses, bundled without choosing an embedding in a closure.
Source: Remark 6.8.15 (blueprint: def-per-adic-exceptional-context). -/
abbrev Coefficient (l : ℕ) [Fact l.Prime] :=
  ConstructibleExceptionalCoefficients.FieldStage.{u} l

variable (l : ℕ) [Fact l.Prime] [Fact (IsUnit (l : k))]

/-- The actual recorded complete constructible integral category.
Source: Lemma 6.7.19 (blueprint: def-per-adic-exceptional-context). -/
abbrev C (E : Coefficient.{u} l) (X : Spaces k) :=
  sfIntegralConstructibleCategory l E.carrier X.scheme

/-- Invertibility in each residue field is induced by the given base-field unit.
Source: Section 6.7 (blueprint: def-per-adic-exceptional-context). -/
@[instance_reducible] def residueInvertible (X : Spaces k) (x : X.scheme) :
    Invertible (l : X.scheme.residueField x) :=
  (Eq.mp (congrArg IsUnit (map_natCast
      ((Scheme.ΓSpecIso (.of k)).inv ≫ X.base.hom.appTop ≫ X.scheme.Γevaluation x).hom l))
    ((Fact.out : IsUnit (l : k)).map ((Scheme.ΓSpecIso (.of k)).inv ≫ X.base.hom.appTop ≫
      X.scheme.Γevaluation x).hom)).invertible


/-- Completed pullback, precisely the dependency's restriction.
Source: Lemma 6.7.2 (blueprint: def-per-adic-exceptional-context). -/
def pull (E : Coefficient.{u} l) {X Y : Spaces k} (f : X ⟶ Y) : C l E Y ⥤ C l E X :=
  letI : ∀ x : X.scheme, Invertible (l : X.scheme.residueField x) := residueInvertible l X
  letI : ∀ y : Y.scheme, Invertible (l : Y.scheme.residueField y) := residueInvertible l Y
  constructibleIntegralPullback l E.carrier (arrow f)

/-- Completed tensor, precisely the dependency's restriction.
Source: Lemma 6.7.14 (blueprint: def-per-adic-exceptional-context). -/
def tensor (E : Coefficient.{u} l) (X : Spaces k) : C l E X × C l E X ⥤ C l E X :=
  letI : ∀ x : X.scheme, Invertible (l : X.scheme.residueField x) := residueInvertible l X
  constructibleIntegralTensor l E.carrier X.scheme

/-- Compact support at a given compactification, with its published Roos normalization.
Source: Definition 6.7.6 (blueprint: def-per-adic-exceptional-context). -/
def support (E : Coefficient.{u} l) {X Y : Spaces k} (f : X ⟶ Y)
    (c : Compactification (arrow f)) : C l E X ⥤ C l E Y :=
  sfCompactSupportFiniteIntegralFunctor l k Fact.out c E.carrier

/-- Positive finite reduction, with the published intrinsic coefficient presentation.
Source: Lemma 6.7.19 (blueprint: def-per-adic-exceptional-context). -/
abbrev red (E : Coefficient.{u} l) (X : Spaces k) (n : ℕ) :=
  (sfIntegralConstructible l E.carrier X.scheme).ι ⋙
    scalarReductionDerivedExtension l E.carrier X.scheme n

/-- The specified etale exceptional adjoint transported through nu and the canonical
constant-ring equivalence. Source: Lemma 6.7.18
(blueprint: def-per-adic-exceptional-context). -/
abbrev finiteExceptional (E : Coefficient.{u} l) {X Y : Spaces k} (f : X ⟶ Y)
    (c : Compactification (arrow f)) (n : ℕ) :=
  ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing l E.carrier (n + 1)) c

/-- Pullback has the representative-normalized shift of the recorded restriction.
Source: Stacks 099N(5) (blueprint: def-per-adic-exceptional-context). -/
@[instance_reducible]
def pullShift (E : Coefficient.{u} l) {X Y : Spaces k} (f : X ⟶ Y) :
    (pull l E f).CommShift ℤ :=
  letI : ∀ x : X.scheme, Invertible (l : X.scheme.residueField x) := residueInvertible l X
  letI : ∀ y : Y.scheme, Invertible (l : Y.scheme.residueField y) := residueInvertible l Y
  fieldConstructiblePullShift l E.carrier (arrow f)

/-- Support inherits exact open descent and right-derived proper shift through its
projection-normalized realization, independently of any exceptional adjoint.
Source: Bhatt--Scholze 6.7.6 (blueprint: def-per-adic-exceptional-context). -/
@[instance_reducible]
def supportShift (E : Coefficient.{u} l) {X Y : Spaces k} (f : X ⟶ Y)
    (c : Compactification (arrow f)) : (support l E f c).CommShift ℤ :=
  letI : (PurCompactSupport.image (PurCompactSupport.completed l E.carrier) c).CommShift ℤ :=
    (IntegralSystemRealization.integralShifts l E.carrier).compactSupport (arrow f) c
  letI : ((sfIntegralConstructible l E.carrier X.scheme).ι).CommShift ℤ := inferInstance
  Functor.CommShift.ofComp
    (sfQcqsCompactSupportRealization l E.carrier k (Fact.out : IsUnit (l : k)) c).symm ℤ

/-- Reduction uses the evaluation of the canonical reconstruction-adjunction shift.
Source: Stacks 0941 (blueprint: def-per-adic-exceptional-context). -/
@[instance_reducible]
def redShift (E : Coefficient.{u} l) (X : Spaces k) (n : ℕ) :
    (red l E X n).CommShift ℤ := by
  letI := IntegralSystemRealization.reductionShift l E.carrier X.scheme
  letI : (coefficientFiniteDerivedExtension l E.carrier X.scheme n).CommShift ℤ :=
    Functor.CommShift.ofIso
      ((IntegralSystemRealization.calculus l E.carrier X.scheme).reductionEvaluation n) ℤ
  exact inferInstanceAs (((sfIntegralConstructible l E.carrier X.scheme).ι ⋙
    coefficientFiniteDerivedExtension l E.carrier X.scheme n).CommShift ℤ)

/-- Finite exceptional shift is the etale right-adjunction mate, transported through
the specified comparison and intrinsic equivalences.
Source: Bhatt--Scholze 6.7.18 (blueprint: def-per-adic-exceptional-context). -/
@[instance_reducible]
def finiteExceptionalShift (E : Coefficient.{u} l) {X Y : Spaces k} (f : X ⟶ Y)
    (c : Compactification (arrow f)) (n : ℕ) :
    (finiteExceptional l E f c n).CommShift ℤ := by
  letI := c.hasCompactification
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E.carrier (n + 1))
  letI := (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A)
    (arrow f)).rightAdjointCommShift ℤ
  letI := (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A)
    Y.scheme).rightAdjointCommShift ℤ
  letI := sfIntrinsicModuleEquivalence_functor_additive
    (Padic.coefficientExtensionRing l E.carrier (n + 1)) X.scheme
  letI := sfIntrinsicModuleEquivalence_functor_additive
    (Padic.coefficientExtensionRing l E.carrier (n + 1)) Y.scheme
  letI : ((sfIntrinsicDerivedEquivalence X.scheme
      (Padic.coefficientExtensionRing l E.carrier (n + 1))).functor).CommShift ℤ := by
    change ((sfIntrinsicModuleEquivalence X.scheme
      (Padic.coefficientExtensionRing l E.carrier (n + 1))).functor.mapDerivedCategory).CommShift ℤ
    infer_instance
  letI : ((sfIntrinsicDerivedEquivalence Y.scheme
      (Padic.coefficientExtensionRing l E.carrier (n + 1))).functor).CommShift ℤ := by
    change ((sfIntrinsicModuleEquivalence Y.scheme
      (Padic.coefficientExtensionRing l E.carrier (n + 1))).functor.mapDerivedCategory).CommShift ℤ
    infer_instance
  letI := (sfIntrinsicDerivedEquivalence Y.scheme
    (Padic.coefficientExtensionRing l E.carrier (n + 1))).commShiftInverse ℤ
  dsimp [finiteExceptional, ProEtale.sfFiniteExceptional, ProEtale.sfFiniteExceptionalFixed]
  infer_instance

/-- The finite counit is the actual comparison/etale-counit/comparison-counit word.
Source: Lemma 6.7.19, proof (blueprint: def-per-adic-exceptional-context). -/
def finiteCounit (E : Coefficient.{u} l) {X Y : Spaces k} (f : X ⟶ Y)
    (c : Compactification (arrow f)) (n : ℕ)
    (hf : letI := c.hasCompactification
      Etale.HasBoundedBelowUpperShriek (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E.carrier (n + 1)))) (arrow f))
    (M : proEtaleDerivedCategory Y.scheme
      (Padic.coefficientExtensionRing l E.carrier (n + 1)))
    (hM : DerivedCategory.TStructure.t.plus
      ((sfIntrinsicDerivedEquivalence Y.scheme
        (Padic.coefficientExtensionRing l E.carrier (n + 1))).inverse.obj M)) :
    (sfAmbientCompactSupportCandidate
      (Padic.coefficientExtensionRing l E.carrier (n + 1)) c).obj
        ((finiteExceptional l E f c n).obj M) ⟶ M := by
  letI := c.hasCompactification
  let A := Padic.coefficientExtensionRing l E.carrier (n + 1)
  letI := hf
  let eY := sfIntrinsicDerivedEquivalence Y.scheme A
  let N := eY.inverse.obj M
  exact (ProEtale.sfIntrinsicCompactSupportComparison A c).hom.app
      ((ProEtale.sfFiniteExceptionalFixed A c).obj N) ≫
    eY.functor.map
      (((ProEtale.compactSupportSiteComparison
        (ULift.{u + 1} A) c).hom.app
          ⟨_, ProEtale.plus_etaleRightDerivedUpperShriek_obj (arrow f) hM⟩) ≫
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A))
          Y.scheme).mapDerivedCategory.map
          ((Etale.rightDerivedLowerShriekIso (ULift.{u + 1} A) c).hom.app _ ≫
            (Etale.rightDerivedUpperShriekAdjunction
              (ModuleCat.{u + 1} (ULift.{u + 1} A)) (arrow f)).counit.app _) ≫
        (ProEtale.derivedComparisonAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) Y.scheme).counit.app N) ≫
    eY.counitIso.hom.app M

/-- The actual ordinary completed-ring geometric adjunction.
Source: Lemma 6.7.2 (blueprint: def-per-adic-exceptional-context). -/
def ordinaryRingAdj (E : Coefficient.{u} l) {X Y : Spaces k} (f : X ⟶ Y) :=
  let R := PurCompactSupport.completed l E.carrier
  (proEtaleRingModuleAdjunction (arrow f) (R.ring Y.scheme) (R.ring X.scheme)
    (R.pull (arrow f))).mapDerivedCategoryRightDerivedAdjunction

/-- Exact integral-linear adjunction, including the shift equations for both structural
maps. Source: Lemmas 6.7.2 and 6.7.19
(blueprint: def-per-adic-exceptional-context). -/
structure ExactAdjunction (E : Coefficient.{u} l) (X Y : Spaces k)
    (F : C l E X ⥤ C l E Y) (G : C l E Y ⥤ C l E X) where
  [leftAdditive : F.Additive]
  [rightAdditive : G.Additive]
  [leftLinear : F.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
  [rightLinear : G.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
  [leftShift : F.CommShift ℤ]
  [rightShift : G.CommShift ℤ]
  leftExact : F.IsTriangulated
  rightExact : G.IsTriangulated
  adj : F ⊣ G
  rightShiftCanonical :
    letI := leftShift
    rightShift = adj.rightAdjointCommShift ℤ
  unitShift : adj.unit.CommShift ℤ
  counitShift : adj.counit.CommShift ℤ

end WeilConjectures.AdicExceptionalProjection
