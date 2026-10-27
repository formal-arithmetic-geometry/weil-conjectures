/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.Paper.AdicPunctualWeights
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.SfConstructibleHeart
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.Paper.LisseAdicFiberFunctors
public import Sheaf.Paper.LisseIntegralSmallCoefficients
public import Sheaf.Paper.RationalCoefficientCategoryComparison
public import Sheaf.Paper.LocalFrobeniusTrace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.Paper.LisseRationalRealization
public import Sheaf.Paper.ContinuousRationalDerivedRealization
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.AdicHeartIntrinsicFibres
public import Sheaf.Paper.LisseCompletedSystemComparison
public import Sheaf.Paper.ContinuousCoefficientRealizations
public import Sheaf.DeligneLaumon.SmoothAffineFrontierStratification


/-! # Classical lisse strata in the raw adic heart

Source: blueprint main-20261015, thm-zl-real-mixed-by-curves, proof paragraphs 6--7
(blueprint: def-zl-raw-heart-adic-lisse-data).

## Main definitions and statement

* `Strata`: one finite heart representative, reduced lisse strata and classical systems.
* `ClassicalAt`, `ClassicalFamily`, `ClassicalCommon`: normalized realizations and maps.
* `HeartComparison`: identity-induced sf/PBC bounds, realization and fibre comparisons.
* `Frontier`, `WeilLift`: finite-field refinement and the actual restricted Weil iterate.
The existence theorem is assembled in `RawHeartAdicLisseStratification`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.RawHeartAdic

/-- Absolute separation inherited from the separated finite-type structure map.
Source: blueprint paragraph 6 (blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
abbrev baseSeparated {k : Type u} [Field k] (X : PerAdic.Base k) : X.scheme.IsSeparated :=
  Scheme.isSeparated_of_isSeparated_hom (X.scheme ↘ Spec (.of k))

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)

/-- The same finite-type geometric scheme in the recorded lisse-realization interface.
Source: blueprint proof paragraph 6 (blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
def realBase (X : PerAdic.Base D.k) : LisseRealization.Base D l hl := ⟨X.scheme⟩

/-- Invertibility inherited from the finite-field base.
Source: blueprint paragraph 6 (blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
abbrev baseInvertible (X : PerAdic.Base D.k) (x : X.scheme) :
    Invertible (l : X.scheme.residueField x) :=
  LisseRealization.baseInvertible D l hl (realBase D l hl X) x

/-- The classical-system interface with the canonical lift of the finite field.
Source: Weil II (1.1.1), BS 6.8.4; blueprint proof paragraph 6
(blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
def systemBase (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : PerAdic.Base D.k) :
    ProEtale.CompletedLisse.Base.{u} l where
  E := ULift.{u + 1} E
  field := inferInstance
  algebra := inferInstance
  finiteDimensional := inferInstance
  X := X.scheme
  noetherian := inferInstance
  separated := Scheme.isSeparated_of_isSeparated_hom (X.scheme ↘ Spec (.of D.k))
  invertible := LisseRealization.baseInvertible D l hl (realBase D l hl X)

/-- The continuous-realization base has the same underlying scheme.
Source: BS 6.8.14, blueprint proof paragraph 6
(blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
def continuousBase (X : PerAdic.Base D.k) : ContinuousRational.Base.{u} l where
  scheme := X.scheme
  dimension := (PerAdic.base_geometric_properties X).2
  prime_unit x := by
    let := LisseRealization.baseInvertible D l hl (realBase D l hl X) x
    apply (isUnit_map_iff (IsLocalRing.residue (X.scheme.presheaf.stalk x)) _).mp
    simpa only [map_natCast] using
      (isUnit_of_invertible (l : X.scheme.residueField x))



/-- The derived comparison uses the dimension bound already implied by finite type.
Source: blueprint paragraph 6 (blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
abbrev baseDimension (X : PerAdic.Base D.k) :
    Fact (∃ n : ℕ, topologicalKrullDim X.scheme ≤ n) :=
  ⟨(continuousBase D l hl X).dimension⟩

/-- Local-ring invertibility inherited from the finite-field base.
Source: blueprint paragraph 6 (blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
abbrev basePrimeUnit (X : PerAdic.Base D.k) :
    Fact (∀ x : X.scheme, IsUnit (l : X.scheme.presheaf.stalk x)) :=
  ⟨(continuousBase D l hl X).prime_unit⟩

variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Canonical coefficient-size comparison: a lifted coefficient is read by `ULift.down`.
Source: BS 6.8.2, blueprint proof paragraph 6
(blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
structure CoefficientSize (X : PerAdic.Base D.k) where
  rational : rationalCoefficientSheaf l X.scheme E ≅
    ProEtale.CompletedLisse.rationalRing l (systemBase D l hl E X)
  rational_sections : ∀ (U : X.scheme.ProEtᵒᵖ)
    (s : (rationalCoefficientSheaf l X.scheme E).obj.obj U) (x : U.unop.left),
    (((rational.hom.hom.app U s).down x).down) =
      rationalCoefficientValue l E X.scheme U s x
  integral : Scheme.integralCoefficientSheaf l X.scheme E ≅
    ProEtale.lisseIntegerSheafSized l (ULift.{u + 1} E) X.scheme
  integral_sections : ∀ (U : X.scheme.ProEtᵒᵖ)
    (s : (Scheme.integralCoefficientSheaf l X.scheme E).obj.obj U) (x : U.unop.left),
    (((integral.hom.hom.app U s).down x).val).down =
      (integralCoefficientValue l E X.scheme U s x).val
  inclusion : integral.hom ≫
      ProEtale.lisseIntegerToFieldSized l (ULift.{u + 1} E) X.scheme =
    integralRationalCoefficientMap l E X.scheme ≫ rational.hom

/-- A small presentation of the same coefficient field and its integer ring, with
continuous-function comparisons fixed pointwise. Composing these with the recorded
`chartComparison` identifies the pulled-back condensed rings; composing the integral
comparison with the normalized completion gives exactly the finite quotient projections.
Source: BS 6.8.2 and blueprint proof paragraph 6
(blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
structure CondensedCoefficients (X : PerAdic.Base D.k) where
  coefficient : Type
  [normedField : NormedField coefficient]
  [normedAlgebra : NormedAlgebra ℚ_[l] coefficient]
  [finite : FiniteDimensional ℚ_[l] coefficient]
  [disconnected : TotallyDisconnectedSpace coefficient]
  size : E ≃ₐ[ℚ_[l]] coefficient
  integers : Padic.coefficientExtensionIntegers l E ≃+*
    ProEtale.CondensedRing.continuousIntegers l coefficient
  integer_values : ∀ x, (integers x).val = size x.val
  rational : (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (rationalCoefficientSheaf l X.scheme E) ≅ ProEtale.continuousMapRingSheaf X.scheme coefficient
  rational_sections : ∀ (U : X.scheme.ProEtᵒᵖ)
    (s : (rationalCoefficientSheaf l X.scheme E).obj.obj U) (x : U.unop.left),
    (rational.hom.hom.app U s).down x = size (rationalCoefficientValue l E X.scheme U s x)
  integral : (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (Scheme.integralCoefficientSheaf l X.scheme E) ≅
    ProEtale.continuousMapRingSheaf X.scheme
      (ProEtale.CondensedRing.continuousIntegers l coefficient)
  integral_sections : ∀ (U : X.scheme.ProEtᵒᵖ)
    (s : (Scheme.integralCoefficientSheaf l X.scheme E).obj.obj U) (x : U.unop.left),
    (integral.hom.hom.app U s).down x = integers (integralCoefficientValue l E X.scheme U s x)

attribute [instance] CondensedCoefficients.normedField CondensedCoefficients.normedAlgebra
  CondensedCoefficients.finite CondensedCoefficients.disconnected

/-- The rational condensed comparison is the actual adjoint of composition with the
profinite test projection. Its multiplicativity is `chartComparison_isMonHom`.
Source: BS 6.8.2, blueprint proof paragraph 6
(blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
def CondensedCoefficients.rationalChart {X : PerAdic.Base D.k}
    (d : CondensedCoefficients D l E X) :=
  asIso (ProEtale.chartComparison X.scheme d.coefficient)

/-- The integral condensed comparison uses the same test projection. Together with
`integer_values` and `integral_sections` this fixes every finite quotient projection.
Its multiplicativity is `chartComparison_isMonHom`.
Source: BS 6.8.2, blueprint proof paragraph 6
(blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
def CondensedCoefficients.integralChart {X : PerAdic.Base D.k}
    (d : CondensedCoefficients D l E X) :=
  asIso (ProEtale.chartComparison X.scheme
    (ProEtale.CondensedRing.continuousIntegers l d.coefficient))

/-- The classical finite-system realization into the *same* raw heart, fixed by the
completed lattice localization, including every rational morphism.
Source: Weil II (1.1.1), BS 6.8.4 and 6.8.14; blueprint proof paragraph 6
(blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
structure ClassicalAt (a : LisseRealization.Family D l hl)
    (c : ProEtale.CompletedLisse.System.{u} l) (X : PerAdic.Base D.k) where
  coefficients : CoefficientSize D l hl E X
  realization : ProEtale.CompletedLisse.RawRational l (systemBase D l hl E X) ⥤
    sfRationalConstructibleCategory l E X.scheme
  fully_faithful : realization.FullyFaithful
  lisse : ∀ F, LisseRealization.Lisse D l hl E (realBase D l hl X) (realization.obj F)
  normalized : realization ⋙ (a.realization E (realBase D l hl X)).sheaf D l hl E ≅
    (c.comparison (systemBase D l hl E X)).rationalRealization ⋙
      ObjectProperty.ι _ ⋙ pbcRestrict coefficients.rational.hom
  fibre : ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
    realization ⋙ sfAdicRationalFiber l E X.scheme x ≅
      ObjectProperty.ι _ ⋙
        @lisseRationalFiberFunctor l _ (ULift.{u + 1} E) _ _ _ X.scheme
          _ (baseSeparated X) (systemBase D l hl E X).invertible κ _ _ x ⋙
        ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} E ≃+* E).symm.toRingHom

/-- The prescribed lift of a finite coefficient inclusion.
Source: Weil II (1.1.1)d), blueprint proof paragraph 6
(blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
def systemArrow (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (i : E →ₐ[ℚ_[l]] F) {X Y : PerAdic.Base D.k} (f : Y.scheme ⟶ X.scheme) :
    ProEtale.CompletedLisse.Arrow l (systemBase D l hl E X) (systemBase D l hl F Y) :=
  { scheme := f
    coefficient :=
      { toRingHom := (ULift.ringEquiv.symm.toRingHom.comp
          (i.toRingHom.comp ULift.ringEquiv.toRingHom))
        commutes' := fun r ↦ congrArg ULift.up (i.commutes r) } }


/-- The actual projection from base change along the identity, used to compare scalar
units in the same chart coordinates. Source: BS 6.8.4 and blueprint proof paragraph 6
(blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
def identityChartProjection (X : Scheme.{u}) (U : X.ProEt) :
    (proEtaleBaseChange (𝟙 X)).obj U ⟶ U :=
  MorphismProperty.Over.homMk (pullback.fst U.hom (𝟙 X))
    (by simpa only [proEtaleBaseChange, MorphismProperty.Over.pullback_obj_hom,
      Category.comp_id] using (pullback.condition (f := U.hom) (g := 𝟙 X)))
    trivial

/-- One classical realization, commuting with arbitrary scheme pullback and finite
coefficient extension through the recorded normalized operation on finite systems.
Source: BS 6.8.4, 6.8.14--15; blueprint proof paragraphs 6--7
(blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
structure ClassicalFamily (a : LisseRealization.Family D l hl)
    (c : ProEtale.CompletedLisse.System.{u} l) where
  finite : ∀ (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (X : PerAdic.Base D.k), ClassicalAt D l hl F a c X
  pull : ∀ (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    {X Y : PerAdic.Base D.k} (f : Y.scheme ⟶ X.scheme),
    (finite F X).realization ⋙ @rationalDerivedPullback l _ F _ _ _ _ _ f
      (baseInvertible D l hl Y) (baseInvertible D l hl X) ≅
      (c.operation (systemArrow D l hl F F
        (AlgHom.id _ _) (X := X) (Y := Y) f)).raw ⋙ (finite F Y).realization
  scalar : ∀ (F G : Type u) [Field F] [Field G] [Algebra ℚ_[l] F] [Algebra ℚ_[l] G]
    [FiniteDimensional ℚ_[l] F] [FiniteDimensional ℚ_[l] G]
    (i : F →ₐ[ℚ_[l]] G) (X : PerAdic.Base D.k),
    (finite F X).realization ⋙ sfRationalScalarExtension l F X.scheme D.p hl G i ≅
      (c.operation (systemArrow D l hl F G i
        (X := X) (Y := X) (𝟙 X.scheme))).raw ⋙ (finite G X).realization

  pull_sections : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    {X Y : PerAdic.Base D.k} (f : Y.scheme ⟶ X.scheme)
    (F : ProEtale.CompletedLisse.RawRational l (systemBase D l hl A X))
    (U : X.scheme.ProEt)
    (z : ((a.realization A (realBase D l hl X)).sheaf D l hl A).obj
      ((finite A X).realization.obj F) |>.val.obj (op U)),
    (((finite A Y).normalized.hom.app
      ((c.operation (systemArrow D l hl A A (AlgHom.id _ _)
        (X := X) (Y := Y) f)).raw.obj F)).val.app
          (op ((proEtaleBaseChange f).obj U)))
      ((((a.realization A (realBase D l hl Y)).sheaf D l hl A).map
        ((pull A f).hom.app F)).val.app (op ((proEtaleBaseChange f).obj U))
          (((a.along A (X := realBase D l hl Y) (Y := realBase D l hl X) f).comparison
            ((finite A X).realization.obj F) ((finite A X).lisse F)).inv.val.app
              (op ((proEtaleBaseChange f).obj U))
            (ContinuousRational.moduleUnit f (LisseRealization.coefficientPull l A f)
              (((a.realization A (realBase D l hl X)).sheaf D l hl A).obj
                ((finite A X).realization.obj F)) U z))) =
    (((c.operation (systemArrow D l hl A A (AlgHom.id _ _)
      (X := X) (Y := Y) f)).rational.hom.app F).hom.val.app
        (op ((proEtaleBaseChange f).obj U)))
      ((((c.operation (systemArrow D l hl A A (AlgHom.id _ _)
          (X := X) (Y := Y) f)).modules.rationalUnit l
            ((c.comparison (systemBase D l hl A X)).rationalRealization.obj F)).hom.app (op U))
        (((finite A X).normalized.hom.app F).val.app (op U) z))

  scalar_sections : ∀ (A B : Type u) [Field A] [Field B] [Algebra ℚ_[l] A]
    [Algebra ℚ_[l] B] [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    (i : A →ₐ[ℚ_[l]] B) (X : PerAdic.Base D.k)
    (F : ProEtale.CompletedLisse.RawRational l (systemBase D l hl A X))
    (U : X.scheme.ProEt)
    (z : ((a.realization A (realBase D l hl X)).sheaf D l hl A).obj
      ((finite A X).realization.obj F) |>.val.obj (op U)),
    (((c.comparison (systemBase D l hl B X)).rationalRealization.obj
      ((c.operation (systemArrow D l hl A B i
        (X := X) (Y := X) (𝟙 X.scheme))).raw.obj F)).obj.val.map
        (identityChartProjection X.scheme U).op)
      ((((finite B X).normalized.hom.app
          ((c.operation (systemArrow D l hl A B i
            (X := X) (Y := X) (𝟙 X.scheme))).raw.obj F)).val.app (op U))
        ((((a.realization B (realBase D l hl X)).sheaf D l hl B).map
          ((scalar A B i X).hom.app F)).val.app (op U)
            (((a.fieldChange A B i (realBase D l hl X)).comparison
                ((finite A X).realization.obj F) ((finite A X).lisse F)).inv.val.app (op U)
              (pbcTensorSection (a.fieldChange A B i (realBase D l hl X)).coefficient
                (((a.realization A (realBase D l hl X)).sheaf D l hl A).obj
                  ((finite A X).realization.obj F)) (op U) 1 z)))) =
    (((c.operation (systemArrow D l hl A B i
      (X := X) (Y := X) (𝟙 X.scheme))).rational.hom.app F).hom.val.app
        (op ((proEtaleBaseChange (𝟙 X.scheme)).obj U)))
      ((((c.operation (systemArrow D l hl A B i
          (X := X) (Y := X) (𝟙 X.scheme))).modules.rationalUnit l
            ((c.comparison (systemBase D l hl A X)).rationalRealization.obj F)).hom.app (op U))
        (((finite A X).normalized.hom.app F).val.app (op U) z))

/-- The specified common-stage pullback, with the coefficient-prime instances inherited
from the finite-field bases. Source: blueprint proof paragraphs 6--7
(blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
abbrev pullCommon (A : Type u) [Field A] [Algebra ℚ_[l] A] [IsAlgClosure ℚ_[l] A]
    {X Y : PerAdic.Base D.k} (f : X.scheme ⟶ Y.scheme) :=
  @commonStageDerivedPullback l _ A _ _ _ _ _ f
    (baseInvertible D l hl X) (baseInvertible D l hl Y)

variable (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The classical system stage uses the recorded normalized finite-system category.
Source: Weil II (1.1.1), blueprint proof paragraph 6
(blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
abbrev ClassicalStage (X : PerAdic.Base D.k)
    (i : AlgebraicallyClosedCoefficients.Index l Ω) :=
  ProEtale.CompletedLisse.RawRational l
    (systemBase D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) X)

/-- The literal finite subfield in the canonically lifted algebraic closure.
Source: Weil II (1.1.1)d), blueprint proof paragraph 6
(blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
def liftedStage (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    Padic.FiniteCoefficientFields l (ULift.{u + 1} Ω) :=
  ⟨i.val.map (ULift.algEquiv (R := ℚ_[l])).symm.toAlgHom,
    Module.Finite.equiv (IntermediateField.equivMap i.val
      (ULift.algEquiv (R := ℚ_[l])).symm.toAlgHom).toLinearEquiv⟩

/-- The actual embedding into the lifted intermediate field, through the two canonical
coefficient-size equivalences. Source: Weil II (1.1.1)d), blueprint proof paragraph 6
(blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
def liftedStageMap (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    ULift.{u + 1} (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) →ₐ[ℚ_[l]]
      (liftedStage l Ω i).val :=
  ((IntermediateField.equivMap i.val (ULift.algEquiv (R := ℚ_[l])).symm.toAlgHom).toAlgHom.comp
    (Shrink.algEquiv ℚ_[l] i.val).toAlgHom).comp ULift.algEquiv.toAlgHom

/-- Algebraic-closure structure transported through the canonical coefficient lift.
Source: Weil II (1.1.1)d), blueprint proof paragraph 6
(blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
abbrev liftedClosure : IsAlgClosure ℚ_[l] (ULift.{u + 1} Ω) :=
  { isAlgClosed := ⟨fun p ↦ by
      let := IsAlgClosure.isAlgClosed ℚ_[l] (K := Ω)
      have h := (IsAlgClosed.splits (p.map ULift.ringEquiv.toRingHom)).map
        (ULift.ringEquiv : ULift.{u + 1} Ω ≃+* Ω).symm.toRingHom
      simpa only [Polynomial.map_map,
        RingEquiv.symm_toRingHom_comp_toRingHom, Polynomial.map_id] using h⟩
    isAlgebraic := (ULift.algEquiv (R := ℚ_[l]) (A := Ω)).symm.isAlgebraic }

/-- The recorded finite-model functor into classical algebraic coefficients, after
canonical coefficient-size transport. Source: Weil II (1.1.1)d), blueprint paragraph 6
(blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
def algebraicModelFunctor (X : PerAdic.Base D.k)
    (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    ClassicalStage D l hl Ω X i ⥤
      @LisseAlgebraicSheaf l _ X.scheme _ (baseSeparated X)
        (baseInvertible D l hl X) (ULift.{u + 1} Ω) _ _ :=
  ObjectProperty.ι _ ⋙
    @lisseRationalScalarExtension l _
      (ULift.{u + 1} (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i)) _ _ _ X.scheme
      _ (baseSeparated X) (baseInvertible D l hl X)
      (liftedStage l Ω i).val _ _ _ (liftedStageMap l Ω i) ⋙
    @lisseAlgebraicModelFunctor l _ X.scheme _ (baseSeparated X)
      (baseInvertible D l hl X) (ULift.{u + 1} Ω) _ _
      (liftedClosure l Ω) (liftedStage l Ω i)

/-- The existing classical algebraic-coefficient sheaf of the normalized finite system.
Source: Weil II (1.1.1)d), blueprint proof paragraph 6
(blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
def algebraicModel (X : PerAdic.Base D.k) (i : AlgebraicallyClosedCoefficients.Index l Ω)
    (F : ClassicalStage D l hl Ω X i) :=
  (algebraicModelFunctor D l hl Ω X i).obj F

/-- Passage to algebraic coefficients uses common-stage Hom colimits, with transitions
and associators fixed by the classical finite-system comparisons. Its realization on
objects and maps is the finite-stage one; no idempotents are adjoined.
Source: Weil II (1.1.1)d), blueprint proof paragraph 6
(blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
structure ClassicalCommon (a : LisseRealization.Family D l hl)
    (c : ProEtale.CompletedLisse.System.{u} l) (b : ClassicalFamily D l hl a c)
    (X : PerAdic.Base D.k) where
  system : StageSystem (ClassicalStage D l hl Ω X)
  transitions : ∀ {i j : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j),
    system.T h = (c.operation (systemArrow D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h)
      (X := X) (Y := X) (𝟙 X.scheme))).raw
  comparison : system.Morphism (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X.scheme)
  stages : ∀ i, comparison.Φ i =
    (b.finite (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) X).realization
  transitions_normalized : ∀ {i j : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j)
    (F : ClassicalStage D l hl Ω X i),
    HEq ((comparison.β h).hom.app F)
      ((b.scalar (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i)
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) X).hom.app F)
  fully_faithful : comparison.functor.FullyFaithful
  classicalFunctor : system.PairCategory ⥤
    @LisseAlgebraicSheaf l _ X.scheme _ (baseSeparated X)
      (baseInvertible D l hl X) (ULift.{u + 1} Ω) _ _
  classical_objects : ∀ F : system.PairCategory,
    classicalFunctor.obj F = algebraicModel D l hl Ω X F.stage F.obj
  classical_maps : ∀ (i : AlgebraicallyClosedCoefficients.Index l Ω)
    (F G : ClassicalStage D l hl Ω X i) (f : F ⟶ G),
    HEq (classicalFunctor.map ((system.ι i).map f))
      ((algebraicModelFunctor D l hl Ω X i).map f)
  classical_fully_faithful : classicalFunctor.FullyFaithful
  image_heart : ∀ F, sfCommonStageHeartProperty l X.scheme Ω (comparison.functor.obj F)
  image_lisse : ∀ F, @IsCommonStageLisse l _ Ω _ _ _ X.scheme
    (baseInvertible D l hl X) (comparison.functor.obj F)

/-- The comparison of raw hearts is the identity-induced J and its prescribed continuous
realization, not an arbitrary equivalence. Both standard halves and actual adic fibres
are identified. Source: BS 6.8.11--14; blueprint proof paragraph 6
(blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
structure HeartComparison (a : LisseRealization.Family D l hl)
    (S : FdCoefficientComparisonSystem.{u} l Ω) (r : ContinuousRational.Family.{u} l)
    (X : PerAdic.Base D.k)
    [hDim : Fact (∃ n : ℕ, topologicalKrullDim X.scheme ≤ n)]
    [hInv : Fact (∀ x : X.scheme, IsUnit (l : X.scheme.presheaf.stalk x))] where
  common_bounds : ∀ (b : Bool) (n : ℤ)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω X.scheme),
    sfCommonStageStandardClass l X.scheme Ω b n K ↔
      pbcQbarStandardClass l Ω X.scheme b n
        ((S.coefficients X.scheme).equivalence.functor.obj K)
  finite_bounds : ∀ (i : AlgebraicallyClosedCoefficients.Index l Ω) (b : Bool) (n : ℤ)
    (K : sfRationalConstructibleCategory l (pbcFiniteField.{u} l Ω i) X.scheme),
    sfRationalStandardClass l (pbcFiniteField.{u} l Ω i) X.scheme b n K ↔
      ∃ L : pbcIntegralStage l Ω X.scheme i,
        (if b then (pbcIntegralTStructure X.scheme l (pbcFiniteField.{u} l Ω i)).le n L
          else (pbcIntegralTStructure X.scheme l (pbcFiniteField.{u} l Ω i)).ge n L) ∧
        Nonempty (((S.coefficients X.scheme).stage i).rational.functor.obj K ≅
          (pbcStageLocalization l Ω X.scheme i).obj L)
  realization : ∀ i : AlgebraicallyClosedCoefficients.Index l Ω,
    ((S.coefficients X.scheme).stage i).rational.functor ⋙
      (r.realization (pbcFiniteField.{u} l Ω i)
        (continuousBase D l hl X)).J ≅
      (a.realization (pbcFiniteField.{u} l Ω i)
        (realBase D l hl X)).J
  fibres : ∀ (i : AlgebraicallyClosedCoefficients.Index l Ω)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
    ((S.coefficients X.scheme).stage i).rational.functor ⋙
      PerAdic.fiber l (pbcFiniteField.{u} l Ω i) X.scheme x ≅
    sfAdicRationalFiber l (pbcFiniteField.{u} l Ω i) X.scheme x

/-- The one coefficient stage and finite reduced partition, with actual normalized
classical systems and their raw restrictions. The integral lattice is recovered by the
recorded completion equivalence, whose reductions are the ordinary finite free quotients.
Source: BS 6.8.4, 6.8.13--14; blueprint proof paragraph 6
(blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
structure Strata (a : LisseRealization.Family D l hl)
    (c : ProEtale.CompletedLisse.System.{u} l) (b : ClassicalFamily D l hl a c)
    (X : PerAdic.Base D.k) (M : sfCommonStageHeart l X.scheme Ω) where
  stage : AlgebraicallyClosedCoefficients.Index l Ω
  finite : sfRationalHeart l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω stage) X.scheme
  representative : (GeneralAlgebraicallyClosedCoefficients.inclusion stage).obj finite.obj ≅ M.obj
  partition : Scheme.FiniteLocallyClosedStratification X.scheme
  reduced : ∀ ν : Fin partition.n, IsReduced (partition.domain ν)
  bases : Fin partition.n → PerAdic.Base D.k
  domain : ∀ ν : Fin partition.n, (bases ν).scheme = partition.domain ν
  base_map : ∀ ν : Fin partition.n,
    eqToHom (domain ν) ≫ partition.immersion ν ≫ (X.scheme ↘ Spec (.of D.k)) =
      ((bases ν).scheme ↘ Spec (.of D.k))
  model : ∀ ν : Fin partition.n,
    ProEtale.CompletedLisse.RawRational l
      (systemBase D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω stage) (bases ν))
  restriction : ∀ ν : Fin partition.n,
    (@rationalDerivedPullback l _
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω stage) _ _ _ _ _
      (eqToHom (domain ν) ≫ partition.immersion ν)
      (baseInvertible D l hl (bases ν)) (baseInvertible D l hl X)).obj finite.obj ≅
        (b.finite (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω stage)
          (bases ν)).realization.obj (model ν)

/-- The completed lisse integral lattice, with its actual compatible finite etale tower.
It is the specified inverse of reduction, rather than a choice from an existence claim.
Source: BS 6.8.4(1),(4), blueprint proof paragraph 6
(blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
def Strata.lattice {a : LisseRealization.Family D l hl}
    {c : ProEtale.CompletedLisse.System.{u} l} {b : ClassicalFamily D l hl a c}
    {X : PerAdic.Base D.k} {M : sfCommonStageHeart l X.scheme Ω}
    (s : Strata D l hl Ω a c b X M) (ν : Fin s.partition.n) :=
  (c.comparison (systemBase D l hl
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω s.stage)
      (s.bases ν))).equivalence.inverse.obj
      ⟨(s.model ν).obj.integral, (s.model ν).property⟩

/-- The completed coefficient comparison for the actual lattice: first use the
finite-quotient-normalized continuous comparison, then the coefficient-size map, then
completion of the same etale tower. Source: BS 6.8.2 and 6.8.4; blueprint paragraph 6
(blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
def ClassicalAt.completed {a : LisseRealization.Family D l hl}
    {c : ProEtale.CompletedLisse.System.{u} l} {X : PerAdic.Base D.k}
    (d : ClassicalAt D l hl E a c X) :=
  (a.realization E (realBase D l hl X)).completion ≪≫ d.coefficients.integral ≪≫
    (c.comparison (systemBase D l hl E X)).coefficientIso

/-- The finite-field model, with its specified structure map.
Source: blueprint proof paragraph 7
(blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
def finiteModel (Y₀ : Over (Spec (.of D.k₀))) (m : ℕ) (hm : 1 ≤ m) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))).obj Y₀

/-- Reduction of the actual finite-field model, as a scheme over that field.
Source: blueprint proof paragraph 7
(blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
def reducedModel (Y₀ : Over (Spec (.of D.k₀))) (m : ℕ) (hm : 1 ≤ m) :=
  Over.mk ((finiteModel D Y₀ m hm).left.nilradical.subschemeι ≫
    (finiteModel D Y₀ m hm).hom)

/-- The canonical inclusion of the reduced finite-field model.
Source: blueprint proof paragraph 7
(blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
def reductionInclusion (Y₀ : Over (Spec (.of D.k₀))) (m : ℕ) (hm : 1 ≤ m) :
    reducedModel D Y₀ m hm ⟶ finiteModel D Y₀ m hm :=
  Over.homMk (finiteModel D Y₀ m hm).left.nilradical.subschemeι (by rfl)

/-- Geometric base change from the one finite extension field.
Source: blueprint proof paragraph 7
(blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
def geometricChange (m : ℕ) (hm : 1 ≤ m) :=
  Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap (D.extensionSubfield m hm) D.k)))

/-- A descended closed frontier chain refining the selected classical-lisse partition.
All arrows are over the same finite field, and each difference is partitioned into
finitely many nonempty smooth geometrically connected affine pieces. The comparison
on each further restriction is the one in `ClassicalFamily`.
Source: blueprint proof paragraphs 6--7; Stacks Tags 0B8X, 06LH and 01ZM
(blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
structure Frontier {a : LisseRealization.Family D l hl}
    {c : ProEtale.CompletedLisse.System.{u} l} {b : ClassicalFamily D l hl a c}
    {X : PerAdic.Base D.k} {M : sfCommonStageHeart l X.scheme Ω}
    (s : Strata D l hl Ω a c b X M) (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (e : X.scheme ≅ (D.geometricFiber Y₀).left.nilradical.subscheme) where
  m : ℕ
  positive : 1 ≤ m
  geometric : (geometricChange D m positive).obj (finiteModel D Y₀ m positive) ≅
    D.geometricFiber Y₀
  geometric_projection : geometric.hom.left ≫ pullback.fst Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
    pullback.fst (finiteModel D Y₀ m positive).hom
      (Spec.map (CommRingCat.ofHom (algebraMap (D.extensionSubfield m positive) D.k))) ≫
        pullback.fst Y₀.hom (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m positive)))
  length : ℕ
  closed : Fin (length + 1) → Over (Spec (.of (D.extensionSubfield m positive)))
  reduced : ∀ i, IsReduced (closed i).left
  start : closed 0 = reducedModel D Y₀ m positive
  finish : closed (Fin.last length) = Over.mk (Scheme.emptyTo _)
  inclusion : ∀ i : Fin length, closed i.succ ⟶ closed i.castSucc
  closed_inclusion : ∀ i, IsClosedImmersion (inclusion i).left
  ambient : ∀ i, closed i ⟶ finiteModel D Y₀ m positive
  ambient_start : ambient 0 = eqToHom start ≫ reductionInclusion D Y₀ m positive
  ambient_next : ∀ i : Fin length, ambient i.succ = inclusion i ≫ ambient i.castSucc
  difference : Fin length → Over (Spec (.of (D.extensionSubfield m positive)))
  openInclusion : ∀ i : Fin length, difference i ⟶ closed i.castSucc
  open_difference : ∀ i, IsOpenImmersion (openInclusion i).left
  range_difference : ∀ i, Set.range (openInclusion i).left = (Set.range (inclusion i).left)ᶜ
  count : Fin length → ℕ
  piece : ∀ i : Fin length, Fin (count i) → Over (Spec (.of (D.extensionSubfield m positive)))
  pieceInclusion : ∀ (i : Fin length) (j : Fin (count i)), piece i j ⟶ difference i
  nonempty_piece : ∀ i j, Nonempty (piece i j).left
  reduced_piece : ∀ i j, IsReduced (piece i j).left
  affine_piece : ∀ i j, IsAffine (piece i j).left
  connected_piece : ∀ i j, GeometricallyConnected (piece i j).hom
  dimension : ∀ i : Fin length, Fin (count i) → ℕ
  smooth_piece : ∀ i j, SmoothOfRelativeDimension (dimension i j) (piece i j).hom
  clopen_piece : ∀ i j,
    IsOpenImmersion (pieceInclusion i j).left ∧ IsClosedImmersion (pieceInclusion i j).left
  cover : ∀ i, ⋃ j, Set.range (pieceInclusion i j).left = Set.univ
  disjoint : ∀ i j k, j ≠ k →
    Disjoint (Set.range (pieceInclusion i j).left) (Set.range (pieceInclusion i k).left)
  zero_dimensional : ∀ i j, dimension i j = 0 →
    Nonempty (piece i j ≅ Over.mk (𝟙 (Spec (.of (D.extensionSubfield m positive)))))
  refinement : ∀ (i : Fin length) (j : Fin (count i)),
    ∃ (ν : Fin s.partition.n)
      (h : ((geometricChange D m positive).obj (piece i j)).left ⟶ s.partition.domain ν),
      IsImmersion h ∧
      h ≫ s.partition.immersion ν ≫ e.hom ≫
          (D.geometricFiber Y₀).left.nilradical.subschemeι =
        ((geometricChange D m positive).map
          (pieceInclusion i j ≫ openInclusion i ≫ ambient i.castSucc) ≫ geometric.hom).left

/-- The genuine geometric fibre in the finite-type separated base interface.
Source: blueprint proof paragraph 7
(blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
def geometricBase (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom] :
    PerAdic.Base D.k where
  scheme := (D.geometricFiber Y₀).left
  «over» := ⟨(D.geometricFiber Y₀).hom⟩
  finiteTypeLocal := inferInstanceAs (LocallyOfFiniteType (pullback.snd Y₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  finiteTypeCompact := inferInstanceAs (QuasiCompact (pullback.snd Y₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  separated := inferInstanceAs (IsSeparated (pullback.snd Y₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- Restriction of the actual iterated Weil isomorphism along an equivariant inclusion.
The equality is inserted between the two prescribed pullback-composition comparisons.
Source: blueprint proof paragraph 7
(blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
def restrictedWeil (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (K : sfCommonStageWeilComplex D l hl Y₀ Ω) (W : PerAdic.Base D.k)
    (f : W.scheme ⟶ (D.geometricFiber Y₀).left) (g : W.scheme ⟶ W.scheme) (n : ℕ)
    (h : g ≫ f = f ≫ localPositivePower (D.geometricFrobenius Y₀).hom n) :
    (pullCommon D l hl Ω (X := W) (Y := W) g).obj
      ((pullCommon D l hl Ω (X := W) (Y := geometricBase D Y₀) f).obj K.carrier) ≅
      (pullCommon D l hl Ω (X := W) (Y := geometricBase D Y₀) f).obj K.carrier :=
  (@localQbarPullbackComposition l _ Ω _ _ _ _ _ _ g f
    (baseInvertible D l hl W) (baseInvertible D l hl W)
    (baseInvertible D l hl (geometricBase D Y₀)) K.carrier).symm ≪≫
  eqToIso (congrArg (fun t ↦
    (pullCommon D l hl Ω (X := W) (Y := geometricBase D Y₀) t).obj K.carrier) h) ≪≫
  @localQbarPullbackComposition l _ Ω _ _ _ _ _ _ f
    (localPositivePower (D.geometricFrobenius Y₀).hom n)
    (baseInvertible D l hl W) (baseInvertible D l hl (geometricBase D Y₀))
    (baseInvertible D l hl (geometricBase D Y₀)) K.carrier ≪≫
  (pullCommon D l hl Ω (X := W) (Y := geometricBase D Y₀) f).mapIso
    (localQbarWeilIterate l Ω D hl Y₀ K n)

/-- Common-stage classical pullback is the prescribed finite-stage comparison followed
by the literal stage identification, so it contains no arbitrary transport iso.
Source: BS 6.8.4 and blueprint proof paragraph 7
(blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
def classicalPullIso {a : LisseRealization.Family D l hl}
    {c : ProEtale.CompletedLisse.System.{u} l} (b : ClassicalFamily D l hl a c)
    (i : AlgebraicallyClosedCoefficients.Index l Ω) {X Y : PerAdic.Base D.k}
    (f : Y.scheme ⟶ X.scheme)
    (F : ClassicalStage D l hl Ω X i) :
    (GeneralAlgebraicallyClosedCoefficients.inclusion i).obj
      ((b.finite (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) Y).realization.obj
        ((c.operation (systemArrow D l hl
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i)
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i)
          (AlgHom.id _ _) (X := X) (Y := Y) f)).raw.obj F)) ≅
      (pullCommon D l hl Ω (X := Y) (Y := X) f).obj
        ((GeneralAlgebraicallyClosedCoefficients.inclusion i).obj
          ((b.finite (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) X).realization.obj
            F)) :=
  (GeneralAlgebraicallyClosedCoefficients.inclusion i).mapIso
    ((b.pull (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) f).app F).symm ≪≫
    (@localQbarPullbackStageIso l _ Ω _ _ _ _ _ f
      (baseInvertible D l hl Y) (baseInvertible D l hl X)
      ((GeneralAlgebraicallyClosedCoefficients.inclusion i).obj
        ((b.finite (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) X).realization.obj
          F))).symm

/-- A rational classical Weil lift on any descended locally closed piece. The two
projection identities specify geometric Frobenius on that piece. The final identity
specifies the lift of the restricted actual Weil iterate; no integral invariant lattice
is part of these data. Source: blueprint proof paragraph 7
(blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
structure WeilLift {a : LisseRealization.Family D l hl}
    {c : ProEtale.CompletedLisse.System.{u} l} {b : ClassicalFamily D l hl a c}
    {X : PerAdic.Base D.k} {M : sfCommonStageHeart l X.scheme Ω}
    (s : Strata D l hl Ω a c b X M) (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (e : X.scheme ≅ (D.geometricFiber Y₀).left)
    (K : sfCommonStageWeilComplex D l hl Y₀ Ω) (ν : Fin s.partition.n)
    (m : ℕ) (hm : 1 ≤ m)
    (V₀ : Over (Spec (.of (D.extensionSubfield m hm))))
    (W : PerAdic.Base D.k)
    (eW : W.scheme ≅ ((geometricChange D m hm).obj V₀).left)
    (j : W.scheme ⟶ (s.bases ν).scheme) where
  frobenius : W.scheme ≅ W.scheme
  model_projection : frobenius.hom ≫ eW.hom ≫
      pullback.fst V₀.hom (Spec.map (CommRingCat.ofHom
        (algebraMap (D.extensionSubfield m hm) D.k))) =
    eW.hom ≫ pullback.fst V₀.hom (Spec.map (CommRingCat.ofHom
      (algebraMap (D.extensionSubfield m hm) D.k)))
  field_projection : frobenius.hom ≫ (W.scheme ↘ Spec (.of D.k)) =
    (W.scheme ↘ Spec (.of D.k)) ≫ localPositivePower (frobeniusPointIso D).hom (m - 1)
  equivariance : frobenius.hom ≫ j ≫ eqToHom (s.domain ν) ≫
      s.partition.immersion ν ≫ e.hom =
    (j ≫ eqToHom (s.domain ν) ≫ s.partition.immersion ν ≫ e.hom) ≫
      localPositivePower (D.geometricFrobenius Y₀).hom (m - 1)
  stage : AlgebraicallyClosedCoefficients.Index l Ω
  extends_stage : s.stage ≤ stage
  model : ClassicalStage D l hl Ω W stage
  carrier : (GeneralAlgebraicallyClosedCoefficients.inclusion stage).obj
      ((b.finite (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω stage) W).realization.obj
        model) ≅
    (pullCommon D l hl Ω (X := W) (Y := geometricBase D Y₀)
      (j ≫ eqToHom (s.domain ν) ≫ s.partition.immersion ν ≫ e.hom)).obj K.carrier
  weil : (c.operation (systemArrow D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω stage)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω stage) (AlgHom.id _ _)
      (X := W) (Y := W) frobenius.hom)).raw.obj model ≅ model
  realizes_iterate : (GeneralAlgebraicallyClosedCoefficients.inclusion stage).mapIso
      ((b.finite (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω stage) W).realization.mapIso
        weil) =
    classicalPullIso D l hl Ω b stage frobenius.hom model ≪≫
      (pullCommon D l hl Ω (X := W) (Y := W) frobenius.hom).mapIso carrier ≪≫
      restrictedWeil D l hl Ω Y₀ K W
        (j ≫ eqToHom (s.domain ν) ≫ s.partition.immersion ν ≫ e.hom)
        frobenius.hom (m - 1) equivariance ≪≫ carrier.symm

/-- Normalizations of the fixed raw lisse realization, including the point square.
Its `Family.transport` square applies to every positive geometric-Frobenius power.
Source: BS 6.8.2, 6.8.4 and 6.8.15; blueprint proof paragraphs 6--7
(blueprint: lem-zl-raw-heart-adic-lisse-stratification). -/
structure Normalized (a : LisseRealization.Family D l hl) : Prop where
  pull : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    {X Y : LisseRealization.Base D l hl} (f : X.scheme ⟶ Y.scheme),
    Nonempty (LisseRealization.PullNormalized D l hl A f
      (a.realization A X) (a.realization A Y) (a.along A f))
  field : ∀ (A B : Type u) [Field A] [Field B] [Algebra ℚ_[l] A] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    (i : A →ₐ[ℚ_[l]] B) (X : LisseRealization.Base D l hl),
    Nonempty (LisseRealization.FieldNormalized D l hl A B i X
      (a.realization A X) (a.realization B X) (a.fieldChange A B i X))
  point : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A],
    Nonempty (LisseRealization.PointNormalized D l hl A
      (a.realization A (LisseRealization.point D l hl)) (a.point A))
  common : ∀ X : LisseRealization.Base D l hl,
    ∃ C : LisseRealization.CommonStage D l hl Ω a X,
      Nonempty (LisseRealization.CommonNormalized D l hl a Ω X C)

end WeilConjectures.RawHeartAdic
