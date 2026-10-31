/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralTwistDerivedScalarCanonical
public import WeilConjectures.AlgebraicGeometry.PbcCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.IntegralCompactSupportUniformRestriction
public import WeilConjectures.AlgebraicGeometry.IntegralCompactSupportCoefficientComparison
import all WeilConjectures.AlgebraicGeometry.IntegralCoefficientCompletenessTransportSupplement
import WeilConjectures.AlgebraicGeometry.PbcConstructibleReductionPullback
import WeilConjectures.AlgebraicGeometry.PbcConstructibleReductionCriterion
import WeilConjectures.AlgebraicGeometry.PbcUniformReductionCriterion
import WeilConjectures.AlgebraicGeometry.IsomorphismComparisonScalarExtension
import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian

/-! # The coefficient models used by the rational purity presentation

These are the original coefficient, Tate, scalar, and completed-pullback constructions
and proved comparison lemmas, extracted with their names, statements and bodies intact.
Source: blueprint prop-pur-rational-purity-transitivity-summands, Steps 1--3.
(blueprint: def-pur-rational-purity-coefficient-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option linter.all false
set_option linter.unusedVariables false
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open WeilConjectures
open scoped TensorProduct

attribute [local instance high] Algebra.toModule ScalarLocalization.category
attribute [local irreducible] ScalarLocalization.composition ScalarLocalization.transportHom
  AlgebraicGeometry.Scheme.pbcRationalScalarHom

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The completed coefficient system already used by PBC, with its actual pullback maps.
Source: proof Step 1 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityCoefficients : PurCompactSupport.Coefficients.{u} where
  ring W := pbcAdicCompletion W (pbcIntegralDatum l E)
  pull g := cbcCompletedCoefficientIso g (pbcIntegralDatum l E)

/-- The actual proper/open compact-support composite, before restricting its domain.
Source: proof Step 1 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityCompactAmbient {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    PbcCompletedDerived X (pbcIntegralDatum l E) ⥤
      PbcCompletedDerived Y (pbcIntegralDatum l E) :=
  PurCompactSupport.image (pbcPurityCoefficients l E) c

/-- The actual completed inverse image followed by Tate tensor and [2d].
Source: proof Step 1, H_E (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityTwistedAmbient {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] :
    PbcCompletedDerived Y (pbcIntegralDatum l E) ⥤
      PbcCompletedDerived X (pbcIntegralDatum l E) :=
  pbcActualCompletedPull f (pbcIntegralDatum l E) ⋙
    pbcTateAmbient l X E (d : ℤ) ⋙ shiftFunctor _ (2 * (d : ℤ))

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]

/-- The geometric bounds and invertibility used in the PBC category notation follow
from the fixed setting, including for the empty scheme.
Source: proof Step 1 (blueprint: prop-pur-rational-purity-transitivity-summands).
Proof: finite type over the field gives Noetherianity and finite dimension by
lem-weil-pbc-finite-type-over-noetherian and lem-kun-dimension-finite-type. The
image of l is invertible in k since l differs from p; map its inverse to each stalk. -/
theorem pbcPurityGeometricBounds (hl : l ≠ D.p) (W : Scheme.{u}) [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))] :
    IsNoetherian W ∧ (∃ n : ℕ, topologicalKrullDim W ≤ (n : WithBot ℕ∞)) ∧
      ∀ x : W, IsUnit (l : W.presheaf.stalk x) := by
  let : IsLocallyNoetherian W :=
    LocallyOfFiniteType.isLocallyNoetherian (W ↘ Spec (.of D.k))
  let : CompactSpace W :=
    QuasiCompact.compactSpace_of_compactSpace (W ↘ Spec (.of D.k))
  let : IsNoetherian W := {}
  refine ⟨inferInstance, exists_topologicalKrullDim_le (W ↘ Spec (.of D.k)), ?_⟩
  have hunit : IsUnit (l : D.k) := PurCompactSupport.coefficientPrimeUnit l D hl
  intro x
  simpa only [map_natCast] using hunit.map
    (((Scheme.ΓSpecIso (.of D.k)).inv ≫ (W ↘ Spec (.of D.k)).appTop) ≫
      W.presheaf.germ ⊤ x trivial).hom

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (i : E →ₐ[Padic l] F) (W : Scheme.{u})
    [IsNoetherian W]
    [hDim : Fact (∃ n : ℕ, topologicalKrullDim W ≤ (n : WithBot ℕ∞))]
    [hInv : Fact (∀ x : W, IsUnit (l : W.presheaf.stalk x))]

/-- The coefficient transport puts a PBC lattice in the recorded intrinsic category.
Source: proof Step 1 (blueprint: prop-pur-rational-purity-transitivity-summands).
Proof: the bounded-predicate clause of purCoefficientModel identifies the two
constructible complete predicates. Invertibility in every stalk implies the same
for the global section l, by the local criterion for invertibility. Apply that
clause to the lattice's membership proof. -/
theorem pbcPurityModel_mem
    (K : PbcBoundedConstructibleComplete W (pbcIntegralDatum l E)) :
    sfIntegralConstructible l E W ((purCoefficientModel l E W).functor.obj K.obj) := by
  have hunit : IsUnit (l : Γ(W, ⊤)) := by
    apply W.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    simpa only [map_natCast] using hInv.out x
  exact (purCoefficientModel_bounded_predicate l E W hDim.out hunit K.obj).mp K.property

/-- The ordinary Tate transport round trip, fixed by identity section functions.
Source: proof Step 3 (blueprint: prop-pur-rational-purity-transitivity-summands).
Proof: expand the transported Tate tensor. The final two coefficient restrictions
are along mutually inverse ring isomorphisms. The identity section functions are
linear, natural and inverse; sectionwise faithfulness proves uniqueness. -/
theorem pbcPurityOrdinaryTateModel_existsUnique (m : ℤ) :
    ∃! e : pbcTateSheafTensor l W E m ⋙ purOrdinaryCoefficientModel l E W ≅
        purOrdinaryCoefficientModel l E W ⋙ integralSheafTwist l E W m,
      ∀ (M : pbcModules W (pbcAdicCompletion W (pbcIntegralDatum l E)))
        (U : W.ProEtᵒᵖ)
        (x : ((pbcTateSheafTensor l W E m ⋙
          purOrdinaryCoefficientModel l E W).obj M).val.obj U),
        (e.hom.app M).val.app U x = x := by
  let q := (adicLisseForget W).mapIso (purCoefficientIso l E W)
  let T := purOrdinaryCoefficientModel l E W ⋙ integralSheafTwist l E W m
  let e : pbcTateSheafTensor l W E m ⋙ purOrdinaryCoefficientModel l E W ≅ T :=
    Functor.isoWhiskerLeft T (restrictionRoundTrip q)
  have he : ∀ M U x, (e.hom.app M).val.app U x = x := by
    intros
    rfl
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  ext M U x
  exact (he' M U x).trans (he M U x).symm

/-- The identity-on-sections Tate transport used before derived localization.
Source: proof Step 3 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityOrdinaryTateModel (m : ℤ) :
    pbcTateSheafTensor l W E m ⋙ purOrdinaryCoefficientModel l E W ≅
      purOrdinaryCoefficientModel l E W ⋙ integralSheafTwist l E W m :=
  (pbcPurityOrdinaryTateModel_existsUnique l E W m).exists.choose

attribute [local irreducible] pbcPurityOrdinaryTateModel

/-- Derived Tate transport, using exactly the ordinary identity-section comparison.
Source: proof Step 3 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityTateModel (m : ℤ) :
    pbcTateAmbient l W E m ⋙ (purCoefficientModel l E W).functor ≅
      (purCoefficientModel l E W).functor ⋙
        (integralSheafTwist l E W m).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (pbcTateSheafTensor l W E m)
    (purOrdinaryCoefficientModel l E W)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (pbcPurityOrdinaryTateModel l E W m) ≪≫
      Functor.mapDerivedCategoryCompIso (purOrdinaryCoefficientModel l E W)
        (integralSheafTwist l E W m)

/-- Identify the two published ordinary scalar models on their tensor generators.
Source: proof Step 3 (blueprint: prop-pur-rational-purity-transitivity-summands).
Proof: both coefficient maps have the same finite quotient projections, hence are
equal. Both ordinary models are the sheafified balanced tensor. Sending b tensor x
to b tensor x is balanced and natural; these local generators prove uniqueness. -/
theorem pbcPurityOrdinaryScalarModel_existsUnique :
    ∃! e : integralOrdinaryScalar l E F i W ≅
        completedOrdinaryScalarExtension l E F i W,
      ∀ (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ)
        (b : (completedIntegralCommRingSheafUnrestricted l F W).obj.obj U)
        (x : M.val.obj U),
        (e.hom.app M).val.app U (integralOrdinaryTensorSection l E F i W M U b x) =
          completedScalarTensorSection l E F i W M U b x := by
  exact isomorphismScalarSheafModel_existsUnique l E F i W

/-- The ordinary tensor-generator identity between the two published presentations.
Source: proof Step 3 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityOrdinaryScalarModel :=
  (pbcPurityOrdinaryScalarModel_existsUnique l E F i W).exists.choose

/-- The derived scalar-model identification is fixed by the universal counits.
Source: proof Step 3 (blueprint: prop-pur-rational-purity-transitivity-summands).
Proof: the existing normalized derived comparison supplies existence, since its
ordinary generator comparison is the one chosen here. Its normalization writes
its composite with the counit as a composite of isomorphisms, so that counit is
invertible on every complex. Cancel it to compare any two normalized maps on
all complex representatives; localization extensionality proves uniqueness. -/
theorem pbcPurityDerivedScalarModel_existsUnique :
    ∃! e : integralOrdinaryDerivedScalar l E F i W ≅
        completedDerivedScalarExtension l E F i W,
      ∀ P : CochainComplex (integralTowerModules l E W) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit l E F i W P =
          (integralOrdinaryScalar l E F i W).mapDerivedCategoryFactors.hom.app P ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (pbcPurityOrdinaryScalarModel l E F i W)
                (.up ℤ)).hom.app P) := by
  obtain ⟨e, he, _⟩ := isomorphismScalarModel_existsUnique l E F i W
  have hep (P : CochainComplex (integralTowerModules l E W) ℤ) :
      e.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit l E F i W P =
        (integralOrdinaryScalar l E F i W).mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (pbcPurityOrdinaryScalarModel l E F i W)
              (.up ℤ)).hom.app P) := by
    exact he.1 P
  refine ⟨e, hep, ?_⟩
  intro e' he'
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso _ _)
  intro P
  have : IsIso (e.hom.app (DerivedCategory.Q.obj P) ≫
      completedScalarCounit l E F i W P) := by
    rw [hep P]
    exact (((integralOrdinaryScalar l E F i W).mapDerivedCategoryFactors.app P) ≪≫
      DerivedCategory.Q.mapIso
        ((NatIso.mapHomologicalComplex (pbcPurityOrdinaryScalarModel l E F i W)
          (.up ℤ)).app P)).isIso_hom
  have : IsIso (completedScalarCounit l E F i W P) :=
    IsIso.of_isIso_comp_left (e.hom.app (DerivedCategory.Q.obj P)) _
  exact (cancel_mono (completedScalarCounit l E F i W P)).mp
    ((he' P).trans (hep P).symm)

/-- The universal-counit normalized derived scalar-model identification.
Source: proof Step 3 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityDerivedScalarModel :=
  (pbcPurityDerivedScalarModel_existsUnique l E F i W).exists.choose

attribute [local irreducible] pbcPurityTateModel pbcPurityDerivedScalarModel
  purCoefficientModel integralSheafTwist completedDerivedScalarExtension pbcTateAmbient
  purScalarModel integralTwistOrdinaryBeta

/-- The six normalized model comparisons assembled before taking components.
Source: proof Step 3 (blueprint: prop-pur-rational-purity-transitivity-summands).
Fully faithful cancellation retains the specified preimage at every lattice. -/
def pbcPurityTateScalarModel (m : ℤ) :
    ObjectProperty.ι (PbcIsBoundedConstructibleComplete W (pbcIntegralDatum l E)) ⋙
        pbcTateAmbient l W E m ⋙ pbcEmbeddingAmbientTensor l E F i W ≅
      ObjectProperty.ι (PbcIsBoundedConstructibleComplete W (pbcIntegralDatum l E)) ⋙
        pbcEmbeddingAmbientTensor l E F i W ⋙ pbcTateAmbient l W F m := by
  let I := ObjectProperty.ι (PbcIsBoundedConstructibleComplete W (pbcIntegralDatum l E))
  let PE := (purCoefficientModel l E W).functor
  let PF := (purCoefficientModel l F W).functor
  let S := pbcEmbeddingAmbientTensor l E F i W
  let TE := pbcTateAmbient l W E m
  let TF := pbcTateAmbient l W F m
  let B := (integralSheafTwist l F W m).mapDerivedCategory
  let J := (sfIntegralConstructible l E W).lift (I ⋙ PE)
    (fun M ↦ pbcPurityModel_mem l E W M)
  let e : (I ⋙ TE ⋙ S) ⋙ PF ≅ (I ⋙ S ⋙ TF) ⋙ PF :=
    Functor.isoWhiskerLeft (I ⋙ TE) (purScalarModel l E F i W) ≪≫
      Functor.isoWhiskerLeft (I ⋙ TE ⋙ PE) (pbcPurityDerivedScalarModel l E F i W) ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft I (pbcPurityTateModel l E W m))
        (completedDerivedScalarExtension l E F i W) ≪≫
      Functor.isoWhiskerLeft J (integralTwistOrdinaryBeta l E F i W m) ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft (I ⋙ PE) (pbcPurityDerivedScalarModel l E F i W).symm ≪≫
          Functor.isoWhiskerLeft I (purScalarModel l E F i W).symm) B ≪≫
      (Functor.isoWhiskerLeft (I ⋙ S) (pbcPurityTateModel l F W m)).symm
  exact Functor.fullyFaithfulCancelRight PF e

/-- Tate/scalar comparison transported from the published pure-tensor normalized beta.
The model functor is fully faithful, so its preimage retains that precise map.
Source: proof Step 3 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityTateScalarComponent (m : ℤ)
    (K : PbcBoundedConstructibleComplete W (pbcIntegralDatum l E)) :
    (pbcEmbeddingAmbientTensor l E F i W).obj ((pbcTateAmbient l W E m).obj K.obj) ≅
      (pbcTateAmbient l W F m).obj ((pbcEmbeddingAmbientTensor l E F i W).obj K.obj) :=
  (pbcPurityTateScalarModel l E F i W m).app K

private theorem purityTateScalarComponent_eq (m : ℤ)
    (K : PbcBoundedConstructibleComplete W (pbcIntegralDatum l E)) :
    pbcPurityTateScalarComponent l E F i W m K =
  (purCoefficientModel l F W).functor.preimageIso
    ((purScalarModel l E F i W).app ((pbcTateAmbient l W E m).obj K.obj) ≪≫
      (pbcPurityDerivedScalarModel l E F i W).app
        ((purCoefficientModel l E W).functor.obj ((pbcTateAmbient l W E m).obj K.obj)) ≪≫
      (completedDerivedScalarExtension l E F i W).mapIso
        ((pbcPurityTateModel l E W m).app K.obj) ≪≫
      (integralTwistOrdinaryBeta l E F i W m).app
        ⟨(purCoefficientModel l E W).functor.obj K.obj, pbcPurityModel_mem l E W K⟩ ≪≫
      (integralSheafTwist l F W m).mapDerivedCategory.mapIso
        (((pbcPurityDerivedScalarModel l E F i W).app
          ((purCoefficientModel l E W).functor.obj K.obj)).symm ≪≫
          ((purScalarModel l E F i W).app K.obj).symm) ≪≫
      ((pbcPurityTateModel l F W m).app
        ((pbcEmbeddingAmbientTensor l E F i W).obj K.obj)).symm) := by
  rfl

attribute [local irreducible] pbcPurityTateScalarModel

attribute [local irreducible] pbcPurityTateScalarComponent

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f) (d : ℕ)
    [IsNoetherian X] [IsNoetherian Y]
    [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
    [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
    [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

/-- Completed pullback preserves the actual integral lattice category.
Source: proof Step 1 (blueprint: prop-pur-rational-purity-transitivity-summands).
Proof: reduction commutes with completed pullback by its quotient augmentation.
Finite pullback is exact and preserves constructible finite stalks, so it preserves
the common support interval and etale origins. The strict reduction-tower formula
supplies the intrinsic completeness condition, including the zero object. -/
theorem pbcPurityPull_mem
    (K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E)) :
    PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
      ((pbcActualCompletedPull f (pbcIntegralDatum l E)).obj K.obj) := by
  let δ := pbcIntegralDatum l E
  obtain ⟨a, b, hp⟩ := (pbcUniformReductionCriterion l E Y K.obj).mp
    ⟨K.property.2.1, K.property.2.2⟩
  have hb : ∀ (n : ℕ) (q : ℤ), (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((pbcCompletedReduction Y δ n).obj K.obj)) := by
    intro n q hq
    let R := pbcRestrict (pbcLevelConstantComparison Y δ n).hom
    have := (hp n).1
    have := (hp n).2.1
    have hz : IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((pbcConstantReduction Y δ n).obj K.obj)) := by
      rcases hq with hq | hq
      · exact DerivedCategory.isZero_of_isGE _ a q hq
      · exact DerivedCategory.isZero_of_isLE _ b q hq
    have hz' := hz.of_iso ((R.mapDerivedCategoryHomologyFunctorIso q).app
      ((pbcCompletedReduction Y δ n).obj K.obj))
    have : R.Faithful := by
      constructor
      intro M N α β h
      apply SheafOfModules.Hom.ext
      exact (PresheafOfModules.restrictScalars _).map_injective
        (congrArg SheafOfModules.Hom.val h)
    apply (IsZero.iff_id_eq_zero _).mpr
    apply R.map_injective
    simpa using (IsZero.iff_id_eq_zero _).mp hz'
  obtain ⟨hc, hcons, hbounds⟩ := pbc_constructible_reduction_pullback l E f a b K.obj
    K.property.1 (fun n ↦ (hp n).2.2) hb
  have hstrict := (pbc_constructible_reduction_criterion l E X a b _ hbounds).mpr
    ⟨hc, hcons⟩
  let e := (pbcActualCompletedPullback_tower δ f).exists.choose.app
    ⟨K.obj, K.property.1⟩
  let := (pbcIntegralUniformComplete_isTriangulated l E X dX.out iX.out).1
  exact ObjectProperty.prop_of_iso _ e hstrict

attribute [local irreducible] pbcActualCompletedPull

end AlgebraicGeometry.Scheme
