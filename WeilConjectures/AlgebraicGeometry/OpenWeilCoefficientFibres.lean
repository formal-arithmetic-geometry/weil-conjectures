/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QcqsCompactSupportRealization
public import WeilConjectures.AlgebraicGeometry.AdicHeartIntrinsicFibres
public import WeilConjectures.AlgebraicGeometry.AdicPunctualWeights
public import WeilConjectures.AlgebraicGeometry.WeilCompactSupportCohomology
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Coefficient stages and fibres for open Weil extension

The existing coefficient interface of ExtensionByZeroPunctual, separated so that
its comparison lemmas can be imported without importing the main theorem.
Source: blueprint lem-zl-quasi-finite, proof (1) and (2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Qbar : Type v) [Field Qbar] [Algebra (Padic l) Qbar] [IsAlgClosure (Padic l) Qbar]
  {U₀ X₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom] [hUsep : IsSeparated U₀.hom]
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [hXsep : IsSeparated X₀.hom]
  (j₀ : U₀ ⟶ X₀) [IsOpenImmersion j₀.left]

/-- Noetherianity makes this open immersion quasi-compact; this is a consequence,
not an extra hypothesis on the open immersion.
Source: Stacks 01T6 and 01OZ (blueprint: lem-zl-extension-by-zero-punctual).
Proof: a finite-type scheme over a field is Noetherian. Every open subset of a
Noetherian space is quasi-compact. Apply this to inverse images of affine opens. -/
@[instance]
theorem zlOpen_quasiCompact : QuasiCompact j₀.left := by
  let := LocallyOfFiniteType.isLocallyNoetherian X₀.hom
  infer_instance

/-- The prescribed geometric-fibre map is an open immersion.
Source: blueprint geometric base change of open immersions
(blueprint: lem-zl-extension-by-zero-punctual).
Proof: zlFiberMap is the map of Over.pullback along Spec(k) → Spec(k₀).
Its square with j₀ is Cartesian by the pullback universal property. Open immersions
are stable under this base change. -/
@[instance]
theorem zlOpenFiber_isOpenImmersion : IsOpenImmersion (zlFiberMap D j₀) := by
  exact MorphismProperty.overPullbackMap (P := @IsOpenImmersion)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) j₀ inferInstance

attribute [local irreducible] commonStageDerivedPullback rationalDerivedPullback

/-- Forget the heart and Weil structures, retaining the literal common-stage carrier.
Source: blueprint proof (1) (blueprint: lem-zl-extension-by-zero-punctual). -/
def zlWeilHeartCarrier (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] :
    sfCommonStageWeilSheaf D l hl Y₀ Qbar ⥤
      generalAlgebraicallyClosedConstructibleCategory l Qbar (D.geometricFiber Y₀).left :=
  ObjectProperty.ι _ ⋙ sfCommonStageWeilForget D l hl Y₀ Qbar

/-- Finite-stage heart carrier, for the normalized rational compact-support comparison.
Source: blueprint proof (1) (blueprint: lem-zl-extension-by-zero-punctual). -/
def zlFiniteWeilHeartCarrier (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] :
    sfWeilSheaf D l hl Y₀ E ⥤ sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left :=
  ObjectProperty.ι _ ⋙ sfWeilForget D l hl Y₀ E

attribute [local irreducible] rationalPullbackScalarComparison operationStageTransitionIso
  StageSystem.PairCategory.mkHom commonStagePullbackComparison
attribute [local instance 5000] GeneralAlgebraicallyClosedCoefficients.stageCategory

private theorem zlTransportHom {C : Type*} [Category C] {A B A' B' : C}
    (hA : A = A') (hB : B = B') (f : A ⟶ B) (g : A' ⟶ B') (h : HEq f g) :
    eqToHom hA.symm ≫ f ≫ eqToHom hB = g := by
  subst A'
  subst B'
  simpa using eq_of_heq h

/-- Naturality of the existing finite-stage Frobenius comparison.
Source: blueprint common-stage passage in proof (1)
(blueprint: lem-zl-extension-by-zero-punctual).
Proof: the common-stage pullback is defined on common-stage representatives by the
finite pullback and its scalar comparisons. Apply its prescribed map formula to a
same-stage arrow. Both sides are its finite pullback, with the identical inclusion
associators. Naturality of the equality comparisons gives the displayed identity. -/
theorem zlWeilStageSquare_naturality (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (L : Padic.FiniteCoefficientFields l Qbar)
    (K M : sfRationalConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) (D.geometricFiber Y₀).left)
    (f : K ⟶ M) :
    (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Qbar).map
        ((GeneralAlgebraicallyClosedCoefficients.inclusion L).map f) ≫
      (sfWeilStagePullbackIdentification D l hl Y₀ Qbar L M).hom =
    (sfWeilStagePullbackIdentification D l hl Y₀ Qbar L K).hom ≫
      (GeneralAlgebraicallyClosedCoefficients.inclusion L).map
        ((sfWeilFrobeniusPullback D l hl Y₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L)).map f) := by
  let := sfWeilPrimeInvertible D l hl Y₀
  let g := (D.geometricFrobenius Y₀).hom
  let R := rationalDerivedPullback l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) g
  let S := GeneralAlgebraicallyClosedCoefficients.stageSystem l Qbar
    (D.geometricFiber Y₀).left
  let c : R ⋙ S.T (le_refl L) ≅ S.T (le_refl L) ⋙ R :=
    isoWhiskerLeft R (operationStageTransitionIso l Qbar _ L L le_rfl) ≪≫
      rationalPullbackScalarComparison l _ _
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Qbar L L le_rfl) g ≪≫
      isoWhiskerRight (operationStageTransitionIso l Qbar _ L L le_rfl).symm R
  have hc : c.hom.app K ≫ R.map ((S.T (le_refl L)).map f) ≫ c.inv.app M =
      (S.T (le_refl L)).map (R.map f) := by
    have hn := c.hom.naturality f
    dsimp only [Functor.comp_map] at hn
    rw [← reassoc_of% hn]
    simp
  have hm := (@commonStageDerivedPullback_existsUnique l _ Qbar _ _ _ _ _ g
    (sfWeilPrimeInvertible D l hl Y₀) (sfWeilPrimeInvertible D l hl Y₀)).exists.choose_spec
  have ht := zlTransportHom (hm.1 ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K))
    (hm.1 ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj M)) _ _
    (hm.2 _ _ L le_rfl le_rfl ((S.T (le_refl L)).map f))
  have same :
      (commonStagePullbackComparison l Qbar g
        ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K) L le_rfl).hom ≫
          R.map ((S.T (le_refl L)).map f) ≫
        (commonStagePullbackComparison l Qbar g
          ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj M) L le_rfl).inv =
            (S.T (le_refl L)).map (R.map f) := by
    simpa only [commonStagePullbackComparison, commonStagePullbackObject,
      GeneralAlgebraicallyClosedCoefficients.inclusion, StageSystem.ι,
      StageSystem.PairCategory.toStage, Functor.comp_obj, c, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv,
      Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatTrans.comp_app] using hc
  have he := ht.trans (congrArg
    (GeneralAlgebraicallyClosedCoefficients.ofHom
      (commonStagePullbackObject l Qbar g
        ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K))
      (commonStagePullbackObject l Qbar g
        ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj M)) L le_rfl le_rfl) same)
  apply (cancel_epi (sfWeilStagePullbackIdentification D l hl Y₀ Qbar L K).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  dsimp only [sfWeilStagePullbackIdentification, sfCommonStageWeilFrobeniusPullback,
    sfWeilFrobeniusPullback, eqToIso,
    GeneralAlgebraicallyClosedCoefficients.inclusion, StageSystem.ι]
  unfold commonStageDerivedPullback
  simpa only [commonStagePullbackObject, R, S, g,
    GeneralAlgebraicallyClosedCoefficients.ofHom,
    GeneralAlgebraicallyClosedCoefficients.inclusion, StageSystem.ι] using he

/-- The existing stage comparison, bundled naturally for the fixed-pair transport.
Source: blueprint common-stage passage in proof (1)
(blueprint: lem-zl-extension-by-zero-punctual). -/
def zlWeilStageSquare (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (L : Padic.FiniteCoefficientFields l Qbar) :
    GeneralAlgebraicallyClosedCoefficients.inclusion L ⋙
        sfCommonStageWeilFrobeniusPullback D l hl Y₀ Qbar ≅
      sfWeilFrobeniusPullback D l hl Y₀
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) ⋙
          GeneralAlgebraicallyClosedCoefficients.inclusion L :=
  NatIso.ofComponents (sfWeilStagePullbackIdentification D l hl Y₀ Qbar L)
    (fun {K M} f ↦ zlWeilStageSquare_naturality D l hl Qbar Y₀ L K M f)

/-- A finite-stage heart object is in the common-stage heart under the recorded
fixed-pair inclusion.
Source: blueprint common-stage passage in proof (1)
(blueprint: lem-zl-extension-by-zero-punctual).
Proof: each of the two standard rational classes represents the corresponding
common-stage class at its given field. Their intersection is the heart. The
fixed-pair transport has exactly that same included carrier. -/
theorem zlWeilHeartStage_mem (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (L : Padic.FiniteCoefficientFields l Qbar)
    (K : sfWeilSheaf D l hl Y₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L)) :
    sfCommonStageHeartProperty l (D.geometricFiber Y₀).left Qbar
      ((CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
        (zlWeilStageSquare D l hl Qbar Y₀ L)).obj K.obj).carrier := by
  constructor
  · exact ⟨L, K.obj.carrier, K.property.1, ⟨Iso.refl _⟩⟩
  · exact ⟨L, K.obj.carrier, K.property.2, ⟨Iso.refl _⟩⟩

/-- The literal finite-stage Weil inclusion, restricted to the two constructible
hearts. This extends the existing sfWeilStageObject action to all arrows.
(blueprint: def-zl-open-weil-coefficient-fibres).
Source: blueprint common-stage passage in proof (1)
(blueprint: lem-zl-extension-by-zero-punctual). -/
def zlWeilHeartStage (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (L : Padic.FiniteCoefficientFields l Qbar) :
    sfWeilSheaf D l hl Y₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) ⥤
      sfCommonStageWeilSheaf D l hl Y₀ Qbar :=
  ((sfCommonStageHeartProperty l (D.geometricFiber Y₀).left Qbar).inverseImage
    (sfCommonStageWeilForget D l hl Y₀ Qbar)).lift
      (ObjectProperty.ι _ ⋙ CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
        (zlWeilStageSquare D l hl Qbar Y₀ L))
      (zlWeilHeartStage_mem D l hl Qbar Y₀ L)

/-- H⁰ of the actual finite-coefficient derived point fibre, natural in Weil sheaves.
The operator on its value is localClosedFrobeniusCohomology in degree zero.
Source: blueprint proof (2) (blueprint: lem-zl-extension-by-zero-punctual). -/
def zlClosedCoefficientFiber (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) :
    sfWeilSheaf D l hl Y₀ E ⥤ ModuleCat.{u} E :=
  zlFiniteWeilHeartCarrier D l hl E Y₀ ⋙
    @rationalDerivedPullback l _ E _ _ _ _ _ (localClosedPoint D Y₀ y ι hι)
      (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl Y₀) ⋙
    pointRationalFibre D l hl E ⋙ DerivedCategory.coefficientFdCohomology E 0

/-- Punctual upper eigenvalue bound, without a mixed-filtration hypothesis.
Source: blueprint proof (2) (blueprint: lem-zl-extension-by-zero-punctual). -/
def ZlPunctualUpperBound (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (iota : Qbar ≃+* ℂ)
    (F : sfCommonStageWeilSheaf D l hl Y₀ Qbar) (w : ℝ) : Prop :=
  ∀ (y : {y : Y₀.left // y ∈ closedPoints Y₀.left}) (α : Qbar),
    SfPunctualEigenvalue D l hl Qbar Y₀ F y α →
      ‖iota α‖ ≤ (Nat.card (Y₀.left.residueField y.val) : ℝ) ^ (w / 2)

end WeilConjectures
