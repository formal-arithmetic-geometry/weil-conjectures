/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstantPurityFrobenius.ConstantPurityFrobeniusSquare
public import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitPullbackData
public import WeilConjectures.SmoothPurity.Pullback.PullbackTensorCommonStageUnitCoherence
import all WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful
import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitCoreSystemNormalization
import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitCoherentSystemNormalization
import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitCommonStageNormalization

/-! # Comparison of the normalized coefficient unit and the coherent tensor unit -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Endofunctor AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompletedUnitPullback

private theorem unit_iso_of_common_system
    {C S : Type*} [Category C] [Category S]
    (R : C ⥤ S) [R.Full] [R.Faithful]
    (F : C ⥤ C) (H : S ⥤ S) (p : F ⋙ R ≅ R ⋙ H)
    (U V : C) (W : S) (d : R.obj U ≅ W) (e : R.obj V ≅ W)
    (θ : F.obj U ≅ U) (ε : F.obj V ≅ V) (δ : H.obj W ≅ W)
    (hθ : R.map θ.hom ≫ d.hom = p.hom.app U ≫ H.map d.hom ≫ δ.hom)
    (hε : R.map ε.hom ≫ e.hom = p.hom.app V ≫ H.map e.hom ≫ δ.hom) :
    ∃ b : U ≅ V, F.map b.hom ≫ ε.hom = θ.hom ≫ b.hom := by
  let b := R.preimageIso (d ≪≫ e.symm)
  have hb : R.map b.hom = d.hom ≫ e.inv := R.map_preimage _
  have hbe : R.map b.hom ≫ e.hom = d.hom := by rw [hb]; simp
  refine ⟨b, R.map_injective ?_⟩
  simp only [Functor.map_comp]
  apply (cancel_mono e.hom).1
  simp only [Category.assoc]
  rw [hε]
  have hn := p.hom.naturality b.hom
  change R.map (F.map b.hom) ≫ p.hom.app V =
    p.hom.app U ≫ H.map (R.map b.hom) at hn
  rw [reassoc_of% hn, ← H.map_comp_assoc, hbe, ← hθ]

private theorem transport_unit_square
    {C D : Type*} [Category C] [Category D]
    (I : C ⥤ D) (F : C ⥤ C) (H : D ⥤ D)
    (p : I ⋙ H ≅ F ⋙ I)
    {U V : C} (θ : F.obj U ≅ U) (ε : F.obj V ≅ V)
    (a : U ≅ V) (ha : F.map a.hom ≫ ε.hom = θ.hom ≫ a.hom) :
    H.map (I.map a.hom) ≫ (p.app V ≪≫ I.mapIso ε).hom =
      (p.app U ≪≫ I.mapIso θ).hom ≫ I.map a.hom := by
  have hn := p.hom.naturality a.hom
  change H.map (I.map a.hom) ≫ p.hom.app V =
    p.hom.app U ≫ I.map (F.map a.hom) at hn
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  rw [reassoc_of% hn, ← I.map_comp, ha, I.map_comp]

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The specified unchanged-stage image of a completed unit arrow.
Source: the rational and common-stage clauses of completed-unit-pullback-tower.
(blueprint: lem-pur-completed-unit-common-tensor-unitor) -/
def commonCoreTheta
    (c : Core l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
      (Padic.finiteCoefficientBase l Ω)) (D.geometricFrobenius X₀).hom) :
    (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).obj
      (ConstantPurityFrobenius.unit D l hl Ω (D.geometricFiber X₀).left) ≅
        ConstantPurityFrobenius.unit D l hl Ω (D.geometricFiber X₀).left := by
  let := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  let L := Padic.finiteCoefficientBase l Ω
  let E := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L
  exact sfWeilStagePullbackIdentification D l hl X₀ Ω L _ ≪≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion L).mapIso
      (eqToIso ((rationalDerivedPullback_existsUnique l E
        (D.geometricFrobenius X₀).hom).exists.choose_spec.2.1 _) ≪≫
        (sfRationalConstructibleLocalization l E (D.geometricFiber X₀).left).mapIso
          (ObjectProperty.isoMk _ c.unit))

/-- The normalized regular coefficient unit has the same Frobenius as the coherent
reconstructed tensor unit, after a unit-object comparison.

Source: Stacks 07A4 and 0941; Bhatt--Scholze, Sections 3.5 and 6.5;
completed-unit-pullback-tower, Step 6, and pullback-tensor-common-stage-unit-coherence.
(blueprint: lem-pur-completed-unit-common-tensor-unitor)

Proof: compare the regular single complex on the whole coefficient sequence site
with the tensor unit of systemClosed. Use the unit isomorphism of the normalized
ringed-site tensor model and uniqueness of the tensor-Hom left adjoint. The ordinary
pullback of this comparison intertwines the coefficient-ring multiplication with the
unit comparison of the pullback tensor functor: on a pure tensor x tensor a both maps
are multiplication by the same structural image of a. The adjunction generator
identity proves this for the specified systemMap. Quotient maps preserve multiplication
and one, so the equation holds on the whole strict system before localization.
Pass to derived systems and reconstruct. Substitute the actual normalized tensor and
pullback model equations, Core.unit_formula, and the two augmentation equations.
Naturality cancels the effective counits; the adjunction triangles identify the arrow
on the regular coefficient with Core.unit and the arrow on the reconstructed unit with
the unique tensor-unit comparison. This constructs an integral unit-object isomorphism
and its intertwining equation. Rationalize and include at the least coefficient stage.
The normalized scalar-unit comparisons and scalar naturality identify its enlarged-stage
representatives. Both unit equations at a common larger stage identify the image of the
integral comparison with the specified common-stage comparison by uniqueness. The
included integral isomorphism is a, and its included equation is the displayed one.
The argument concerns unit arrows only, has no shifted line or cohomology assertion,
and uses no joint faithfulness of arbitrary derived finite evaluations. Empty schemes
and identity coefficient extensions satisfy the same equations. -/
theorem completedUnitCommonTensorComparison
    (c : Core l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
      (Padic.finiteCoefficientBase l Ω)) (D.geometricFrobenius X₀).hom) :
    letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
    let U := ConstantPurityFrobenius.unit D l hl Ω (D.geometricFiber X₀).left
    let V := pullbackTensorCommonUnit l Ω (D.geometricFiber X₀).left
    let F := sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω
    let ε := (pullbackTensorCommonStageUnitCoherence l Ω
      (D.geometricFrobenius X₀).hom).exists.choose
    ∃ a : U ≅ V, F.map a.hom ≫ ε.hom = (commonCoreTheta D l hl X₀ Ω c).hom ≫ a.hom := by
  let := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  let X := (D.geometricFiber X₀).left
  let E := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
    (Padic.finiteCoefficientBase l Ω)
  let g := (D.geometricFrobenius X₀).hom
  let U := integralObject l E X c.admissibleX.1.1
  let V := pullbackTensorIntegralUnit l E X
  let R := integralSystemReduction l E X
  have : R.Full := (integralSystemReduction_fullyFaithful l E X).1
  have : R.Faithful := (integralSystemReduction_fullyFaithful l E X).2
  let F := constructibleIntegralPullback l E g
  let H := pullbackTensorSequenceDerived l E g
  let p := reduction_pullback l E g
  let θ : F.obj U ≅ U := ObjectProperty.isoMk _ c.unit
  let ε := (pullbackTensorIntegralUnitCoherence l E g).exists.choose
  let d := regularTensorSystemComparison l E X c.reductionX
  let e := pullbackTensorIntegralUnitReduction l E X
  have hθ : R.map θ.hom ≫ d.hom = p.hom.app U ≫ H.map d.hom ≫
      (tensorSystemPullbackUnit l E g).hom :=
    completedUnit_core_tensorSystemReduction l E X g c
  have hε : R.map ε.hom ≫ e.hom = p.hom.app V ≫ H.map e.hom ≫
      (tensorSystemPullbackUnit l E g).hom :=
    completedUnit_coherent_tensorSystemReduction l E g
  obtain ⟨a, ha⟩ := unit_iso_of_common_system R F H p U V _ d e θ ε
    (tensorSystemPullbackUnit l E g) hθ hε
  let I := tensorUnitInclusion l Ω X
  let q := tensorInclusionPullbackComparison l Ω g
  have h := transport_unit_square I F (commonStageDerivedPullback l Ω g) q θ ε a ha
  refine ⟨I.mapIso a, ?_⟩
  have he := completedUnit_commonStage_normalization l Ω g
  change (commonStageDerivedPullback l Ω g).map (I.map a.hom) ≫
    (pullbackTensorCommonStageUnitCoherence l Ω g).exists.choose.hom =
      (commonCoreTheta D l hl X₀ Ω c).hom ≫ I.map a.hom
  rw [he]
  have hc : (q.app U ≪≫ I.mapIso θ).hom = (commonCoreTheta D l hl X₀ Ω c).hom := by
    simp only [q, I, tensorInclusionPullbackComparison, tensorUnitInclusion,
      tensorCommonPullbackComparison, tensorRationalPullbackComparison,
      commonCoreTheta, sfWeilStagePullbackIdentification, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatIso.ofComponents_hom_app, Functor.comp_obj, Functor.comp_map,
      Functor.map_comp, Category.assoc]
    rfl
  rw [hc] at h
  exact h

end WeilConjectures.CompletedUnitPullback
