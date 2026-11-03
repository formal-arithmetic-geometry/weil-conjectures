/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
public import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedExtensionZeroBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerOpenAdjunctionEvaluation
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageGlobalEvaluation
public import WeilConjectures.AlgebraicGeometry.Open.OpenScalarExchange
public import WeilConjectures.SixFunctors.AmbientCompositor.Operations.AmbientAdjunctionCompositorNormalization
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerDirectImageCoherence
public import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteIntrinsicPullbackUnitComposition
public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.Normalization.ExactClopenNormalization
public import WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.Open.OpenScalarRestrictionUnit
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedExtensionZeroBaseChange
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerOpenAdjunctionEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSquareExchange
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedPullbackCoherence
import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageGlobalEvaluation
import WeilConjectures.AlgebraicGeometry.Open.OpenScalarExchange
import WeilConjectures.SixFunctors.AmbientCompositor.Operations.AmbientAdjunctionCompositorNormalization
import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerDirectImageCoherence
import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
import WeilConjectures.AlgebraicGeometry.Finite.FiniteIntrinsicPullbackUnitComposition
import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.Normalization.ExactClopenNormalization
import WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.Open.OpenScalarRestrictionUnit
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerShriek
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
private theorem inverse_evaluation {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y : C} (e : X ≅ Y) {Z W : D}
    (s : F.obj X ≅ Z) (t : F.obj Y ≅ W) (b : Z ≅ W)
    (he : F.map e.hom ≫ t.hom = s.hom ≫ b.hom) :
    F.map e.inv ≫ s.hom = t.hom ≫ b.inv := by
  apply (cancel_epi (F.map e.hom)).mp
  simp only [← F.map_comp_assoc, e.hom_inv_id, F.map_id, Category.id_comp]
  rw [reassoc_of% he, b.hom_inv_id, Category.comp_id]

private theorem mate_component
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (adj : L ⊣ R) (adj' : L' ⊣ R') {G : A ⥤ C} {H : B ⥤ D}
    (s : R ⋙ G ⟶ H ⋙ R') (M : A) :
    ((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ s)).natTrans.app M =
      (adj'.homEquiv _ _).symm (G.map (adj.unit.app M) ≫ s.app (L.obj M)) := by
  apply (adj'.homEquiv _ _).injective
  erw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  exact (unit_mateEquiv_symm adj adj' (TwoSquare.mk _ _ _ _ s) M).symm

/-- Open base change on the whole ordinary unbounded tower category. `b` and `o`
are the published section-normalized coordinates for precisely these operations.
There is no boundedness, cartesianness or etale-origin condition on the input.
Source: blueprint operations proof (2) and (3)
(blueprint: lem-sp-strict-open-word-evaluation).

Proof: (1) Form the left mate using the open adjunction, applying pullback to the
open unit and then the inverse-image square compositor. Its natural transformation
is `towerOpenAlpha`; its components are `openMate`. (2) Evaluation preserves the
specified adjunction transposes, units and compositors by
lem-coef-semilinear-derived-sections. It carries this mate to the finite left mate.
Intrinsic open-mate transport and exact-localization compatibility identify the
finite mate with the inverse of canonical finite extension-by-zero base change.
The triangle identities
and uniqueness of transposes establish this identification as an equality of maps.
(3) Exact evaluations jointly detect isomorphisms on the ordinary unbounded derived
category, so the natural left mate is invertible. Define beta to be its inverse.
Functoriality of evaluation and cancellation give the final equation for beta.
This uses conservativity only for invertibility, never for equality of maps. -/
theorem towerOpenMateEvaluation (b : Base l E) (o : Operations l E b)
    {S : Scheme.{u}} (X Y : Over S)
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (c : Compactification f.left) {Y' : Scheme.{u}} (g : Y' ⟶ Y.left) :
    ∃ beta : openD l E b (o.openOp c.i) ⋙
          pull l E b (o.geometry (pullback.fst c.g g)) ≅
        pull l E b (o.geometry (pullback.fst f.left g)) ⋙
          openD l E b (o.openOp (c.baseChange g).i),
      beta.inv = towerOpenAlpha l E b o (pullback.fst f.left g)
        (c.baseChange g).i c.i (pullback.fst c.g g)
        (c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback f.left g)).w ∧
      (∀ C : D l E X.left,
        beta.inv.app C = openMate l E b o (pullback.fst f.left g)
          (c.baseChange g).i c.i (pullback.fst c.g g)
          (c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback f.left g)).w C) ∧
      (∀ (n : ℕ) (C : D l E X.left),
        (Ev l E (c.baseChange g).Z n).map (beta.inv.app C) ≫
            (towerOpenTargetEvaluation l E b o c.i (pullback.fst c.g g) n).hom.app C =
          (towerOpenSourceEvaluation l E b o (pullback.fst f.left g)
            (c.baseChange g).i n).hom.app C ≫
          (towerOpenFiniteBeta l E b (pullback.fst f.left g) (c.baseChange g).i
            c.i (pullback.fst c.g g)
            (c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback f.left g)) n).inv.app
              ((Ev l E X.left n).obj C)) ∧
      (∀ (n : ℕ) (C : D l E X.left),
        (Ev l E (c.baseChange g).Z n).map (beta.hom.app C) ≫
            (towerOpenSourceEvaluation l E b o (pullback.fst f.left g)
              (c.baseChange g).i n).hom.app C =
          (towerOpenTargetEvaluation l E b o c.i (pullback.fst c.g g) n).hom.app C ≫
          (towerOpenFiniteBeta l E b (pullback.fst f.left g) (c.baseChange g).i
            c.i (pullback.fst c.g g)
            (c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback f.left g)) n).hom.app
              ((Ev l E X.left n).obj C)) := by
  let h := pullback.fst f.left g
  let j' := (c.baseChange g).i
  let g' := pullback.fst c.g g
  let sq := c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback f.left g)
  let α := towerOpenAlpha l E b o h j' c.i g' sq.w
  have he (n : ℕ) (C : D l E X.left) :=
    towerOpenAlphaEvaluation l E b o h j' c.i g' sq n C
  have hi (C : D l E X.left) : IsIso (α.app C) := by
    apply (b.calculus (c.baseChange g).Z).detects
    intro n
    have hh := he n C
    have : IsIso ((Ev l E (c.baseChange g).Z n).map (α.app C) ≫
        (towerOpenTargetEvaluation l E b o c.i g' n).hom.app C) := by
      rw [hh]
      infer_instance
    exact (isIso_comp_right_iff _ _).mp this
  let (C : D l E X.left) : IsIso (α.app C) := hi C
  let : IsIso α := NatIso.isIso_of_isIso_app α
  refine ⟨(asIso α).symm, rfl, ?_, he, ?_⟩
  · intro C
    exact mate_component (o.openOp c.i).derivedAdjunction
      (o.openOp j').derivedAdjunction
      (square l E b o h j' c.i g' sq.w).inv C
  · intro n C
    exact inverse_evaluation (Ev l E (c.baseChange g).Z n) ((asIso α).app C)
      ((towerOpenSourceEvaluation l E b o h j' n).app C)
      ((towerOpenTargetEvaluation l E b o c.i g' n).app C)
      ((towerOpenFiniteBeta l E b h j' c.i g' sq n).symm.app
        ((Ev l E X.left n).obj C)) (he n C)

end AlgebraicGeometry.ProEtale.SpTowerShriek
