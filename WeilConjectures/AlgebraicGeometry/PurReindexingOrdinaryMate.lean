/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurCompletedReindexingData
import all WeilConjectures.AlgebraicGeometry.RingedOrdinaryOpenExchange

/-! # PurReindexingOrdinaryMate

Source: Stacks Project and the extracted proof of
lem-pur-isomorphism-completed-reduction-reindexing.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.privateModule false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] completedAdicChangeData completedReductionCoefficient
attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
  StrictTowerRingedSquare.exchangeModuleSquare
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
attribute [local irreducible] CochainComplex.IsKFlatIndependentCoefficients
attribute [local instance 2000] reductionModulesHasDerivedCategory reductionTowerHasDerivedCategory
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

private theorem ordinary_on_unit_normalized
    {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    {sq : ChosenCartesianSquare v p' p g} (r : StrictTowerRingedSquare sq) :
    RingedRestrictionExchange.MateUnitFormula r
      (RingedRestrictionExchange.basePull r) (RingedRestrictionExchange.upperPull r)
      (proEtaleRingModuleAdjunction g r.RY r.RY' r.cg)
      (proEtaleRingModuleAdjunction v r.RX r.RX' r.cg')
      (purReindexingTestSquare sq.w).symm (RingedRestrictionExchange.ordinary r) := by
  have hs : RingedRestrictionExchange.siteSquare (sq := sq) =
      (purReindexingTestSquare sq.w).symm := by
    apply Iso.ext
    simp only [RingedRestrictionExchange.siteSquare, purReindexingTestSquare,
      Iso.trans_inv, Iso.symm_inv, Iso.trans_hom, Iso.symm_hom,
      eqToIso.inv, eqToIso.hom, Category.assoc]
  rw [← hs]
  exact RingedRestrictionExchange.ordinary_on_unit r

private theorem completed_mate_eq
    {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare v p' p g) :
    RingedRestrictionExchange.ordinary (purReindexingRingedSquare d sq) =
      purReindexingModuleMate d sq := by
  rfl


attribute [local irreducible] RingedRestrictionExchange.ordinary purReindexingModuleMate

private theorem completed_unit_formula
    {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare v p' p g)
    (m : proEtaleRingModuleDirectImage p (d.completedRing Y) (d.completedRing X)
        (d.integralRingIso p) ⋙ proEtaleRingModulePullback g (d.completedRing Y)
        (d.completedRing Y') (d.integralRingIso g) ⟶
      proEtaleRingModulePullback v (d.completedRing X)
        (d.completedRing X') (d.integralRingIso v) ⋙
        proEtaleRingModuleDirectImage p' (d.completedRing Y') (d.completedRing X')
          (d.integralRingIso p'))
    (h : RingedRestrictionExchange.MateUnitFormula (purReindexingRingedSquare d sq)
      (proEtaleRingModulePullback g (d.completedRing Y) (d.completedRing Y')
        (d.integralRingIso g))
      (proEtaleRingModulePullback v (d.completedRing X) (d.completedRing X')
        (d.integralRingIso v))
      (proEtaleRingModuleAdjunction g (d.completedRing Y) (d.completedRing Y')
        (d.integralRingIso g))
      (proEtaleRingModuleAdjunction v (d.completedRing X) (d.completedRing X')
        (d.integralRingIso v))
      (purReindexingTestSquare sq.w).symm m) :
  (∀ (M : reductionModules X (d.completedRing X)) (V : Y.ProEt)
      (x : M.val.obj (op ((proEtaleBaseChange p).obj V))),
    (m.app M).val.app (op ((proEtaleBaseChange g).obj V))
        (((proEtaleRingModuleAdjunction g (d.completedRing Y) (d.completedRing Y')
          (d.integralRingIso g)).unit.app
            ((proEtaleRingModuleDirectImage p (d.completedRing Y) (d.completedRing X)
              (d.integralRingIso p)).obj M)).val.app (op V) x) =
      ((proEtaleRingModulePullback v (d.completedRing X)
        (d.completedRing X') (d.integralRingIso v)).obj M).val.map
        ((purReindexingTestSquare sq.w).hom.app V).op
        (((proEtaleRingModuleAdjunction v (d.completedRing X) (d.completedRing X')
          (d.integralRingIso v)).unit.app M).val.app
            (op ((proEtaleBaseChange p).obj V)) x)) := by
  exact h


-- Allow coefficient and adjunction conversions when specializing the abstract mate lemma.
set_option maxHeartbeats 800000 in
-- The mate and unit formulas contain large sheaf and category expressions.
/-- The ordinary completed-module mate is the sectionwise isomorphism-square
comparison, with its inverse-image-unit normalization.
Source: extracted proof, step 6; Stacks Tag 07A7.
(blueprint: lem-pur-reindexing-ordinary-mate-sections).
Proof: on a test over Y prime, use the canonical map (v,1) between the two fibre
products to restrict sections of M. Its inverse uses (inv v,1); commutativity and
cancellation of g show that both maps lie over the required tests. They commute
with restrictions and carry the completed coefficient action correctly by the
coefficient composition equation. Under the comma-normalized inverse-image
identification these maps give inverse natural transformations. Their adjunction
transpose is the specified pullback-square comparison followed by the counit:
a local inverse-image section is restricted along (v,W to V), on both sides.
The tensor-unit adjunction and sheafification extend that equality to all
sections. Uniqueness of adjunction transposes identifies this transformation with
purReindexingModuleMate. Evaluation after the inverse-image unit is exactly the
restriction along purReindexingTestSquare displayed below. -/
theorem purReindexingOrdinaryMate
    {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    [IsIso v] [IsIso g] (sq : ChosenCartesianSquare v p' p g) :
  PurCompletedReindexingSquareOrdinary d sq ∧
  PurCompletedReindexingSquareSections d sq := by
  constructor
  · change IsIso (purReindexingModuleMate d sq)
    rw [← completed_mate_eq d sq]
    exact RingedRestrictionExchange.ordinary_open_isIso (purReindexingRingedSquare d sq)
  · apply completed_unit_formula d sq (purReindexingModuleMate d sq)
    rw [← completed_mate_eq d sq]
    exact ordinary_on_unit_normalized (purReindexingRingedSquare d sq)


end AlgebraicGeometry.Scheme
