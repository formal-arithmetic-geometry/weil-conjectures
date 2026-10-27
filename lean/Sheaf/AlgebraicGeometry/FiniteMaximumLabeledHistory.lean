module

public import Sheaf.AlgebraicGeometry.ResolutionInvariantCalculusData

/-!
# Finite maximum histories with their cut-indexed realization

Source: ILO, Expose VIII, 2.3.1, 2.3.4--2.3.5, 2.3.11--2.3.13, pp. 91--94
(blueprint: def-trf-finite-maximum-labeled-history).

This packages a given finite sequence, its actual raw prefixes, and its labeled realization.
It asserts neither existence of a history nor existence of a resolution invariant calculus.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

open EmbeddedResolutionHistory

/-- The inclusion of the first `i + 1` stages in a history of length `n`.
Source: ILO VIII 2.3.1 (blueprint: def-trf-finite-maximum-labeled-history). -/
def resolutionHistoryPrefixIndex (n : ℕ) (i : Fin (n + 1)) :
    Fin (i.val + 1) →o Fin (n + 1) where
  toFun := Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ i.isLt))
  monotone' := fun _ _ h ↦ h

/-- A finite maximum-extension history stopped at its first regular strict transform,
with its prescribed labeling by positive maxima and its realization on all lower cuts.
The prefixHistory identifications retain the entire raw diagrams and their earlier center ideals.
The cut identifications are natural isomorphisms, so padding really inserts identity stages.
Source: ILO VIII 2.3.1, 2.3.4--2.3.5, 2.3.11--2.3.13
(blueprint: def-trf-finite-maximum-labeled-history). -/
structure FiniteMaximumLabeledHistory {V : Type w} [LinearOrder V] [OrderBot V]
    (ν : ResolutionInvariantCalculus.{u} V) (A : EmbeddedResolutionPair.{u}) where
  length : ℕ
  raw : EmbeddedResolutionHistory A length
  prefixHistory : (i : Fin (length + 1)) → EmbeddedResolutionHistory A i.val
  extension : ∀ j : Fin length, Extension (prefixHistory j.castSucc) (prefixHistory j.succ)
  maximum : ∀ j : Fin length, IsMaximumStep ν.value (extension j)
  admissible : ∀ i, Admissible ν.value (prefixHistory i)
  finalRegular : IsRegularScheme raw.X
  firstRegular : ∀ i : Fin (length + 1), IsRegularScheme (prefixHistory i).X ↔ i.val = length
  prefixAmbient : ∀ i, (prefixHistory i).ambient ≅
    (resolutionHistoryPrefixIndex length i).toFunctor.op ⋙ raw.ambient
  prefixIntrinsic : ∀ i, (prefixHistory i).intrinsic ≅
    (resolutionHistoryPrefixIndex length i).toFunctor.op ⋙ raw.intrinsic
  extensionAmbient : ∀ (j : Fin length) (k : Fin (j.val + 1)),
    ((extension j).ambient k).hom ≫
      ((prefixAmbient j.succ).app (op k.castSucc)).hom =
        ((prefixAmbient j.castSucc).app (op k)).hom
  extensionIntrinsic : ∀ (j : Fin length) (k : Fin (j.val + 1)),
    ((extension j).intrinsic k).hom ≫
      ((prefixIntrinsic j.succ).app (op k.castSucc)).hom =
        ((prefixIntrinsic j.castSucc).app (op k)).hom
  prefixInitialAmbient : ∀ i,
    ((prefixAmbient i).app (op 0)).hom ≫ raw.initialAmbient.hom =
      (prefixHistory i).initialAmbient.hom
  prefixInitialIntrinsic : ∀ i,
    ((prefixIntrinsic i).app (op 0)).hom ≫ raw.initialIntrinsic.hom =
      (prefixHistory i).initialIntrinsic.hom
  prefixInclusion : ∀ (i : Fin (length + 1)) (j : Fin (i.val + 1)),
    (prefixHistory i).inclusion.app (op j) ≫ ((prefixAmbient i).app (op j)).hom =
      ((prefixIntrinsic i).app (op j)).hom ≫
        raw.inclusion.app (op (resolutionHistoryPrefixIndex length i j))
  prefixCenters : ∀ (i : Fin (length + 1)) (j : Fin i.val),
    (prefixHistory i).center j =
      (raw.center ⟨j.val, lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ i.isLt)⟩).comap
        ((prefixAmbient i).app (op j.castSucc)).hom
  label : Fin length → OrderDual {v : V // v ≠ ⊥}
  increasing : StrictMono label
  labelMaximum : ∀ j : Fin length,
    IsGreatest (Set.range (ν.value (prefixHistory j.castSucc))) (OrderDual.ofDual (label j)).val
  tower : LabeledEmbeddedResolutionTower (OrderDual {v : V // v ≠ ⊥}) A
  labels : tower.labels = Finset.univ.image label
  stage : LowerSet (OrderDual {v : V // v ≠ ⊥}) →o Fin (length + 1)
  stageCount : ∀ D, (stage D).val =
    (@Finset.filter _ (fun l ↦ l ∈ D) (Classical.decPred _) tower.labels).card
  stageZero : stage ⊥ = 0
  stageBefore : ∀ j : Fin length, stage (LowerSet.Iio (label j)) = j.castSucc
  stageAfter : ∀ j : Fin length, stage (LowerSet.Iic (label j)) = j.succ
  ambientIso : tower.ambient ≅ stage.toFunctor.op ⋙ raw.ambient
  intrinsicIso : tower.intrinsic ≅ stage.toFunctor.op ⋙ raw.intrinsic
  initialAmbient : (ambientIso.app (op ⊥)).hom ≫
    eqToHom (congrArg (fun j ↦ raw.ambient.obj (op j)) stageZero) ≫
      raw.initialAmbient.hom = tower.initialAmbient.hom
  initialIntrinsic : (intrinsicIso.app (op ⊥)).hom ≫
    eqToHom (congrArg (fun j ↦ raw.intrinsic.obj (op j)) stageZero) ≫
      raw.initialIntrinsic.hom = tower.initialIntrinsic.hom
  inclusion : ∀ D, tower.inclusion.app (op D) ≫ (ambientIso.app (op D)).hom =
    (intrinsicIso.app (op D)).hom ≫ raw.inclusion.app (op (stage D))
  centers : ∀ j : Fin length, tower.center (label j) = (raw.center j).comap
    ((ambientIso.app (op (LowerSet.Iio (label j)))).hom ≫
      eqToHom (congrArg (fun k ↦ raw.ambient.obj (op k)) (stageBefore j)))

/-- The local invariant at a cut, evaluated on the actual raw prefixHistory at that cut.
Source: ILO VIII 2.3.4--2.3.5, 2.3.11--2.3.13
(blueprint: def-trf-finite-maximum-labeled-history). -/
def FiniteMaximumLabeledHistory.valueAtCut {V : Type w} [LinearOrder V] [OrderBot V]
    {ν : ResolutionInvariantCalculus.{u} V} {A : EmbeddedResolutionPair.{u}}
    (H : FiniteMaximumLabeledHistory ν A)
    (D : LowerSet (OrderDual {v : V // v ≠ ⊥}))
    (x : H.tower.intrinsic.obj (op D)) : V :=
  ν.value (H.prefixHistory (H.stage D))
    (((H.prefixIntrinsic (H.stage D)).app (op (Fin.last (H.stage D).val))).inv
      ((H.intrinsicIso.app (op D)).hom x))

end AlgebraicGeometry
