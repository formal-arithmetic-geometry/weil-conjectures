/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.KummerLogMorphism
public import Sheaf.AlgebraicGeometry.FSLogGroupAction
public import Sheaf.AlgebraicGeometry.LogFanChartBlowup
public import Sheaf.AlgebraicGeometry.LogMorphismOperations
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # Kummer etale group covers and fs base-change diagrams

Source: ILO VI 2.1--2.3, printed pp.71--73; X 1.8, printed pp.146--147
(blueprint: def-per-kummer-g-cover).

The diagonal condition says that the disjoint union with component maps `(1,g)`
IS an fs pullback. This is the universal-property formulation of the canonical
map from that disjoint union to an fs self-product being an isomorphism.
The underlying coproduct and strict component inclusions specify its log structure.
No ordinary scheme pullback is substituted for an fs pullback.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite surjective Kummer etale group cover. Invariance is equality of log maps.
The diagonal is expressed by a disjoint union with its component log structures
and the fs pullback universal property, with component projections `(1,g)`.
Source: ILO VI 2.1--2.2 (blueprint: def-per-kummer-g-cover). -/
def FSLogGroupAction.IsKummerGCover {G : Type v} [Group G] [Finite G]
    {C D : FineSaturatedLogScheme.{u}} (a : FSLogGroupAction G C)
    (q : EtaleLogHom C D) : Prop :=
  q.IsLogEtale ∧ q.IsKummer ∧ IsFinite q.base ∧ Surjective q.base ∧
    (∀ g : G, (a.logMap g).CompEq q q) ∧
    ∃ (S : FineSaturatedLogScheme.{u}) (ι : G → EtaleLogHom C S)
      (l r : EtaleLogHom S C),
      Nonempty (IsColimit (Cofan.mk S.scheme (fun g : G ↦ (ι g).base))) ∧
      (∀ g : G, (ι g).IsStrict) ∧ l.IsFSPullback q r q ∧
      ∀ g : G, (ι g).CompEq l (EtaleLogHom.id C) ∧ (ι g).CompEq r (a.logMap g)

/-- A representative of a locally Noetherian fs base change, including both projections
and the full log universal property. Source: ILO X 1.8, diagram (1.a)
(blueprint: def-per-kummer-g-cover). -/
structure FSLogBaseChange {C D : FineSaturatedLogScheme.{u}} (q : EtaleLogHom C D) where
  base : FineSaturatedLogScheme.{u}
  total : FineSaturatedLogScheme.{u}
  map : EtaleLogHom base D
  fst : EtaleLogHom total C
  snd : EtaleLogHom total base
  cartesian : fst.IsFSPullback q snd map

/-- The induced action is characterized by the pair `(g,1)` on the two projections.
All equations include log-section maps. Source: ILO X 1.8
(blueprint: def-per-kummer-g-cover). -/
def FSLogBaseChange.IsInducedAction {G : Type v} [Group G]
    {C D : FineSaturatedLogScheme.{u}} {q : EtaleLogHom C D}
    (B : FSLogBaseChange q) (a : FSLogGroupAction G C)
    (b : FSLogGroupAction G B.total) : Prop :=
  ∀ g : G, (b.logMap g).comp B.fst = B.fst.comp (a.logMap g) ∧
    (b.logMap g).CompEq B.snd B.snd

/-- The canonical comparison over a base map is specified by its two projections.
It is not an arbitrary map between the underlying schemes. Source: ILO X 1.8
(blueprint: def-per-kummer-g-cover). -/
def FSLogBaseChange.IsComparison {C D : FineSaturatedLogScheme.{u}}
    {q : EtaleLogHom C D} (B B' : FSLogBaseChange q)
    (h : EtaleLogHom B'.base B.base) (r : EtaleLogHom B'.total B.total) : Prop :=
  r.CompEq B.fst B'.fst ∧ r.CompEq B.snd (B'.snd.comp h)

end AlgebraicGeometry
