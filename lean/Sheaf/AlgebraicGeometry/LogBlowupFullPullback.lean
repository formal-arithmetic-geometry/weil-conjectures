/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.AlgebraicGeometry.StrictLogBlowupProcedure

/-! # Full pullbacks of ordered log blowup towers

Source: ILO VIII 3.3.8--3.3.11 and proof of 3.3.15, pp.107--110
(blueprint: def-trf-log-tower-full-pullback).

Full pullbacks retain every original stage, including whole-monoid centers. The
auxiliary predicates specify contraction, its interchange isomorphism, and restriction
of actual comparisons and tower isomorphisms, without choosing universal objects.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An uncontracted recursive pullback, with its ordered level and stage identifications,
actual log maps, fs Cartesian squares and generated pullback ideals. No whole center is
removed. Source: ILO VIII 3.3.9--3.3.11
(blueprint: def-trf-log-tower-full-pullback). -/
structure LogBlowupFullPullback {X Y : FineSaturatedLogScheme.{u}} (f : EtaleLogHom Y X)
    (A : LogBlowupTowerOver X) (B : LogBlowupTowerOver Y) where
  index : Fin (A.tower.length + 1) ≃o Fin (B.tower.length + 1)
  stage : Fin A.tower.length ≃o Fin B.tower.length
  first : index 0 = 0
  before : ∀ i, index i.castSucc = (stage i).castSucc
  after : ∀ i, index i.succ = (stage i).succ
  map : ∀ i, EtaleLogHom (B.tower.level (index i)) (A.tower.level i)
  base : HEq (map 0) f
  cartesian : ∀ i, ∃ b : EtaleLogHom (B.tower.level (index i.succ))
    (B.tower.level (index i.castSucc)), HEq b (B.tower.arrow (stage i)) ∧
      b.IsFSPullback (map i.castSucc) (map i.succ) (A.tower.arrow i)
  centers : ∀ i, HEq ((map i.castSucc).pullbackIdeal (A.tower.center i))
    (B.tower.center (stage i))

/-- Contracted means exactly that no actual center is the whole monoid sheaf.
It does not exclude proper principal centers. Source: ILO VIII 3.3.8
(blueprint: def-trf-log-tower-full-pullback). -/
def LogBlowupTowerOver.IsContracted {X : FineSaturatedLogScheme.{u}}
    (A : LogBlowupTowerOver X) : Prop :=
  ∀ i, A.tower.center i ≠ fun _ ↦ Set.univ

/-- Scheme base change and whole-ideal detection at every original level of a full
pullback. The base projection is the constructed composite of tower arrows.
Source: ILO VIII 3.3.8--3.3.11 (blueprint: def-trf-log-tower-full-pullback). -/
def LogBlowupFullPullback.IsCoverSynchronized {X Y : FineSaturatedLogScheme.{u}}
    {f : EtaleLogHom Y X} {A : LogBlowupTowerOver X} {B : LogBlowupTowerOver Y}
    (p : LogBlowupFullPullback f A B) : Prop :=
  (∀ i, IsPullback (p.map i).base (B.toBase (p.index i)).base (A.toBase i).base f.base ∧
    (p.map i).IsStrict ∧ Etale (p.map i).base ∧ Surjective (p.map i).base) ∧
  ∀ i, B.tower.center (p.stage i) = (fun _ ↦ Set.univ) ↔
    A.tower.center i = (fun _ ↦ Set.univ)

/-- The normalized interchange isomorphism: both routes have the same retained original
labels and count maps, and their actual log composites agree. This specifies the
canonical isomorphism, rather than just an abstract isomorphism of the top schemes.
Source: ILO VIII 3.3.8--3.3.11, proof of 3.3.15
(blueprint: def-trf-log-tower-full-pullback). -/
def LogBlowupFullPullback.IsContractionInterchange
    {Y W : FineSaturatedLogScheme.{u}} {v : EtaleLogHom W Y}
    {D C : LogBlowupTowerOver Y} {E F U : LogBlowupTowerOver W}
    (p : LogBlowupFullPullback v D E)
    (c : LogBlowupComparison (EtaleLogHom.id Y) D C)
    (d : LogBlowupComparison (EtaleLogHom.id W) E F)
    (q : LogBlowupFullPullback v C U) (e : LogBlowupTowerIso U F) : Prop :=
  (∀ i, e.index (q.index (c.count i)) = d.count (p.index i)) ∧
  (∀ k, p.stage (c.retained k) = d.retained (e.stage (q.stage k))) ∧
  ∀ i, HEq (((e.forward (q.index (c.count i))).comp (q.map (c.count i))).comp (c.map i))
    ((d.map (p.index i)).comp (p.map i))

/-- Restriction of an ordered center-preserving isomorphism is the actual commuting
log square, with the corresponding ordered indices. Source: ILO VIII proof of 3.3.15
(blueprint: def-trf-log-tower-full-pullback). -/
def LogBlowupTowerIso.IsPullbackIso
    {Y W : FineSaturatedLogScheme.{u}} {v : EtaleLogHom W Y}
    {A B : LogBlowupTowerOver Y} {U V : LogBlowupTowerOver W}
    (p : LogBlowupFullPullback v A U) (q : LogBlowupFullPullback v B V)
    (e : LogBlowupTowerIso A B) (a : LogBlowupTowerIso U V) : Prop :=
  (∀ i, q.index (e.index i) = a.index (p.index i)) ∧
  (∀ k, q.stage (e.stage k) = a.stage (p.stage k)) ∧
  ∀ i, ∃ r : EtaleLogHom (V.tower.level (a.index (p.index i)))
    (B.tower.level (e.index i)), HEq r (q.map (e.index i)) ∧
      (a.forward (p.index i)).Square (p.map i) r (e.forward i)

/-- The local isomorphism from the contracted full pullback to the pullback of a
contracted tower is induced by the downstairs isomorphism. This includes the normalized
interchange and the actual log square on each original level of the contraction.
Source: ILO VIII 3.3.8--3.3.11, proof of 3.3.15
(blueprint: def-trf-log-tower-full-pullback). -/
def LogBlowupTowerIso.InducesContractedLocalIso
    {Y W : FineSaturatedLogScheme.{u}} {v : EtaleLogHom W Y}
    {C A : LogBlowupTowerOver Y} {U F V : LogBlowupTowerOver W}
    (p : LogBlowupFullPullback v C U) (q : LogBlowupFullPullback v A V)
    (e : LogBlowupTowerIso U F) (a : LogBlowupTowerIso F V)
    (b : LogBlowupTowerIso C A) : Prop :=
  ∃ t : LogBlowupTowerIso U V, b.IsPullbackIso p q t ∧
    (∀ i, t.index i = a.index (e.index i)) ∧
    (∀ k, t.stage k = a.stage (e.stage k)) ∧
    ∀ i, HEq (t.forward i) ((a.forward (e.index i)).comp (e.forward i))

/-- Restriction of a contracted pullback comparison along a full pullback of its source.
The retained labels and actual log maps, not merely the underlying schemes, are fixed.
Source: ILO VIII 3.3.10 and proof of 3.3.15
(blueprint: def-trf-log-tower-full-pullback). -/
def LogBlowupComparison.RestrictsTo
    {X Y W : FineSaturatedLogScheme.{u}} {f : EtaleLogHom Y X} {v : EtaleLogHom W Y}
    {B : LogBlowupTowerOver X} {A : LogBlowupTowerOver Y} {U : LogBlowupTowerOver W}
    (p : LogBlowupFullPullback v A U) (c : LogBlowupComparison f B A)
    (a : LogBlowupComparison (v.comp f) B U) : Prop :=
  (∀ i, a.count i = p.index (c.count i)) ∧
  (∀ k, a.retained (p.stage k) = c.retained k) ∧
  ∀ i, HEq (a.map i) ((p.map (c.count i)).comp (c.map i))

/-- The identity law for a contracted comparison, including retained labels and actual
log identities. Source: ILO VIII 3.3.10, proof of 3.3.15
(blueprint: def-trf-log-tower-full-pullback). -/
def LogBlowupComparison.IsIdentityComparison {Y : FineSaturatedLogScheme.{u}}
    {A : LogBlowupTowerOver Y} (c : LogBlowupComparison (EtaleLogHom.id Y) A A) : Prop :=
  (∀ i, c.count i = i) ∧ (∀ k, c.retained k = k) ∧
    ∀ i, HEq (c.map i) (EtaleLogHom.id (A.tower.level i))

/-- Agreement with the unchanged full pullback, the local form of the identity law.
Source: ILO VIII 3.3.10, proof of 3.3.15
(blueprint: def-trf-log-tower-full-pullback). -/
def LogBlowupComparison.AgreesWithFullPullback
    {Y W : FineSaturatedLogScheme.{u}} {v : EtaleLogHom W Y}
    {A : LogBlowupTowerOver Y} {U : LogBlowupTowerOver W}
    (p : LogBlowupFullPullback v A U) (a : LogBlowupComparison v A U) : Prop :=
  (∀ i, a.count i = p.index i) ∧ (∀ k, a.retained (p.stage k) = k) ∧
    ∀ i, HEq (a.map i) (p.map i)

/-- The composition law on both count maps and retained embeddings and on actual log
morphisms. The third base map may be any presentation of the composite, permitting
associativity transports without a second notion of log composition.
Source: ILO VIII 3.3.10, proof of 3.3.15
(blueprint: def-trf-log-tower-full-pullback). -/
def LogBlowupComparison.IsCompositeComparison
    {X Y Z : FineSaturatedLogScheme.{u}}
    {f : EtaleLogHom Y X} {g : EtaleLogHom Z Y} {h : EtaleLogHom Z X}
    {B : LogBlowupTowerOver X} {A : LogBlowupTowerOver Y} {C : LogBlowupTowerOver Z}
    (a : LogBlowupComparison f B A) (b : LogBlowupComparison g A C)
    (c : LogBlowupComparison h B C) : Prop :=
  (∀ i, c.count i = b.count (a.count i)) ∧
  (∀ k, c.retained k = a.retained (b.retained k)) ∧
    ∀ i, HEq (c.map i) ((b.map (a.count i)).comp (a.map i))

end AlgebraicGeometry
