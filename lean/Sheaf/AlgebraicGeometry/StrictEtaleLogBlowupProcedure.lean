/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q153
-/
import Sheaf.AlgebraicGeometry.LogFanChartBlowup

/-!
# Strict étale functorial log blowup procedures

Source: ILO VIII 3.3.8--3.3.15, especially the descent reduction on pp. 109--110
(blueprint: def-trf-strict-etale-log-blowup-procedure).

A comparison directly displays the recursively pulled-back tower with repetitions:
`count` counts retained stages, and `step` is the identity at exactly the deleted stages.
Thus whole-monoid centers alone are removed, including consecutive such centers.
All log maps, centers, and identity/composition laws are retained as data or predicates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The quasi-compact, monoidally torsion-free inputs. Local Noetherianity and fs are
already fields of `FineSaturatedLogScheme`. Source: ILO VIII 3.3.14--3.3.15
(blueprint: def-trf-strict-etale-log-blowup-procedure). -/
def IsLogBlowupInput (X : FineSaturatedLogScheme.{u}) : Prop :=
  CompactSpace X.scheme ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme)
      (g : Algebra.GrothendieckGroup (X.logStructure.characteristic t)) (n : ℕ),
      0 < n → g ^ n = 1 → g = 1

/-- Admission of a global fan chart is a property, with no chosen chart in the input.
This includes finite disjoint unions with their componentwise fans.
Source: ILO VIII 3.3.12, 3.3.15 (blueprint: def-trf-strict-etale-log-blowup-procedure). -/
def IsChartedLogBlowupInput (X : FineSaturatedLogScheme.{u}) : Prop :=
  IsLogBlowupInput X ∧ ∃ F : FineFan.Fan.{u}, Nonempty (LogFanChart X F)

/-- A tower together with its specified initial log scheme. Centers and their nonempty
coherence are part of the existing tower's blowup properties. Length zero is allowed.
Source: ILO VIII 3.3.8--3.3.10 (blueprint: def-trf-strict-etale-log-blowup-procedure). -/
structure LogBlowupTowerOver (X : FineSaturatedLogScheme.{u}) where
  tower : SaturatedLogBlowupTower.{u}
  initial : tower.level 0 = X

/-- A contracted recursive pullback, preserving the order and the actual log ideals.
The repeated levels of `B`, with `step`, form the uncontracted pullback: every square
is Cartesian in fs log schemes, and each retained center is the generated pullback ideal.
Deleted steps are transported identities, and deletion is equivalent to the pulled ideal
being the whole monoid sheaf. Proper principal centers are therefore retained.
Source: ILO VIII 3.3.8--3.3.10 (blueprint: def-trf-strict-etale-log-blowup-procedure). -/
structure LogBlowupComparison {X Y : FineSaturatedLogScheme.{u}} (f : EtaleLogHom Y X)
    (A : LogBlowupTowerOver X) (B : LogBlowupTowerOver Y) where
  count : Fin (A.tower.length + 1) →o Fin (B.tower.length + 1)
  first : count 0 = 0
  last : count (Fin.last A.tower.length) = Fin.last B.tower.length
  retained : Fin B.tower.length ↪o Fin A.tower.length
  before : ∀ k, count (retained k).castSucc = k.castSucc
  after : ∀ k, count (retained k).succ = k.succ
  deleted : ∀ i, i ∉ Set.range retained → count i.succ = count i.castSucc
  map : ∀ i, EtaleLogHom (B.tower.level (count i)) (A.tower.level i)
  base : HEq (map 0) f
  step : ∀ i : Fin A.tower.length,
    EtaleLogHom (B.tower.level (count i.succ)) (B.tower.level (count i.castSucc))
  cartesian : ∀ i, (step i).IsFSPullback (map i.castSucc) (map i.succ) (A.tower.arrow i)
  keptStep : ∀ k, HEq (step (retained k)) (B.tower.arrow k)
  deletedStep : ∀ i, i ∉ Set.range retained →
    ∃ e : EtaleLogHom (B.tower.level (count i.castSucc))
      (B.tower.level (count i.castSucc)), e.IsIdentity ∧ HEq (step i) e
  centers : ∀ k,
    HEq ((map (retained k).castSucc).pullbackIdeal (A.tower.center (retained k)))
      (B.tower.center k)
  whole : ∀ i, i ∉ Set.range retained ↔
    (map i.castSucc).pullbackIdeal (A.tower.center i) = fun _ ↦ Set.univ

/-- A functorial assignment on a class of log schemes. The domain is a property, so
fan charts are not choices on which the tower can depend. Comparisons apply to every
strict étale morphism, in particular all component inclusions of finite disjoint unions.
Identity and composition are equations on the contraction indices and actual log maps.
Source: ILO VIII 3.3.15 (blueprint: def-trf-strict-etale-log-blowup-procedure). -/
structure StrictEtaleLogBlowupProcedure (D : FineSaturatedLogScheme.{u} → Prop) where
  tower : ∀ X, D X → LogBlowupTowerOver X
  comparison : ∀ {X Y : FineSaturatedLogScheme.{u}} (hX : D X) (hY : D Y)
    (f : EtaleLogHom Y X), f.IsStrict → Etale f.base →
      LogBlowupComparison f (tower X hX) (tower Y hY)
  identityIndex : ∀ (X : FineSaturatedLogScheme.{u}) (hX : D X) (f : EtaleLogHom X X)
    (hs : f.IsStrict) (he : Etale f.base), f.IsIdentity →
      ∀ i, (comparison hX hX f hs he).count i = i
  identityMap : ∀ (X : FineSaturatedLogScheme.{u}) (hX : D X) (f : EtaleLogHom X X)
    (hs : f.IsStrict) (he : Etale f.base), f.IsIdentity → ∀ i,
      ∃ e : EtaleLogHom ((tower X hX).tower.level i) ((tower X hX).tower.level i),
        e.IsIdentity ∧ HEq ((comparison hX hX f hs he).map i) e
  compositionIndex : ∀ {X Y Z : FineSaturatedLogScheme.{u}}
    (hX : D X) (hY : D Y) (hZ : D Z)
    (f : EtaleLogHom Y X) (g : EtaleLogHom Z Y) (h : EtaleLogHom Z X)
    (sf : f.IsStrict) (sg : g.IsStrict) (sh : h.IsStrict)
    (ef : Etale f.base) (eg : Etale g.base) (eh : Etale h.base),
    g.CompEq f h → ∀ i,
      (comparison hX hZ h sh eh).count i =
        (comparison hY hZ g sg eg).count ((comparison hX hY f sf ef).count i)
  compositionMap : ∀ {X Y Z : FineSaturatedLogScheme.{u}}
    (hX : D X) (hY : D Y) (hZ : D Z)
    (f : EtaleLogHom Y X) (g : EtaleLogHom Z Y) (h : EtaleLogHom Z X)
    (sf : f.IsStrict) (sg : g.IsStrict) (sh : h.IsStrict)
    (ef : Etale f.base) (eg : Etale g.base) (eh : Etale h.base),
    g.CompEq f h → ∀ i,
      ∃ r : EtaleLogHom
        ((tower Z hZ).tower.level ((comparison hX hZ h sh eh).count i))
        ((tower Y hY).tower.level ((comparison hX hY f sf ef).count i)),
        HEq r ((comparison hY hZ g sg eg).map ((comparison hX hY f sf ef).count i)) ∧
          r.CompEq ((comparison hX hY f sf ef).map i) ((comparison hX hZ h sh eh).map i)

/-- An ordered isomorphism of towers with centers over the same initial log scheme.
The base map is the actual log identity, and every level has an actual log inverse.
Source: ILO VIII 3.3.8--3.3.15 (blueprint: def-trf-strict-etale-log-blowup-procedure). -/
structure LogBlowupTowerIso {X : FineSaturatedLogScheme.{u}}
    (A B : LogBlowupTowerOver X) where
  index : Fin (A.tower.length + 1) ≃o Fin (B.tower.length + 1)
  stage : Fin A.tower.length ≃o Fin B.tower.length
  first : index 0 = 0
  before : ∀ i, index i.castSucc = (stage i).castSucc
  after : ∀ i, index i.succ = (stage i).succ
  forward : ∀ i, EtaleLogHom (B.tower.level (index i)) (A.tower.level i)
  backward : ∀ i, EtaleLogHom (A.tower.level i) (B.tower.level (index i))
  inverse : ∀ i, (forward i).AreInverses (backward i)
  base : ∃ e : EtaleLogHom X X, e.IsIdentity ∧ HEq (forward 0) e
  arrows : ∀ i,
    ∃ b : EtaleLogHom (B.tower.level (index i.succ))
      (B.tower.level (index i.castSucc)),
      HEq b (B.tower.arrow (stage i)) ∧
        b.Square (forward i.castSucc) (forward i.succ) (A.tower.arrow i)
  centers : ∀ i, HEq ((forward i.castSucc).pullbackIdeal (A.tower.center i))
    (B.tower.center (stage i))

/-- Agreement of functorial procedures on a subdomain. The level isomorphisms preserve
centers and are natural for strict étale comparisons, on both indices and log maps.
This expresses extension as well as the canonical, functorial uniqueness of extensions.
Source: ILO VIII 3.3.15 (blueprint: def-trf-strict-etale-log-blowup-procedure). -/
structure LogBlowupProcedureAgreement {D E : FineSaturatedLogScheme.{u} → Prop}
    (P : StrictEtaleLogBlowupProcedure D) (Q : StrictEtaleLogBlowupProcedure E)
    (incl : ∀ X, D X → E X) where
  iso : ∀ (X : FineSaturatedLogScheme.{u}) (hX : D X),
    LogBlowupTowerIso (P.tower X hX) (Q.tower X (incl X hX))
  indexNaturality : ∀ {X Y : FineSaturatedLogScheme.{u}} (hX : D X) (hY : D Y)
    (f : EtaleLogHom Y X) (hs : f.IsStrict) (he : Etale f.base) i,
    (iso Y hY).index ((P.comparison hX hY f hs he).count i) =
      (Q.comparison (incl X hX) (incl Y hY) f hs he).count ((iso X hX).index i)
  mapNaturality : ∀ {X Y : FineSaturatedLogScheme.{u}} (hX : D X) (hY : D Y)
    (f : EtaleLogHom Y X) (hs : f.IsStrict) (he : Etale f.base) i,
    ∃ r : EtaleLogHom
      ((Q.tower Y (incl Y hY)).tower.level
        ((iso Y hY).index ((P.comparison hX hY f hs he).count i)))
      ((Q.tower X (incl X hX)).tower.level ((iso X hX).index i)),
      HEq r ((Q.comparison (incl X hX) (incl Y hY) f hs he).map ((iso X hX).index i)) ∧
        ((iso Y hY).forward ((P.comparison hX hY f hs he).count i)).Square
          ((P.comparison hX hY f hs he).map i) r ((iso X hX).forward i)

end AlgebraicGeometry
