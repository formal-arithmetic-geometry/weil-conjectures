/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q95
-/
module

public import Sheaf.AlgebraicGeometry.StrictEtaleLogBlowupProcedure
public import Sheaf.AlgebraicGeometry.LogMorphismOperations
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Log blowup procedures functorial for all strict morphisms

Source: ILO, Travaux de Gabber, VIII 3.3.8--3.3.15 and 3.4.9, pp.107--112
(blueprint: def-per-strict-log-blowup-procedure).

## Main definitions

* `StrictLogBlowupProcedure`: ordered comparisons for arbitrary strict morphisms.
* `LogBlowupTowerOver.toBase`: the actual composite of the tower arrows.

The existing fs Cartesian comparison retains every center and its order. This extends
its functoriality domain beyond the strict etale maps of `StrictEtaleLogBlowupProcedure`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Noetherian separated log regular inputs, allowing the empty scheme and disconnected
schemes and imposing no excellence condition. Local Noetherianity and fs are already
fields of the log scheme. Source: ILO VIII 3.4.1, 3.4.9
(blueprint: def-per-strict-log-blowup-procedure). -/
def IsLogRegularResolutionInput (X : FineSaturatedLogScheme.{u}) : Prop :=
  IsNoetherian X.scheme ∧ X.scheme.IsSeparated ∧ X.IsLogRegular

/-- A tower procedure on a class of fs log schemes, functorial for every strict map.
Comparison indices and actual log maps obey identity and composition. The existing
`LogBlowupComparison` deletes exactly whole-monoid centers, retains proper principal
centers, and supplies the recursive fs pullback squares and log-center identifications.
Source: ILO VIII 3.3.8--3.3.15, 3.4.9 (blueprint: def-per-strict-log-blowup-procedure). -/
structure StrictLogBlowupProcedure (D : FineSaturatedLogScheme.{u} → Prop) where
  tower : ∀ X, D X → LogBlowupTowerOver X
  comparison : ∀ {X Y : FineSaturatedLogScheme.{u}} (hX : D X) (hY : D Y)
    (f : EtaleLogHom Y X), f.IsStrict → LogBlowupComparison f (tower X hX) (tower Y hY)
  identityIndex : ∀ (X : FineSaturatedLogScheme.{u}) (hX : D X)
    (f : EtaleLogHom X X) (hs : f.IsStrict), f.IsIdentity → ∀ i,
      (comparison hX hX f hs).count i = i
  identityMap : ∀ (X : FineSaturatedLogScheme.{u}) (hX : D X)
    (f : EtaleLogHom X X) (hs : f.IsStrict), f.IsIdentity → ∀ i,
      HEq ((comparison hX hX f hs).map i) (EtaleLogHom.id ((tower X hX).tower.level i))
  compositionIndex : ∀ {X Y Z : FineSaturatedLogScheme.{u}}
    (hX : D X) (hY : D Y) (hZ : D Z)
    (f : EtaleLogHom Y X) (g : EtaleLogHom Z Y) (h : EtaleLogHom Z X)
    (sf : f.IsStrict) (sg : g.IsStrict) (sh : h.IsStrict), g.CompEq f h → ∀ i,
      (comparison hX hZ h sh).count i =
        (comparison hY hZ g sg).count ((comparison hX hY f sf).count i)
  compositionMap : ∀ {X Y Z : FineSaturatedLogScheme.{u}}
    (hX : D X) (hY : D Y) (hZ : D Z)
    (f : EtaleLogHom Y X) (g : EtaleLogHom Z Y) (h : EtaleLogHom Z X)
    (sf : f.IsStrict) (sg : g.IsStrict) (sh : h.IsStrict), g.CompEq f h → ∀ i,
      HEq ((comparison hX hZ h sh).map i)
        (((comparison hY hZ g sg).map ((comparison hX hY f sf).count i)).comp
          ((comparison hX hY f sf).map i))

/-- The composite from each level to the specified base. At level zero it is the log
identity transported through the specified initial equality; at a successor it composes
the next blowup arrow with the preceding composite. No morphism is chosen from existence.
Source: ILO VIII 3.3.9--3.3.10 (blueprint: def-per-strict-log-blowup-procedure). -/
def LogBlowupTowerOver.toBase {X : FineSaturatedLogScheme.{u}} (A : LogBlowupTowerOver X)
    (i : Fin (A.tower.length + 1)) : EtaleLogHom (A.tower.level i) X :=
  Fin.induction
    (Eq.ndrec (motive := fun Y ↦ EtaleLogHom Y X) (EtaleLogHom.id X) A.initial.symm)
    (fun j f ↦ (A.tower.arrow j).comp f) i

end AlgebraicGeometry
