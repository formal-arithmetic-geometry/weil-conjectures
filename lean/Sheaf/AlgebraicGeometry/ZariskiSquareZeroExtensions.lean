/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Sheaf.Topology.SquareZeroSheafAlgebra

/-! # Zariski square-zero extension problems

Source: Stacks Project, Deformation Theory, Tags 0GPZ and 0GQ1
(blueprint: def-sfb-zariski-square-zero-extension-problems).

Exactness is local surjectivity, not surjectivity on every open set.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace TopCat.SquareZero

open TopCat.SquareZeroSheaf

/-- An extension over a thickened base with a prescribed map of its base ideal.
The condition is imposed on every local section of that ideal.
Source: Stacks 08UC (blueprint: def-sfb-zariski-square-zero-extension-problems). -/
structure Problem {T : TopCat.{u}} {R' R A : T.Sheaf CommRingCat.{u}}
    (q : R' ⟶ R) (ρ : R ⟶ A)
    (G : SheafOfModules.{u} (SheafDifferentials.ring A)) where
  baseIdeal (V : (Opens T)ᵒᵖ) :
    RingHom.ker (q.hom.app V).hom →+ G.val.obj V
  naturality {V W : (Opens T)ᵒᵖ} (r : V ⟶ W)
    (a : RingHom.ker (q.hom.app V).hom)
    (b : RingHom.ker (q.hom.app W).hom)
    (h : R'.obj.map r a.val = b.val) : G.val.map r (baseIdeal V a) = baseIdeal W b

/-- A solution has exactly the prescribed base-ideal action.
Source: Stacks 08UC (blueprint: def-sfb-zariski-square-zero-extension-problems). -/
def Problem.Solution {T : TopCat.{u}} {R' R A : T.Sheaf CommRingCat.{u}}
    {q : R' ⟶ R} {ρ : R ⟶ A}
    {G : SheafOfModules.{u} (SheafDifferentials.ring A)} (P : Problem q ρ G) :=
  {E : Extension (q ≫ ρ) G // ∀ (V : (Opens T)ᵒᵖ)
    (a : RingHom.ker (q.hom.app V).hom), E.base.hom.app V a.val = E.i V (P.baseIdeal V a)}

/-- A coefficient morphism carries the prescribed base-ideal map to the new one.
Source: Stacks 0GQ1 (blueprint: def-sfb-zariski-square-zero-extension-problems). -/
def Problem.Compatible {T : TopCat.{u}} {R' R A : T.Sheaf CommRingCat.{u}}
    {q : R' ⟶ R} {ρ : R ⟶ A} {G H : SheafOfModules.{u} (SheafDifferentials.ring A)}
    (P : Problem q ρ G) (Q : Problem q ρ H) (a : G ⟶ H) : Prop :=
  ∀ (V : (Opens T)ᵒᵖ) (r : RingHom.ker (q.hom.app V).hom),
    a.val.app V (P.baseIdeal V r) = Q.baseIdeal V r

/-- Isomorphism classes of solutions with the prescribed base-ideal map.
Source: Stacks 08UC (blueprint: def-sfb-zariski-square-zero-extension-problems). -/
def Problem.Classes {T : TopCat.{u}} {R' R A : T.Sheaf CommRingCat.{u}}
    {q : R' ⟶ R} {ρ : R ⟶ A}
    {G : SheafOfModules.{u} (SheafDifferentials.ring A)} (P : Problem q ρ G) :=
  Quot (fun E F : P.Solution ↦ Nonempty (Iso E.val F.val))

/-- The marked class of a solution. Source: Stacks 08UC
(blueprint: def-sfb-zariski-square-zero-extension-problems). -/
def Problem.Solution.class {T : TopCat.{u}} {R' R A : T.Sheaf CommRingCat.{u}}
    {q : R' ⟶ R} {ρ : R ⟶ A}
    {G : SheafOfModules.{u} (SheafDifferentials.ring A)} {P : Problem q ρ G}
    (E : P.Solution) : P.Classes := Quot.mk _ E

end TopCat.SquareZero
