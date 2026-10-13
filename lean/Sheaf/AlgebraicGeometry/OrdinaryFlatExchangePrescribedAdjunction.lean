/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

import Sheaf.AlgebraicGeometry.FlatBaseChangeMapSections
import Sheaf.AlgebraicGeometry.FlatBaseChangeResolutionIso

/-! # Ordinary flat exchange with a prescribed adjunction

Source: Stacks Project, Tags 02KH and 02N7.
(blueprint: lem-weil-pbc-ordinary-flat-exchange-prescribed-adjunction).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Ordinary flat exchange, normalized for the supplied adjunction on f.
Source: Stacks Project, Tags 02KH (part (1), degree zero) and 02N7 (mate construction).
(blueprint: lem-weil-pbc-ordinary-flat-exchange-prescribed-adjunction).

Proof: Choose tensor-pullback adjunctions on g, q and p. The sectionwise
pushforward-composition isomorphisms and the cartesian-square equation give an
isomorphism q_* f_* = p_* g_*. Its conjugate under the composite adjunctions
(g^* followed by p^*) and (f^* followed by q^*) gives c, using the supplied
adjunction on f. Take the horizontal mate under the adjunctions on q and g to
obtain B. Naturality follows from the unit, counit and composition comparisons.
For the unit identity, use unit_conjugateEquiv_symm on the composite adjunctions.
Expand their units: the f,q unit followed by the pushforward square equals the
g,p unit followed by the pushforward of c. Take the g-adjoint of the claimed
left side. Naturality of the g-unit moves the f-unit to the front; the defining
adjoint equation for B turns the remaining map into f_* of the q-unit followed
by the pushforward square. Substitute the composite-unit equation. This is the
g-adjoint of the claimed right side, so injectivity of homEquiv proves equality.
In degree zero the resolution-defined comparison of 02N7 is precisely this mate:
transport through the canonical zeroth-derived-functor identifications, evaluate
on an augmented resolution, and use its augmentation equation. Degree-zero flat
base change (02KH) makes B invertible for every quasi-coherent M, since proper f
is quasi-compact and quasi-separated. The definition of B uses only the chosen
adjunctions and the pushforward comparison, so it is natural on all modules,
including non-quasi-coherent modules. Empty schemes and zero modules require no
separate case: the same unit and counit equations apply. -/
theorem ordinary_flat_exchange_prescribed_adjunction
    {X Y S : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : S ⟶ Y) [Flat g]
    (adj : Scheme.Modules.tensorPullback f ⊣ Scheme.Modules.pushforward f) :
    let p := pullback.snd f g
    let q := pullback.fst f g
    let adjR := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction p)
    let c := (conjugateIsoEquiv
      (adj.comp (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction q)))
      ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp adjR)).symm
        (Scheme.Modules.pushforwardComp q f ≪≫
          Scheme.Modules.pushforwardCongr pullback.condition ≪≫
          (Scheme.Modules.pushforwardComp p g).symm)
    let B : Scheme.Modules.pushforward f ⋙ Scheme.Modules.tensorPullback g ⟶
        Scheme.Modules.tensorPullback q ⋙ Scheme.Modules.pushforward p :=
      { app := fun M ↦ Scheme.Modules.moduleBaseChangeMap f p g q pullback.condition M
        naturality := fun _ _ a ↦
          Scheme.Modules.moduleBaseChangeMap_naturality f p g q pullback.condition a }
    (∀ (M : X.Modules), M.IsQuasicoherent → IsIso (B.app M)) ∧
      (∀ (N : Y.Modules),
        (Scheme.Modules.tensorPullback g).map (adj.unit.app N) ≫
          B.app ((Scheme.Modules.tensorPullback f).obj N) =
        adjR.unit.app ((Scheme.Modules.tensorPullback g).obj N) ≫
          (Scheme.Modules.pushforward p).map (c.hom.app N)) := by sorry

end AlgebraicGeometry
