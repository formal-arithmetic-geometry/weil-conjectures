/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.AlgebraicGeometry.FormalFunctionsFinitePullback
public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial

/-! # Adjacent-level naturality of the finite quotient comparison

Source: Stacks Project, Tag 02OD, finite-level identifications, and Tags 01F7 and 01FB.
(blueprint: lem-weil-pbc-formal-functions-finite-quotient-transition)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

namespace AlgebraicGeometry

/-- Any family of sheaf maps factoring the finite pullback units respects adjacent
quotient transitions after applying the cohomology h-maps. The maps are not assumed
invertible, and the statement makes no assertion of linearity over the local ring.

Source: Stacks Project, Tag 02OD, finite-level identifications; Tags 01F7 and 01FB.
(blueprint: lem-weil-pbc-formal-functions-finite-quotient-transition)
Proof: Write j_n for the finite fibre immersion into the local base change and t_n for
the transition from fibre n to fibre n+1. Pullback uniqueness gives t_n followed by
j_(n+1) = j_n. The adjunction equations defining formalFunctionsFiniteFMap and
formalFibreTransitionFMap identify the composite unit through these two morphisms
with the unit for j_n, with the canonical composition identification of direct images.
Precompose the desired sheaf square with the quotient projection at level n+1.
The quotient-transition cokernel equation identifies its left side with the level-n
unit. The unit equations for e and for the transition identify its right side with
the same map. Cancel the epimorphic quotient projection to obtain the sheaf square.
Apply moduleCohomologyFMap_source_naturality to the quotient transition and
moduleCohomologyFMap_comp to t_n and j_(n+1). Transport across their equality with j_n
using the canonical pushforward congruence. The sheaf square then yields the displayed
identity of additive maps. This does not use surjectivity of a map on cohomology; only
the sheaf quotient projection is cancelled. It applies to n = 0, every p, and the zero
module exactly as to all other levels. -/
theorem formalFunctions_finite_quotient_transition {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) (y : Y) (p : ℕ) :
    let X' := pullback (Y.fromSpecStalk y) f
    let F' := (Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F
    let J := (Scheme.IdealSheafData.ofIdealTop
      ((maximalIdeal (Y.presheaf.stalk y)).map
        (Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv.hom)).comap
          (pullback.fst (Y.fromSpecStalk y) f)
    let C := RingedSpace.moduleCohomology X'.toRingedSpace p ⋙
      ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv ≫
          (pullback.fst (Y.fromSpecStalk y) f).appTop).hom
    let S := formalCompletionSystem J F' ⋙ C
    let T := formalFibreCohomologySystem f y F p ⋙ ModuleCat.restrictScalars
      (algebraMap (Y.presheaf.stalk y)
        (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)))
    ∀ (e : ∀ n : ℕ, formalModuleQuotient J (n + 1) F' ⟶
        (Scheme.Modules.pushforward (formalFunctionsFiniteι f y n)).obj
          ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F)),
      (∀ n : ℕ, formalModuleQuotientπ J (n + 1) F' ≫ e n =
        formalFunctionsFiniteFMap f y F n) →
      ∀ (n : ℕ) (x : S.obj (op (n + 1))),
        (show T.obj (op n) from
          (Scheme.Modules.moduleCohomologyFMap (formalFunctionsFiniteι f y n) (e n) p).hom
            ((S.map (homOfLE (Nat.le_succ n)).op) x)) =
          (T.map (homOfLE (Nat.le_succ n)).op)
            (show T.obj (op (n + 1)) from
              (Scheme.Modules.moduleCohomologyFMap (formalFunctionsFiniteι f y (n + 1))
                (e (n + 1)) p).hom x) := by
  sorry

end AlgebraicGeometry
