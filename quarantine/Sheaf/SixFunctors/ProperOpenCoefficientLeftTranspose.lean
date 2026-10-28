/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.SixFunctors.ScalarSixDirectImage
public import Sheaf.SixFunctors.ScalarSixPullback
public import Sheaf.Paper.FiniteConstantRingedLocalModel
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Mathlib.CategoryTheory.Adjunction.Basic

/-! # The left transpose of proper/open coefficient restriction

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six/
det-prop-scalar-six-compact-support.proof.md, Independence paragraph.
(blueprint: lem-sfb-proper-open-coefficient-left-transpose).

The helpers spell out the two morphisms in the calculation, using the existing
normalized scalar comparison and the counit-defined exchange map.

## Main definitions

- `properOpenCoefficientLeft`: the specified composite h_L.
- `properOpenCoefficientLeftExpanded`: its displayed expanded inverse transpose.

## Main statements

- `properOpenCoefficientLeftTranspose`: the two transpose equalities and pullback coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The specified left composite h_L, with u and q the two actual pullback projections.
Here theta inverse is c, scalarDirectImageMate is gamma, and exchange is b.
Source: blueprint compact-support proof, Independence paragraph, restriction calculation
(blueprint: lem-sfb-proper-open-coefficient-left-transpose). -/
def properOpenCoefficientLeft {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {Z Y V : Scheme.{u}} (p : Z ⟶ Y) (v : V ⟶ Y)
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Z)) :
    (scalarSixChange a V).obj
        ((scalarSixPull Λ v).obj ((RootCoordinateFace.lower Λ.X p).obj M)) ⟶
      (RootCoordinateFace.lower Λ'.X (pullback.snd p v)).obj
        ((scalarSixChange a (pullback p v)).obj
          ((scalarSixPull Λ (pullback.fst p v)).obj M)) :=
  (scalarDirectImagePullbackData.theta a v).hom.app
      ((RootCoordinateFace.lower Λ.X p).obj M) ≫
    (scalarSixPull Λ' v).map ((scalarDirectImageMate a p).app M) ≫
    (RootCoordinateFace.exchange Λ'.X (pullback.fst p v) (pullback.snd p v) p v
      (pullback.condition)).app ((scalarSixChange a Z).obj M) ≫
    (RootCoordinateFace.lower Λ'.X (pullback.snd p v)).map
      ((scalarDirectImagePullbackData.theta a (pullback.fst p v)).inv.app M)

/-- The expanded inverse transpose of h_L, in the order of the first displayed equality.
No exchange map or direct-image coefficient mate is inverted.
Source: blueprint compact-support proof, Independence paragraph, restriction calculation
(blueprint: lem-sfb-proper-open-coefficient-left-transpose). -/
def properOpenCoefficientLeftExpanded {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {Z Y V : Scheme.{u}} (p : Z ⟶ Y) (v : V ⟶ Y)
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Z)) :
    (scalarSixPull Λ' (pullback.snd p v)).obj
        ((scalarSixChange a V).obj
          ((scalarSixPull Λ v).obj ((RootCoordinateFace.lower Λ.X p).obj M))) ⟶
      (scalarSixChange a (pullback p v)).obj
        ((scalarSixPull Λ (pullback.fst p v)).obj M) :=
  (scalarSixPull Λ' (pullback.snd p v)).map
      ((scalarDirectImagePullbackData.theta a v).hom.app
        ((RootCoordinateFace.lower Λ.X p).obj M)) ≫
    (RootCoordinateFace.squareUpper Λ'.X (pullback.fst p v) (pullback.snd p v) p v
      (pullback.condition)).hom.app
        ((scalarSixChange a Y).obj ((RootCoordinateFace.lower Λ.X p).obj M)) ≫
    (scalarSixPull Λ' (pullback.fst p v)).map
      ((scalarSixPull Λ' p).map ((scalarDirectImageMate a p).app M)) ≫
    (scalarSixPull Λ' (pullback.fst p v)).map
      ((RootCoordinateFace.adjunction Λ'.X p).counit.app ((scalarSixChange a Z).obj M)) ≫
    (scalarDirectImagePullbackData.theta a (pullback.fst p v)).inv.app M

/-- The left inverse-transpose calculation and the coherent pullback identity, for the
listed coefficient maps and bounded constructible finite-Tor input of the node.

Source: blueprint compact-support proof, Independence paragraph, restriction calculation
(blueprint: lem-sfb-proper-open-coefficient-left-transpose).

Proof:
1. Apply lem-sfb-adjunction-transpose-square twice to the recorded derived adjunction
   for q, first to precomposition by L'_v(gamma) c_v inverse, then to postcomposition
   by R'_q(c_u). The defining transpose of b' gives c_u L'_u(epsilon') a' L'_q(d).
2. Naturality of a' at gamma moves L'_v(gamma) through a'. This is precisely
   properOpenCoefficientLeftExpanded.
3. Use det-prop-scalar-six-pullback (1) for the two factorizations pu = vq. Its
   composition coherence, followed by cancellation of c_v and its inverse, gives
   the third equality below.
4. Substitute the counit equation of det-prop-scalar-six-direct-image (2) at p,M.
   Naturality of c_u at epsilon and step 3 identify the expansion with T(t) c_q.
   Functoriality combines T(a_P) and T(L_u(epsilon)). Only c_v was inverted. -/
theorem properOpenCoefficientLeftTranspose
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (_ha : ListedCoefficientMap ell a)
    {Z Y V : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : Z ⟶ Y) [IsProper p.left] (v : V ⟶ Y) [IsOpenImmersion v.left]
    (M : ConstantModelConstructibleFiniteTor Λ.X Z.left) :
    ((scalarSixPull Λ' (pullback.snd p.left v.left)).map
        (properOpenCoefficientLeft a p.left v.left M.obj) ≫
      (RootCoordinateFace.adjunction Λ'.X (pullback.snd p.left v.left)).counit.app
        ((scalarSixChange a (pullback p.left v.left)).obj
          ((scalarSixPull Λ (pullback.fst p.left v.left)).obj M.obj)) =
      properOpenCoefficientLeftExpanded a p.left v.left M.obj) ∧
    (properOpenCoefficientLeftExpanded a p.left v.left M.obj =
      (scalarDirectImagePullbackData.theta a (pullback.snd p.left v.left)).inv.app
          ((scalarSixPull Λ v.left).obj ((RootCoordinateFace.lower Λ.X p.left).obj M.obj)) ≫
        (scalarSixChange a (pullback p.left v.left)).map
          ((RootCoordinateFace.squareUpper Λ.X (pullback.fst p.left v.left)
              (pullback.snd p.left v.left) p.left v.left
              (pullback.condition)).hom.app
                ((RootCoordinateFace.lower Λ.X p.left).obj M.obj) ≫
            (scalarSixPull Λ (pullback.fst p.left v.left)).map
              ((RootCoordinateFace.adjunction Λ.X p.left).counit.app M.obj))) ∧
    ((scalarSixPull Λ' (pullback.snd p.left v.left)).map
        ((scalarDirectImagePullbackData.theta a v.left).hom.app
          ((RootCoordinateFace.lower Λ.X p.left).obj M.obj)) ≫
      (RootCoordinateFace.squareUpper Λ'.X (pullback.fst p.left v.left)
          (pullback.snd p.left v.left) p.left v.left
          (pullback.condition)).hom.app
            ((scalarSixChange a Y.left).obj ((RootCoordinateFace.lower Λ.X p.left).obj M.obj)) ≫
      (scalarSixPull Λ' (pullback.fst p.left v.left)).map
        ((scalarDirectImagePullbackData.theta a p.left).inv.app
          ((RootCoordinateFace.lower Λ.X p.left).obj M.obj)) ≫
      (scalarDirectImagePullbackData.theta a (pullback.fst p.left v.left)).inv.app
        ((scalarSixPull Λ p.left).obj ((RootCoordinateFace.lower Λ.X p.left).obj M.obj)) =
      (scalarDirectImagePullbackData.theta a (pullback.snd p.left v.left)).inv.app
          ((scalarSixPull Λ v.left).obj ((RootCoordinateFace.lower Λ.X p.left).obj M.obj)) ≫
        (scalarSixChange a (pullback p.left v.left)).map
          ((RootCoordinateFace.squareUpper Λ.X (pullback.fst p.left v.left)
              (pullback.snd p.left v.left) p.left v.left
              (pullback.condition)).hom.app
                ((RootCoordinateFace.lower Λ.X p.left).obj M.obj))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
