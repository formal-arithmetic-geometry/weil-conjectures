module

public import Sheaf.SixFunctors.ScalarSixDirectImage
public import Sheaf.SixFunctors.ScalarSixPullback
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.FiniteConstantRingedLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Right transpose of the proper/open coefficient comparison

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six/
det-prop-scalar-six-compact-support.proof.md, Independence paragraph; Stacks Tag 0037.
(blueprint: lem-sfb-proper-open-coefficient-right-transpose).

All functors use ordinary unbounded derived categories of internal modules. The exchange
and coefficient mate are the published canonical maps, with no invertibility hypothesis.
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

/-- The right-hand coefficient/restriction map h_R, using the canonical exchange on the
actual fibre product and the specified direct-image coefficient mate.
Source: blueprint latest, compact-support proof, Independence paragraph
(blueprint: lem-sfb-proper-open-coefficient-right-transpose). -/
def properOpenCoefficientRightMap {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {Z Y V : Scheme.{u}} (p : Z ⟶ Y) (v : V ⟶ Y)
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Z)) :
    (scalarSixChange a V).obj
        ((RootCoordinateFace.upper Λ.X v).obj ((RootCoordinateFace.lower Λ.X p).obj M)) ⟶
      (RootCoordinateFace.lower Λ'.X (pullback.snd p v)).obj
        ((scalarSixChange a (pullback p v)).obj
          ((RootCoordinateFace.upper Λ.X (pullback.fst p v)).obj M)) :=
  (scalarSixChange a V).map
      ((RootCoordinateFace.exchange Λ.X (pullback.fst p v) (pullback.snd p v) p v
        pullback.condition).app M) ≫
    (scalarDirectImageMate a (pullback.snd p v)).app
      ((RootCoordinateFace.upper Λ.X (pullback.fst p v)).obj M)

/-- The inverse adjunction transpose tau(h_R), explicitly left pullback followed by the
primed counit; this definition does not invert h_R, the exchange or the coefficient mate.
Source: blueprint latest, compact-support proof, Independence paragraph; Stacks Tag 0037
(blueprint: lem-sfb-proper-open-coefficient-right-transpose). -/
def properOpenCoefficientRightTranspose {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {Z Y V : Scheme.{u}} (p : Z ⟶ Y) (v : V ⟶ Y)
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Z)) :=
  (scalarSixPull Λ' (pullback.snd p v)).map (properOpenCoefficientRightMap a p v M) ≫
    (RootCoordinateFace.adjunction Λ'.X (pullback.snd p v)).counit.app
      ((scalarSixChange a (pullback p v)).obj
        ((RootCoordinateFace.upper Λ.X (pullback.fst p v)).obj M))

/-- The three expressions for the right inverse transpose, and the exchange counit
identity with the specified composition comparison a_P.

Source: blueprint latest, compact-support proof, Independence paragraph; Stacks Tag 0037
(blueprint: lem-sfb-proper-open-coefficient-right-transpose).

Proof:
1. Put A = L_v R_p M, B = L_u M. The exchange is the adjunct of
   t = a_(R_p M) followed by L_u of the p-counit. The inverse formula for the
   Hom bijection in lem-weil-pbc-adjunction-of-natural-bijection gives
   L_q(b) followed by the q-counit equal to t.
2. The defining mate formula of det-prop-scalar-six-direct-image gives
   L'_q(gamma) followed by the primed counit equal to c_(R_q B) followed by
   T of the q-counit. Expand h_R and use functoriality to get the first equality.
3. Naturality of the inverse comparison in det-prop-scalar-six-pullback (1) at b
   moves L'_q(T_V(b)) past c. Functoriality of T gives the second equality.
   Substitute step 1 to get the third. Only the canonical pullback comparison
   is inverted; no invertibility of b or gamma, flatness or completion is used. -/
theorem properOpenCoefficientRightTranspose_eq
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (_ha : ListedCoefficientMap ell a)
    {Z Y V : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : Z ⟶ Y) [IsProper p.left] (v : V ⟶ Y) [IsOpenImmersion v.left]
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Z.left))
    (_hM : constantModelBoundedConstructible Λ.X Z.left M ∧
      DerivedCategory.finiteTorAmplitude _ M) :
    (properOpenCoefficientRightTranspose a p.left v.left M =
      (scalarSixPull Λ' (pullback.snd p.left v.left)).map
          ((scalarSixChange a V.left).map
            ((RootCoordinateFace.exchange Λ.X (pullback.fst p.left v.left)
              (pullback.snd p.left v.left) p.left v.left pullback.condition).app M)) ≫
        (scalarDirectImagePullbackData.theta a (pullback.snd p.left v.left)).inv.app
          ((RootCoordinateFace.lower Λ.X (pullback.snd p.left v.left)).obj
            ((scalarSixPull Λ (pullback.fst p.left v.left)).obj M)) ≫
        (scalarSixChange a (pullback p.left v.left)).map
          ((RootCoordinateFace.adjunction Λ.X (pullback.snd p.left v.left)).counit.app
            ((scalarSixPull Λ (pullback.fst p.left v.left)).obj M))) ∧
    (properOpenCoefficientRightTranspose a p.left v.left M =
      (scalarDirectImagePullbackData.theta a (pullback.snd p.left v.left)).inv.app
          ((scalarSixPull Λ v.left).obj ((RootCoordinateFace.lower Λ.X p.left).obj M)) ≫
        (scalarSixChange a (pullback p.left v.left)).map
          ((scalarSixPull Λ (pullback.snd p.left v.left)).map
              ((RootCoordinateFace.exchange Λ.X (pullback.fst p.left v.left)
                (pullback.snd p.left v.left) p.left v.left pullback.condition).app M) ≫
            (RootCoordinateFace.adjunction Λ.X (pullback.snd p.left v.left)).counit.app
              ((scalarSixPull Λ (pullback.fst p.left v.left)).obj M))) ∧
    (properOpenCoefficientRightTranspose a p.left v.left M =
      (scalarDirectImagePullbackData.theta a (pullback.snd p.left v.left)).inv.app
          ((scalarSixPull Λ v.left).obj ((RootCoordinateFace.lower Λ.X p.left).obj M)) ≫
        (scalarSixChange a (pullback p.left v.left)).map
          ((RootCoordinateFace.squareUpper Λ.X (pullback.fst p.left v.left)
              (pullback.snd p.left v.left) p.left v.left pullback.condition).hom.app
                ((RootCoordinateFace.lower Λ.X p.left).obj M) ≫
            (scalarSixPull Λ (pullback.fst p.left v.left)).map
              ((RootCoordinateFace.adjunction Λ.X p.left).counit.app M))) ∧
    ((scalarSixPull Λ (pullback.snd p.left v.left)).map
        ((RootCoordinateFace.exchange Λ.X (pullback.fst p.left v.left)
          (pullback.snd p.left v.left) p.left v.left pullback.condition).app M) ≫
      (RootCoordinateFace.adjunction Λ.X (pullback.snd p.left v.left)).counit.app
        ((scalarSixPull Λ (pullback.fst p.left v.left)).obj M) =
      (RootCoordinateFace.squareUpper Λ.X (pullback.fst p.left v.left)
          (pullback.snd p.left v.left) p.left v.left pullback.condition).hom.app
            ((RootCoordinateFace.lower Λ.X p.left).obj M) ≫
        (scalarSixPull Λ (pullback.fst p.left v.left)).map
          ((RootCoordinateFace.adjunction Λ.X p.left).counit.app M)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
