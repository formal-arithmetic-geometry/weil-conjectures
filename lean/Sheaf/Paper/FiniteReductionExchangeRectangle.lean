/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FourArrows
import all Sheaf.Paper.FiniteReductionPullbackSquare
import all Sheaf.CategoryTheory.ExchangeMateCube

/-! The finite projection/exchange rectangle in the intrinsic quotient-ring coordinates.
Source: Stacks Project, Tag 0E48.
(blueprint: lem-weil-pbc-intrinsic-finite-exchange-rectangle) -/

@[expose] public noncomputable section
set_option autoImplicit false


-- Avoid replaying the large dependent coefficient transports for tactic linting.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory
namespace AlgebraicGeometry.Scheme
attribute [local instance 2000] proEtaleRingModules_hasDerivedCategory
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  proEtaleRingModulePullback proEtaleRingDerivedAdjunction
  proEtaleAmbientRingedPullbackComparison completedAdicDerivedChange

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

private theorem finiteProjection_mate {U V : Scheme.{t}} (u : U ⟶ V)
    (n : ℕ) (E : d.derived U) :
    (mateEquiv
      (proEtaleRingDerivedAdjunction u (d.completedRing V) (d.completedRing U)
        (d.integralRingIso u))
      (proEtaleRingDerivedAdjunction u (d.finiteRing V n) (d.finiteRing U n)
        (d.finiteRingIso u n))
      (TwoSquare.mk _ _ _ _ (d.chi u n).hom)).app E = d.finiteProjection u E n :=
  mate_app_eq_adjunct
    (proEtaleRingDerivedAdjunction u (d.completedRing V) (d.completedRing U)
      (d.integralRingIso u))
    (proEtaleRingDerivedAdjunction u (d.finiteRing V n) (d.finiteRing U n)
      (d.finiteRingIso u n)) (d.chi u n).hom E

private theorem integralExchange_mate
    (sq : ChosenCartesianSquare g' f' f g) :
    (mateEquiv
      (proEtaleRingDerivedAdjunction f (d.completedRing Y) (d.completedRing X)
        (d.integralRingIso f))
      (proEtaleRingDerivedAdjunction f' (d.completedRing Y') (d.completedRing X')
        (d.integralRingIso f'))
      (TwoSquare.mk (d.pull g) (d.pull f) (d.pull f') (d.pull g')
        (proEtaleAmbientRingedPullbackComparison sq
          (d.completedRing X) (d.completedRing Y) (d.completedRing X') (d.completedRing Y')
          (d.integralRingIso f) (d.integralRingIso g) (d.integralRingIso g')
          (d.integralRingIso f') (d.integral_coherent sq)).hom)).natTrans =
      d.integralExchange sq := rfl

private theorem finiteExchange_mate
    (sq : ChosenCartesianSquare g' f' f g) (n : ℕ) :
    (mateEquiv
      (proEtaleRingDerivedAdjunction f (d.finiteRing Y n) (d.finiteRing X n)
        (d.finiteRingIso f n))
      (proEtaleRingDerivedAdjunction f' (d.finiteRing Y' n) (d.finiteRing X' n)
        (d.finiteRingIso f' n))
      (TwoSquare.mk (d.finitePull g n) (d.finitePull f n)
        (d.finitePull f' n) (d.finitePull g' n)
        (proEtaleAmbientRingedPullbackComparison sq
          (d.finiteRing X n) (d.finiteRing Y n) (d.finiteRing X' n) (d.finiteRing Y' n)
          (d.finiteRingIso f n) (d.finiteRingIso g n) (d.finiteRingIso g' n)
          (d.finiteRingIso f' n) (d.finite_coherent sq n)).hom)).natTrans =
      d.finiteExchange sq n := rfl

private def finiteProjectionNat {U V : Scheme.{t}} (u : U ⟶ V) (n : ℕ) :
    d.push u ⋙ d.reduction V n ⟶ d.reduction U n ⋙ d.finitePush u n where
  app E := d.finiteProjection u E n
  naturality E E' a := by
    let m := (mateEquiv
      (proEtaleRingDerivedAdjunction u (d.completedRing V) (d.completedRing U)
        (d.integralRingIso u))
      (proEtaleRingDerivedAdjunction u (d.finiteRing V n) (d.finiteRing U n)
        (d.finiteRingIso u n))
      (TwoSquare.mk _ _ _ _ (d.chi u n).hom)).natTrans
    have he (N : d.derived U) : m.app N = d.finiteProjection u N n :=
      finiteProjection_mate d u n N
    simpa only [he] using m.naturality a

private theorem finiteProjectionNat_mate {U V : Scheme.{t}} (u : U ⟶ V) (n : ℕ) :
    (mateEquiv
      (proEtaleRingDerivedAdjunction u (d.completedRing V) (d.completedRing U)
        (d.integralRingIso u))
      (proEtaleRingDerivedAdjunction u (d.finiteRing V n) (d.finiteRing U n)
        (d.finiteRingIso u n))
      (TwoSquare.mk _ _ _ _ (d.chi u n).hom)).natTrans = finiteProjectionNat d u n := by
  apply NatTrans.ext
  funext E
  exact finiteProjection_mate d u n E

private theorem finiteRectangle_nat (sq : ChosenCartesianSquare g' f' f g) (n : ℕ) :
    Functor.whiskerRight (finiteProjectionNat d f n) (d.finitePull g n) ≫
      Functor.whiskerLeft (d.reduction X n) (d.finiteExchange sq n) =
    Functor.whiskerLeft (d.push f) (d.chi g n).hom ≫
      Functor.whiskerRight (d.integralExchange sq) (d.reduction Y' n) ≫
      Functor.whiskerLeft (d.pull g') (finiteProjectionNat d f' n) ≫
      Functor.whiskerRight (d.chi g' n).inv (d.finitePush f' n) := by
  exact exchangeMate_forward_nat_coherent
    (F := d.pull f) (R := d.push f)
    (K := d.pull f') (S := d.push f')
    (F' := d.finitePull f n) (R' := d.finitePush f n)
    (K' := d.finitePull f' n) (S' := d.finitePush f' n)
    (G := d.pull g) (H := d.pull g')
    (G' := d.finitePull g n) (H' := d.finitePull g' n)
    (proEtaleRingDerivedAdjunction f (d.completedRing Y) (d.completedRing X)
      (d.integralRingIso f))
    (proEtaleRingDerivedAdjunction f' (d.completedRing Y') (d.completedRing X')
      (d.integralRingIso f'))
    (proEtaleRingDerivedAdjunction f (d.finiteRing Y n) (d.finiteRing X n)
      (d.finiteRingIso f n))
    (proEtaleRingDerivedAdjunction f' (d.finiteRing Y' n) (d.finiteRing X' n)
      (d.finiteRingIso f' n))
    (d.reduction Y n) (d.reduction X n) (d.reduction Y' n) (d.reduction X' n)
    (d.chi f n) (d.chi g n) (d.chi g' n) (d.chi f' n)
    (proEtaleAmbientRingedPullbackComparison sq
      (d.completedRing X) (d.completedRing Y) (d.completedRing X') (d.completedRing Y')
      (d.integralRingIso f) (d.integralRingIso g) (d.integralRingIso g')
      (d.integralRingIso f') (d.integral_coherent sq)).hom
    (proEtaleAmbientRingedPullbackComparison sq
      (d.finiteRing X n) (d.finiteRing Y n) (d.finiteRing X' n) (d.finiteRing Y' n)
      (d.finiteRingIso f n) (d.finiteRingIso g n) (d.finiteRingIso g' n)
      (d.finiteRingIso f' n) (d.finite_coherent sq n)).hom
    (finiteReductionSquare_nat d sq n)
    (finiteProjectionNat d f n) (finiteProjectionNat d f' n)
    (d.integralExchange sq) (d.finiteExchange sq n)
    (integralExchange_mate d sq) (finiteExchange_mate d sq n)
    (finiteProjectionNat_mate d f n) (finiteProjectionNat_mate d f' n)

/-- The finite projection arrows intertwine the ambient and finite exchange maps.
This holds for every derived input, before using a finite-origin witness.
Source: Stacks Project, Tag 0E48
(blueprint: lem-weil-pbc-intrinsic-finite-exchange-rectangle).
Proof: the reduction/pullback comparisons form a commuting cube on inverse-image
functors. Apply exchangeMate_cube to this cube. The mates on the f and f' edges
are exactly the finite projection arrows by their counit-adjunct definitions.
Postcompose with direct image of the inverse g' comparison and cancel that
comparison. The resulting identity is the stated finite rectangle. -/
theorem finiteReductionExchange_rectangle
    (sq : ChosenCartesianSquare g' f' f g) (K : d.derived X) (n : ℕ) :
    (d.finitePull g n).map (d.finiteProjection f K n) ≫
        (d.finiteExchange sq n).app ((d.reduction X n).obj K) =
      (d.chi g n).hom.app ((d.push f).obj K) ≫
        (d.reduction Y' n).map ((d.integralExchange sq).app K) ≫
        d.finiteProjection f' ((d.pull g').obj K) n ≫
        (d.finitePush f' n).map ((d.chi g' n).inv.app K) := by
  exact congrArg (fun z ↦ z.app K) (finiteRectangle_nat d sq n)

end AlgebraicGeometry.Scheme
