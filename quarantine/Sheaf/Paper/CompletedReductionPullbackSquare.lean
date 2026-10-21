/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.StrictTowerOperations
public import Sheaf.Paper.CompletedDirectImageLimits

/-! Pullback composition and completed reduction on the strict diagram category.
Source: Stacks Project, Tags 0D6D and 0E48.
(blueprint: lem-weil-pbc-completed-reduction-pullback-square) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory
namespace AlgebraicGeometry.Scheme
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The integral ringed square retains the specified completed coefficient maps.
Source: Stacks Tag 0D6D
(blueprint: lem-weil-pbc-completed-reduction-pullback-square). -/
def AdicCoefficientDatum.integralTowerRingedSquare
    (sq : ChosenCartesianSquare g' f' f g) : StrictTowerRingedSquare sq where
  RY := d.completedRing Y
  RX := d.completedRing X
  RY' := d.completedRing Y'
  RX' := d.completedRing X'
  cf := d.integralRingIso f
  cg := d.integralRingIso g
  cg' := d.integralRingIso g'
  cf' := d.integralRingIso f'
  coherent := d.integral_coherent sq

/-- The normalized completed reduction comparisons respect the inverse-image square.
This is an equation before taking mates and in the full derived diagram category.
Source: blueprint completed-exchange-coherence, tensor/pullback coherence in its
first two proof sentences; Stacks Tags 0D6D and 0E48
(blueprint: lem-weil-pbc-completed-reduction-pullback-square).

Proof: take a flat-term K-flat representative P on Y. Its two successive inverse
images remain flat-term K-flat. The canonical geometric composition comparison is
localization of the ordinary compositor whose right-adjoint conjugate is restriction
along Over.pullbackComp. At each coefficient level the ordinary reduction comparison
is tensor balancing; its two composites around the square send a pure tensor to its
inverse image with the same quotient scalar. Naturality of the ring projections and
the quotient transition maps makes this an equality of strict tower-complex maps.
Use the defining normalization equations for completedReductionPullbackIso on all
four edges. The ordinary equality and the factorization equations for derived
pullback give the displayed equation after cancellation of the invertible K-flat
counits. Finally resolve an arbitrary M by P and use naturality across the resulting
quasi-isomorphism. This proves equality of strict derived maps, without assuming
that derived evaluation is faithful. Zero complexes, zero coefficient rings and
empty schemes satisfy the same tensor formulas. -/
theorem completedReductionPullback_square
    (sq : ChosenCartesianSquare g' f' f g) :
    Functor.whiskerRight (d.reductionTowerPullbackIso g).hom (d.towerPull f') ≫
      Functor.whiskerLeft (d.pull g) (d.reductionTowerPullbackIso f').hom ≫
      Functor.whiskerRight
        (proEtaleAmbientRingedPullbackComparison sq
          (d.completedRing X) (d.completedRing Y) (d.completedRing X') (d.completedRing Y')
          (d.integralRingIso f) (d.integralRingIso g) (d.integralRingIso g')
          (d.integralRingIso f') (d.integral_coherent sq)).hom
        (completedReductionTower X' d) =
    Functor.whiskerLeft (completedReductionTower Y d)
        (d.integralTowerRingedSquare sq).exchangeTowerSquare.hom ≫
      Functor.whiskerRight (d.reductionTowerPullbackIso f).hom (d.towerPull g') ≫
      Functor.whiskerLeft (d.pull f) (d.reductionTowerPullbackIso g').hom := by
  sorry

end AlgebraicGeometry.Scheme
