/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.Paper.BoundedConstructibleComplete
public import Sheaf.Paper.CompletedBaseChangeMap
import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.FiniteLevelProEtaleBaseChange
import Sheaf.Paper.CompletedExchangeCoherence
import Sheaf.Paper.FourArrows
import Sheaf.Paper.CompletedTowerCompatibility
import Sheaf.Paper.CompletedAdicLevelwiseIsomorphismCones
import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Paper.CompletedMapReduction

/-! # Completed proper base change with compatible retained origins

Source: Stacks 09C9; blueprint order 1354
(blueprint: thm-weil-pbc-complete-proetale).
The published actual-coefficient exchange is used without any auxiliary presentation.
Neither constructibility nor a common cohomological bound is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The specified completed exchange is invertible for an intrinsically complete
object with compatible retained bounded-below etale origins. The strict reduction
tower records canonical computations; no constructibility condition is imposed.
Source: Stacks 09C9 (blueprint: thm-weil-pbc-complete-proetale).
Proof: intrinsic completeness identifies K with the derived limit of its canonical
quotient tower. The perfect projection mate identifies reduction of Rf K with strict
Rf of the reductions. At each positive level the retained bounded-below etale origin
allows finite-coefficient proper base change. Compatibility identifies its maps with
the evaluated canonical tower exchange. Evaluation detects isomorphisms of strict
derived towers because cohomology is pointwise. Apply the actual Rlim functor to this
isomorphism and compose with the specified projection and direct-image/limit
isomorphisms. The resulting ordered composite is exactly d.completedExchange sq K in the
actual completed-ring category. -/
theorem completeProetale_isIso
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g) [IsProper f]
    (K : PbcCompletedDerived X d)
    (_hK : PbcIsIntrinsicallyComplete X d K)
    (_origins : PbcHasCompatibleEtaleOrigins X d K) :
    IsIso (d.completedExchange sq K) := by
  sorry

end AlgebraicGeometry.Scheme
