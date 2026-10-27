/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q57
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import WeilConjectures.RingTheory.Depth
public import Sheaf.RingTheory.PresentationFittingIdeal
import Sheaf.RingTheory.SeparableClosedPointFormalPresentation
import Mathlib.RingTheory.Etale.Kaehler
import Sheaf.TraceFormula.CompletedJacobianDifferentials
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Regular.RegularSequence
import WeilConjectures.RingTheory.FlatLocalDepthFormula

/-!
# The first Fitting ideal and depth at a geometric node

Source: Stacks Project, curves.tex, Tags 0C4D (algebraically closed case), 0C4C, and 0C49
(blueprint: lem-trf-geometric-node-fitting-depth).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace AlgebraicGeometry

/-- A rational geometric node has first Fitting ideal equal to its maximal ideal and depth one,
both before and after completion. The completion isomorphism is only a ring isomorphism.
The Fitting assertion is stated for every finite generating surjection, using the recorded
presentation-minor ideal, so it does not depend on a choice of generators. The completed depth
is written as ideal-depth for the extended maximal ideal, which is the completed maximal ideal.

Source: Stacks Project, curves.tex, Tags 0C4D, 0C4C, and 0C49
(blueprint: lem-trf-geometric-node-fitting-depth).

Proof plan:
1. Apply lem-trf-separable-closed-point-formal-presentation with the identity extension K/K.
   The local ring and its completion are Noetherian local, with residue field K and extended
   maximal ideal. Use lem-trf-rational-nodal-completion-algebra to replace the abstract ring
   isomorphism by a coefficient-compatible presentation K[[u,v]] onto the completion, with
   kernel (uv). Its variable images x,y generate the completed maximal ideal.
2. Differentials of finitely many algebra generators generate the module of differentials.
   Apply lem-weil-pbc-kahler-differentials-localization and the arbitrary-base-change clause
   of lem-trf-fitting-ideal-independence-base-change to R to B and then B to its completion.
3. Apply lem-trf-completed-jacobian-differentials with two variables and the relation uv.
   Its Jacobian column is (y,x); the index-one minors therefore generate (x,y). This proves
   equality of the extended Fitting ideal and the completed maximal ideal.
4. Completion is faithfully flat by lem-weil-pbc-local-completion-faithfully-flat.
   Apply lem-weil-pbc-faithfully-flat-ideal-contraction to descend this ideal equality to B.
5. The model has depth one by lem-trf-binary-quadratic-model-depth with a=c=0 and b=1.
   The ring isomorphism transports regular sequences, hence depth, to the completion.
   Apply lem-weil-pbc-flat-local-depth-formula to completion. Its closed fibre is the field K,
   of depth zero, so B also has depth one. The computation works in characteristic two.
-/
theorem geometricNode_fitting_depth
    (K : Type u) (R : Type v) [Field K] [IsAlgClosed K] [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] (q : Ideal R) [q.IsMaximal]
    (hrational : Function.Bijective (algebraMap K (R ⧸ q)))
    (hnode : Nonempty
      (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
        (Localization.AtPrime q) ≃+*
        (MvPowerSeries (Fin 2) K ⧸ Ideal.span
          ({MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2)} :
            Set (MvPowerSeries (Fin 2) K))))) :
    (∀ (n : ℕ) (π : (Fin n → R) →ₗ[R] KaehlerDifferential K R),
      Function.Surjective π →
        Ideal.map (algebraMap R (Localization.AtPrime q)) (π.presentationFittingIdeal 1) =
          Ideal.map (algebraMap R (Localization.AtPrime q)) q) ∧
    IsLocalRing.depth (R := Localization.AtPrime q) (Localization.AtPrime q) = 1 ∧
    (Ideal.map
      (algebraMap (Localization.AtPrime q)
        (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
          (Localization.AtPrime q)))
      (IsLocalRing.maximalIdeal (Localization.AtPrime q))).depth
      (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
        (Localization.AtPrime q)) = 1 := by
  sorry

end AlgebraicGeometry
