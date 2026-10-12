/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.DivisorModule
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
import Sheaf.AlgebraicGeometry.DvrFieldExtensionOrder
import Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings
import Sheaf.RingTheory.FibrePrimesResidueFields

/-!
# Local orders at rational points after extension of algebraically closed fields

Source: blueprint sec-curve-estimates/sk-prop-ext-invariance,
thm-sc-constant-invariance, affine-case unit quotient paragraph
(blueprint: lem-sc-local-dvr-base-change).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- The unique point over a rational closed point has a DVR stalk, and pullback preserves
normalized orders. Source: blueprint thm-sc-constant-invariance, affine-case unit quotient
paragraph (blueprint: lem-sc-local-dvr-base-change).

Proof:
1. Choose an affine neighbourhood Spec A of P. Its residue field is k because P is closed,
   A is of finite type over the algebraically closed field k. By
   lem-weil-pbc-fibre-ring-primes-residue-fields, points over P correspond to primes of
   (A/m) tensor_k k' = k'. This field has exactly one prime, giving the unique point P'.
2. Localize A tensor_k k' at m(A tensor_k k'). This is the corresponding localization of
   O_{X,P} tensor_k k'. The original stalk is a DVR by
   lem-sc-smooth-connected-curve-local-rings. Apply lem-sc-dvr-field-extension-order:
   the new stalk is a DVR, and a uniformizer stays a uniformizer.
3. The stalk fraction fields are the scheme function fields. Extend the stalk map to
   their fraction fields; the displayed compatibility specifies exactly the rational
   pullback. Unit-times-uniformizer factorizations then have the same integer exponent
   on both sides, giving the equality of Scheme.ord, as used in def-sc-divisor.

The existential integral and locally Noetherian instances only make the function fields
and Scheme.ord well typed; they follow from the smooth connected finite-type curve
hypotheses and their base changes. No such hypothesis is imposed on the input.
Closed points of this finite-type scheme over algebraically closed k are k-rational.
The pullback ring homomorphism is specified on the entire stalk, whose fraction field is
X.functionField, so this condition determines the canonical rational pullback uniquely. -/
theorem Scheme.local_dvr_base_change
    (k k' : Type u) [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']
    [Algebra k k'] (X : Scheme.{u}) (s : X ⟶ Spec (.of k))
    [IsConnectedCurve s] [Smooth s] [IsProper s] (P : X)
    (hP : P ∈ closedPoints X) :
    ∃ (_ : IsIntegral X)
      (_ : IsIntegral (pullback s (Spec.map (CommRingCat.ofHom (algebraMap k k')))))
      (_ : IsLocallyNoetherian X)
      (_ : IsLocallyNoetherian
        (pullback s (Spec.map (CommRingCat.ofHom (algebraMap k k'))))),
    ∃ P' : (pullback s (Spec.map (CommRingCat.ofHom (algebraMap k k'))) : Scheme.{u}),
      pullback.fst s (Spec.map (CommRingCat.ofHom (algebraMap k k'))) P' = P ∧
      (∀ Q : (pullback s (Spec.map (CommRingCat.ofHom (algebraMap k k'))) : Scheme.{u}),
        pullback.fst s (Spec.map (CommRingCat.ofHom (algebraMap k k'))) Q = P → Q = P') ∧
      IsDiscreteValuationRing (X.presheaf.stalk P) ∧
      IsDiscreteValuationRing
        ((pullback s (Spec.map (CommRingCat.ofHom (algebraMap k k')))).presheaf.stalk P') ∧
      ∃ ρ : X.functionField →+*
          (pullback s (Spec.map (CommRingCat.ofHom (algebraMap k k')))).functionField,
        (∀ r : X.presheaf.stalk
            (pullback.fst s (Spec.map (CommRingCat.ofHom (algebraMap k k'))) P'),
          ρ (algebraMap _ X.functionField r) =
            algebraMap _
              (pullback s (Spec.map (CommRingCat.ofHom (algebraMap k k')))).functionField
              ((pullback.fst s
                (Spec.map (CommRingCat.ofHom (algebraMap k k')))).stalkMap P' r)) ∧
        ∀ f : X.functionFieldˣ,
          (pullback s (Spec.map (CommRingCat.ofHom (algebraMap k k')))).ord (ρ f) P' =
            X.ord (f : X.functionField) P := by
  sorry

end AlgebraicGeometry
