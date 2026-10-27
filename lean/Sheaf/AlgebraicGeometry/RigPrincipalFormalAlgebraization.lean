/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Sheaf.AlgebraicGeometry.FormalCompletionGeometry
public import Sheaf.AlgebraicGeometry.SupportedCenteredBlowupTowers
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.FiniteType
public import WeilConjectures.RingTheory.GRing
public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.Blowup.Gluing
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
import Sheaf.RingTheory.FieldsExcellent
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.AlgebraicGeometry.SupportedFormalBlowupAlgebraization

/-! # Algebraization of principal rig-regular formal varieties

Source: Temkin, Non-embedded Desingularization, Remarks 3.1.3(ii), 3.1.4(i)--(iii),
section 3.3.1, and the first sentence of section 3.4.1; sections 2.4.4--2.4.8
for completion of blowups (blueprint: lem-per-rig-principal-formal-algebraization).

A principal affine formal pair is given in its complete-ring coordinates. Its
reduced closed fibre is the quotient by the radical of its specified principal ideal.
An isomorphism of complete rings carrying the extended principal ideal to that ideal
is precisely an isomorphism of these formal affine pairs; the coefficient field is
not required to be preserved. The tower comparison uses the existing infinitesimal
formal-scheme coordinates and retains every ordered center ideal.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A reduced principal affine rig-regular characteristic-zero formal variety admits
an Elkik algebraization, and every finite supported ordinary blowup tower completes
with all its centers in their original order. The isomorphism is of formal pairs,
expressed by its complete-ring isomorphism and equality of the distinguished ideals.
The output field need not be the input field, and no field structure is imposed on
that isomorphism.

Source: Temkin, Non-embedded Desingularization, Remarks 3.1.3(ii), 3.1.4(i)--(iii),
section 3.3.1, section 3.4.1 first sentence, and sections 2.4.4--2.4.8
(blueprint: lem-per-rig-principal-formal-algebraization).

Proof plan:
1. Choose a field of definition of the reduced closed fibre. By
   lem-per-principal-formal-coefficient-presentation lift its map to B and present B
   as a quotient of the t-adic completion of k[t,x_1,...,x_r], with t mapping to pi.
   This preserves the actual principal ideal, not only its radical.
2. Rig-regularity makes B[1/pi] regular: a prime avoiding pi cannot contain its
   singular ideal. Apply lem-per-regular-generic-continuous-jacobian to obtain a
   conormal splitting after multiplication by a power of t. Multiples of that power
   give the corresponding splittings by scaling.
3. Fields are excellent by lem-exc-fields-excellent, and k[t] is excellent by
   lem-exc-finite-type-localization-excellent, hence a Noetherian G-ring. Apply
   lem-per-g-ring-rig-smooth-algebraization to the presentation and splitting. Obtain
   a finite type k[t]-algebra C whose completion is B, preserving t. It is also finite
   type over k by adjoining t to its finite set of generators.
4. C is excellent by lem-exc-finite-type-localization-excellent. Apply
   lem-per-principal-completion-good-neighborhood to invert g in 1+tC. The resulting
   A is reduced, t is a non-zero-divisor, and A[1/t] is regular. Localization at g
   preserves the completion and its distinguished ideal. This is the Elkik pair;
   regularity away from t says that every nonregular prime contains t.
5. A is excellent and its principal ideal is coherent. Apply
   lem-per-supported-formal-blowup-algebraization to each finite supported tower.
   In a Noetherian ring support over V(t) is equivalent to containing a positive
   power of t. Its Completion comparison identifies every extended center ideal,
   and CentersAgree identifies the center schemes. The fixed ideal-preserving
   complete-ring isomorphism identifies the base with the original formal pair.
   No identity or empty-center stage is removed; length zero is included. -/
theorem rigPrincipalFormalAlgebraization
    (B : CommRingCat.{u}) [IsNoetherianRing B] [_root_.IsReduced B]
    (pi : B) (hpi : pi ∈ nonZeroDivisors B)
    [IsAdicComplete (Ideal.span {pi}) B]
    (hQE : _root_.IsQuasiExcellent B)
    (hvar : ∃ (k : Type u) (_ : Field k) (_ : CharZero k)
      (f : k →+* B ⧸ (Ideal.span {pi}).radical), f.FiniteType)
    (hrig : ∃ N : ℕ, 0 < N ∧
      Ideal.span {pi} ^ N ≤ absoluteSingularIdeal B) :
    ∃ (k : Type u) (_ : Field k) (_ : CharZero k)
      (A : CommRingCat.{u}) (f : k →+* A) (a : A),
      f.FiniteType ∧ _root_.IsReduced A ∧ a ∈ nonZeroDivisors A ∧
      (∀ p : PrimeSpectrum A,
        ¬ IsRegularLocalRing (Localization.AtPrime p.asIdeal) → a ∈ p.asIdeal) ∧
      ∃ e : AdicCompletion (Ideal.span {a}) A ≃+* B,
        (Ideal.span {a}).map
          (e.toRingHom.comp (algebraMap A (AdicCompletion (Ideal.span {a}) A))) =
            Ideal.span {pi} ∧
        ∀ (r : ℕ) (T : AdicFormal.OrdinaryTower
          (AdicFormal.affineIdeal A (Ideal.span {a})) r),
          ∃ (F : AdicFormal.FormalTower (AdicFormal.affineIdeal A (Ideal.span {a})) r)
            (c : AdicFormal.Completion T F), c.CentersAgree := by
  sorry

end AlgebraicGeometry
