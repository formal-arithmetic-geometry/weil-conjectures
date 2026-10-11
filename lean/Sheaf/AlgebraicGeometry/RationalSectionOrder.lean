/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings
import Sheaf.AlgebraicGeometry.InvertibleModuleGenericStalk

/-!
# Orders of a rational section of an invertible module

Source: Stacks Project, Divisors, Section 02SE before Definition 02SF and Lemma 02SG
(blueprint: lem-sc-rational-section-order).
-/

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Changing a local generator does not change the order of a nonzero rational section,
and only finitely many closed points have nonzero order.
Source: Stacks Project, Divisors, Section 02SE before Definition 02SF and Lemma 02SG
(blueprint: lem-sc-rational-section-order).

The integral instance and normalized valuations are taken from
`lem-sc-smooth-connected-curve-local-rings`, rather than imposed as extra hypotheses.
`lam` is the specialization map of stalks used in `lem-sc-invertible-module-generic-stalk`.
A generator means that its singleton spans the local stalk. The existential coefficient in
the finite-support set avoids making any choice of local generators; the first clause and
`lem-sc-invertible-module-generic-stalk` make it the same set for every choice.

Proof:
1. At a closed point, any two generators of the free rank-one stalk differ by a local unit
   (`lem-sc-invertible-module-generic-stalk`). Their coefficients therefore differ by the
   inverse of that unit. The normalized DVR valuation of a unit is zero, proving equality.
2. Trivialize the invertible module near the generic point (`def-sc-invertible-module`) and
   choose a nonempty affine open there. Its generic generator is a basis
   (`lem-sc-invertible-module-generic-stalk`), so write the section as g times that basis.
   Express g as a/b with nonzero a,b in the affine ring
   (`lem-sc-integral-function-field-affine-fraction`). On the nonempty principal open D(ab),
   both a and b are units, so the section itself generates the module.
3. At every closed point in this open, its coefficient relative to any generator is a unit,
   hence has order zero. The remaining points lie in the proper closed complement.
   A length-one chain in that complement would extend to a length-two chain in the curve,
   contradicting dimension one (`def-sc-curves`). Thus the complement has dimension at most
   zero and is finite (`lem-sc-dim0-finite`), proving finite support. -/
theorem rational_section_order
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (L : C.Modules) [L.IsInvertible] :
    let hC := Classical.choose (C.smooth_connected_curve_local_rings k f)
    letI := hC
    let h := Classical.choose_spec (C.smooth_connected_curve_local_rings k f)
    let η := genericPoint C
    let lam := fun x : C ↦
      TopCat.Presheaf.stalkSpecializes L.val.presheaf
        ((genericPoint_spec C).specializes (Set.mem_univ x))
    let v := fun P : {P : C // P ∈ closedPoints C} ↦
      Classical.choose ((h.2.2.2.2.2.2.2.2 P.val P.property).2.2)
    ∀ (s : ↑(TopCat.Presheaf.stalk L.val.presheaf η)), s ≠ 0 →
      (∀ (P : {P : C // P ∈ closedPoints C})
        (e e' : ↑(TopCat.Presheaf.stalk L.val.presheaf P.val)),
        Submodule.span (C.presheaf.stalk P.val) {e} = ⊤ →
        Submodule.span (C.presheaf.stalk P.val) {e'} = ⊤ →
        ∀ g g' : C.functionFieldˣ,
          s = (g : C.functionField) • lam P.val e →
          s = (g' : C.functionField) • lam P.val e' →
          Multiplicative.toAdd (v P g) = Multiplicative.toAdd (v P g')) ∧
      Set.Finite {P : C | ∃ hP : P ∈ closedPoints C,
        ∃ e : ↑(TopCat.Presheaf.stalk L.val.presheaf P),
          Submodule.span (C.presheaf.stalk P) {e} = ⊤ ∧
          ∃ g : C.functionFieldˣ,
            s = (g : C.functionField) • lam P e ∧
              Multiplicative.toAdd (v ⟨P, hP⟩ g) ≠ 0} :=
  sorry

end AlgebraicGeometry.Scheme.Modules
