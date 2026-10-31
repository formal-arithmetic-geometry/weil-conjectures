/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LisseQlbarRepresentations

/-! # Detecting normalized integral monodromy on finite reductions -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.LisseQlbar

set_option maxHeartbeats 0 in
-- The reduction types contain large canonical coefficient and fibre transports.
/-- If all normalized finite reductions of an integral fibre fix an element, then the
integral action fixes it. Source: `thm-lisse-qlbar-representations`, clause (1),
completeness of the integral fibre.
(blueprint: lem-dl-a1-condensed-lisse-reduction-faithful).

Proof: apply uniqueness in `ReductionComplete` to the reductions of a fixed vector.
Both the vector and its translate have the same reductions by equivariance and the
finite-level hypothesis. The fibre comparison is an isomorphism, so equality on the
actual fibre implies equality on the representation module. -/
theorem integral_action_eq_one_of_reductions
    (l : ℕ) [Fact l.Prime] {X : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) (G : ProfiniteGrp.{u})
    [∀ P, MulAction G ((FiniteEtale.fiber x).obj P)]
    (c : Correspondence l x G) (E : PadicAlgCl.FiniteIntermediateField l)
    (L : ObjectProperty.FullSubcategory (CondensedRing.LocallyFree
      (condensedRingObj (integerRing l E) X)))
    (r : ∀ n : ℕ, integralFiniteReduction l x G c.finite E (c.integral E) L n)
    (hr : ReductionComplete l x G c.finite E (c.integral E) L r)
    (g : G)
    (hg : ∀ n : ℕ,
      letI := Padic.finite_coefficientExtensionRing l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n))
      (((c.finite.e _).functor.obj (r n).etale).obj.ρ g) = 1) :
    ((c.integral E).functor.obj L).ρ g = 1 := by
  let (n : ℕ) : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  ext v
  change (((c.integral E).functor.obj L).ρ g) v = v
  let w := (c.integral E).comparison.hom.app L v
  let t := fun n ↦ reductionOnFibre (integerRing l E) x G c.finite L.obj _
    (r n).etale (r n).quotient w
  obtain ⟨z, hz, hu⟩ := hr t (fun n ↦ ⟨w, rfl, rfl⟩)
  have hw : w = z := hu w (fun _ ↦ rfl)
  have hgv : (c.integral E).comparison.hom.app L
      (((c.integral E).functor.obj L).ρ g v) = z := by
    apply hu
    intro n
    exact ((r n).equivariant g v).trans (LinearMap.congr_fun (hg n) _)
  have heq := hgv.trans hw.symm
  have h := congrArg ((c.integral E).comparison.inv.app L) heq
  simpa only [w, ← ConcreteCategory.comp_apply,
    (c.integral E).comparison.hom_inv_id_app, ConcreteCategory.id_apply] using h

end AlgebraicGeometry.ProEtale.LisseQlbar
