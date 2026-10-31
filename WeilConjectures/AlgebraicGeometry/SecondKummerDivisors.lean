/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Kummer
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard

/-!
# Second Kummer cohomology of a curve

Source: blueprint sec-curve-estimates, sk-prop-h2, lem-sc-second-kummer-divisors;
Stacks Project, Tags 03PK and 03RQ, the long exact Kummer sequence
(blueprint: lem-sc-second-kummer-divisors).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsCurve

/-- Source: blueprint lem-sc-second-kummer-divisors; Stacks Project, Tags 03PK and 03RQ.
For any curve over an algebraically closed field and any positive invertible integer n,
second Kummer cohomology is Pic/n via the Kummer coboundary, and H² of Gₘ vanishes.

Proof step 1: `lem-sc-brauer-zero-all-curves` gives vanishing of H²(Gₘ). Invertibility
of n in the field implies invertibility on C. By `lem-sc-kummer-exact`, the sequence
of `def-sc-kummer-sequence` is short exact.
Proof step 2: `Scheme.exact_sheafH_rootsOfUnitySheaf_two` already gives the
long exact Kummer sequence for the specified boundary: its kernel is n H¹(Gₘ),
and it is surjective because H²(Gₘ) vanishes. Compose this boundary with the
canonical group isomorphism of `lem-sc-h1-gm-pic`. Additivity identifies its kernel
with n Pic. The first isomorphism theorem gives Pic/n → H²(μₙ); invert it for the
displayed orientation. Its defining equation on quotient classes gives the boundary
compatibility. Proof irrelevance identifies the boundaries for every proof of
invertibility on C.
(blueprint: lem-sc-second-kummer-divisors) -/
theorem exists_addEquiv_secondKummer_divisors {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f] (n : ℕ) (hn : (n : k) ≠ 0) :
    (∃ e : Sheaf.H (C.rootsOfUnitySheaf n) 2 ≃+
        Additive C.Pic ⧸ (zsmulAddGroupHom (α := Additive C.Pic) (n : ℤ)).range,
      ∀ (hnC : IsUnit (n : Γ(C, ⊤))) (L : Additive C.Pic),
        e (C.kummerδ₁ n hnC (Scheme.Pic.toCohomologicalPicardGroupAddEquiv C L)) =
          QuotientAddGroup.mk L) ∧
      Subsingleton C.CohomologicalBrauerGroup := by
  classical
  have hBr : Subsingleton C.CohomologicalBrauerGroup :=
    subsingleton_cohomologicalBrauerGroup f
  have hnC0 : IsUnit (n : Γ(C, ⊤)) := by
    simpa using hn.isUnit.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom
  let P := Scheme.Pic.toCohomologicalPicardGroupAddEquiv C
  let δ := (C.kummerδ₁ n hnC0).comp P.toAddMonoidHom
  have hδ : Function.Surjective δ := by
    intro x
    obtain ⟨L, hL⟩ := ((C.exact_sheafH_rootsOfUnitySheaf_two n hnC0).2.1 x).1
      (Subsingleton.elim _ _)
    exact ⟨P.symm L, by simpa [δ] using hL⟩
  have hker : δ.ker =
      (zsmulAddGroupHom (α := Additive C.Pic) (n : ℤ)).range := by
    ext L
    change C.kummerδ₁ n hnC0 (P L) = 0 ↔ _
    rw [← AddMonoidHom.mem_ker, (C.exact_sheafH_rootsOfUnitySheaf_two n hnC0).1]
    constructor
    · rintro ⟨M, hM⟩
      refine ⟨P.symm M, ?_⟩
      apply P.injective
      simpa only [map_zsmul, AddEquiv.apply_symm_apply, zsmulAddGroupHom_apply] using hM
    · rintro ⟨M, rfl⟩
      exact ⟨P M, by simp only [zsmulAddGroupHom_apply, map_zsmul]⟩
  let e := (QuotientAddGroup.quotientKerEquivOfSurjective δ hδ).symm.trans
    (QuotientAddGroup.quotientAddEquivOfEq hker)
  refine ⟨⟨e, ?_⟩, hBr⟩
  intro hnC L
  change e (δ L) = QuotientAddGroup.mk L
  have hmk : (QuotientAddGroup.quotientKerEquivOfSurjective δ hδ)
      (QuotientAddGroup.mk L) = δ L := rfl
  rw [← hmk]
  dsimp only [e, AddEquiv.trans_apply]
  rw [AddEquiv.symm_apply_apply]
  rfl

end AlgebraicGeometry.IsCurve
