/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q21
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import WeilConjectures.RingTheory.GradedAlgebra.Standard

/-! # The induced grading on a homogeneous coordinate quotient

Source: Stacks Project, Algebra, Tag 00JL, section-graded, graded quotient rings.
(blueprint: def-sfb-coordinate-quotient-grading)
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

variable {k : Type u} [Field k] {N : ℕ}

/-- The actual image of the degree-m polynomial submodule in the quotient ring.
Source: Stacks, Tag 00JL (blueprint: def-sfb-coordinate-quotient-grading). -/
def coordinateQuotientPiece
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k))
    (m : ℕ) : Submodule k (MvPolynomial (ULift.{u} (Fin (N + 1))) k ⧸ J.toIdeal) :=
  (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k m).map
    (Ideal.Quotient.mkₐ k J.toIdeal).toLinearMap

/-- Compatibility of a quotient decomposition with the actual polynomial projections.
Source: Stacks, Tag 00JL (blueprint: def-sfb-coordinate-quotient-grading). -/
def coordinateQuotientGradingCompatible
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k))
    (g : GradedAlgebra (coordinateQuotientPiece J)) : Prop :=
  letI := g
  ∀ (m : ℕ) (x : MvPolynomial (ULift.{u} (Fin (N + 1))) k),
    GradedRing.proj (coordinateQuotientPiece J) m (Ideal.Quotient.mk J.toIdeal x) =
      Ideal.Quotient.mk J.toIdeal
        (GradedRing.proj (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k) m x)

/-- The induced grading exists uniquely, with projections descended from polynomials.
Source: Stacks, Tag 00JL (blueprint: def-sfb-coordinate-quotient-grading).
Proof: homogeneity of J makes every polynomial homogeneous projection preserve J,
so it descends to the quotient. The descended projections have finite support and
sum to the identity, because the original polynomial decomposition does. They give
an inverse to the sum map from the direct sum of the displayed image submodules.
Images of homogeneous products multiply in the sum of the two degrees, and the unit
has degree zero. Thus these submodules form a graded algebra. Its decomposition is
unique because it must be the inverse of their fixed sum map; all remaining fields
are propositions. This also covers the zero quotient. -/
theorem existsUnique_coordinateQuotientGrading
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k)) :
    ∃! g : GradedAlgebra (coordinateQuotientPiece J), coordinateQuotientGradingCompatible J g := by
  classical
  let B := MvPolynomial (ULift.{u} (Fin (N + 1))) k
  let P := MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k
  let Q := coordinateQuotientPiece J
  let q := Ideal.Quotient.mk J.toIdeal
  let f (i : ℕ) : P i →+ Q i :=
    { toFun := fun x ↦ ⟨q x, ⟨x, x.property, rfl⟩⟩
      map_zero' := Subtype.ext (map_zero q)
      map_add' := fun x y ↦ Subtype.ext (map_add q (x : B) (y : B)) }
  let d : B →+ DirectSum ℕ (fun i ↦ Q i) :=
    (DirectSum.map f).comp (DirectSum.decomposeAddEquiv P).toAddMonoidHom
  have hd (x : B) (hx : x ∈ J.toIdeal) : d x = 0 := by
    ext i
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (J.isHomogeneous i hx)
  let e : (B ⧸ J.toIdeal) →+ DirectSum ℕ (fun i ↦ Q i) :=
    QuotientAddGroup.lift J.toIdeal.toAddSubgroup d hd
  have he (x : B) : e (q x) = d x := rfl
  have hd_coe (i : ℕ) (x : P i) : d x = DirectSum.of (fun i ↦ Q i) i (f i x) := by
    change DirectSum.map f (DirectSum.decompose P x) = _
    rw [DirectSum.decompose_coe, DirectSum.map_of]
  have hsum : (DirectSum.coeAddMonoidHom Q).comp d = q.toAddMonoidHom := by
    apply AddMonoidHom.ext
    intro x
    induction x using DirectSum.Decomposition.inductionOn P with
    | zero => simp
    | homogeneous x =>
      rw [AddMonoidHom.comp_apply, hd_coe, DirectSum.coeAddMonoidHom_of]
      rfl
    | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (· + ·) hx hy
  have hl : (DirectSum.coeAddMonoidHom Q).comp e = AddMonoidHom.id _ := by
    ext x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact DFunLike.congr_fun hsum b
  have hr : e.comp (DirectSum.coeAddMonoidHom Q) = AddMonoidHom.id _ := by
    apply DirectSum.addHom_ext
    intro i x
    obtain ⟨b, hb, hbx⟩ := x.property
    have hx : f i ⟨b, hb⟩ = x := Subtype.ext hbx
    change e ((DirectSum.coeAddMonoidHom Q) (DirectSum.of _ i x)) =
      DirectSum.of _ i x
    calc
      _ = e (x : B ⧸ J.toIdeal) :=
        congrArg e (DirectSum.coeAddMonoidHom_of Q i x)
      _ = _ := by
        rw [← hx]
        exact (he b).trans (hd_coe i ⟨b, hb⟩)
  let gm : SetLike.GradedMonoid Q :=
    { one_mem := ⟨1, SetLike.GradedOne.one_mem (A := P), map_one q⟩
      mul_mem := by
        intro i j a b ha hb
        obtain ⟨x, hx, rfl⟩ := ha
        obtain ⟨y, hy, rfl⟩ := hb
        exact ⟨x * y, SetLike.mul_mem_graded hx hy, map_mul q x y⟩ }
  let g : GradedAlgebra Q :=
    { gm, DirectSum.Decomposition.ofAddHom Q e hl hr with }
  refine ⟨g, ?_, ?_⟩
  · intro m x
    change ((e (q x) m : Q m) : B ⧸ J.toIdeal) = _
    rfl
  · intro g' _
    cases g'
    cases g
    congr 1
    exact Subsingleton.elim _ _

/-- The unique induced quotient grading. The submodules are explicit images; only the
proof that their sum decomposition is invertible is postponed in the named theorem.
Source: Stacks, Tag 00JL (blueprint: def-sfb-coordinate-quotient-grading). -/
noncomputable instance coordinateQuotientGrading
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k)) :
    GradedAlgebra (coordinateQuotientPiece J) :=
  (existsUnique_coordinateQuotientGrading J).choose

end
end AlgebraicGeometry
