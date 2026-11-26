/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.DirectSum.Ring
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The associated graded ring of an ideal

The associated graded ring `gr_J(A) = ⨁ J^n / J^(n+1)` of an ideal `J`, with the multiplication
induced by that of `A`.

The ring structure is the one of Mathlib's `DirectSum.commRing` for the graded
multiplication `associatedGradedMul`, so its addition and zero are those of the
direct sum by definition.

## References

* [Stacks, Tag 05GH], proof
* [Stacks, Tag 00JM]
* [Stacks, Tag 07XA]
-/

@[expose] public section

universe u

open DirectSum

namespace Ideal

variable {A : Type u} [CommRing A]

/-- The degree `n` quotient `J^n / J^(n+1)`. -/
abbrev associatedGradedPiece (J : Ideal A) (n : ℕ) : Type u :=
  (J ^ n : Submodule A A) ⧸
    (Submodule.comap (J ^ n).subtype (J ^ (n + 1)))

/-- The additive direct sum of the quotients `J^n / J^(n+1)`. -/
abbrev associatedGraded (J : Ideal A) : Type u :=
  ⨁ n : ℕ, associatedGradedPiece J n

/-- The bilinear map `J^n × J^m → J^(n+m)/J^(n+m+1)`, `(a, b) ↦ ab mod J^(n+m+1)`. -/
def associatedGradedMulAux (J : Ideal A) (n m : ℕ) :
    (J ^ n : Ideal A) →ₗ[A] (J ^ m : Ideal A) →ₗ[A] associatedGradedPiece J (n + m) :=
  LinearMap.mk₂ A
    (fun a b => Submodule.Quotient.mk
      (⟨a.1 * b.1, by simpa [pow_add] using Ideal.mul_mem_mul a.2 b.2⟩ :
        (J ^ (n + m) : Ideal A)))
    (fun a a' b => by
      rw [← Submodule.Quotient.mk_add]; congr 1; ext; simp [add_mul])
    (fun r a b => by
      rw [← Submodule.Quotient.mk_smul]; congr 1; ext; simp [mul_assoc])
    (fun a b b' => by
      rw [← Submodule.Quotient.mk_add]; congr 1; ext; simp [mul_add])
    (fun r a b => by
      rw [← Submodule.Quotient.mk_smul]; congr 1; ext; simp [mul_left_comm])

/-- The product of a representative in `J^(n+1)` with one in `J^m` lies in `J^(n+m+1)`, so its class
vanishes. -/
theorem associatedGradedMulAux_left (J : Ideal A) (n m : ℕ) :
    Submodule.comap (J ^ n).subtype (J ^ (n + 1)) ≤
      (associatedGradedMulAux J n m).ker := by
  intro a ha
  apply LinearMap.mem_ker.mpr
  ext b
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change a.1 * b.1 ∈ J ^ (n + m + 1)
  change a.1 ∈ J ^ (n + 1) at ha
  have hab := Ideal.mul_mem_mul ha b.2
  simpa [← pow_add, Nat.add_right_comm] using hab

/-- The product of a representative in `J^n` with one in `J^(m+1)` lies in `J^(n+m+1)`, so its class
vanishes. -/
theorem associatedGradedMulAux_right (J : Ideal A) (n m : ℕ) :
    Submodule.comap (J ^ m).subtype (J ^ (m + 1)) ≤
      (associatedGradedMulAux J n m).flip.ker := by
  intro b hb
  apply LinearMap.mem_ker.mpr
  ext a
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change a.1 * b.1 ∈ J ^ (n + m + 1)
  change b.1 ∈ J ^ (m + 1) at hb
  have hab := Ideal.mul_mem_mul a.2 hb
  simpa [← pow_add, Nat.add_assoc] using hab

/-- The biadditive map `μ_{n,m} : J^n/J^(n+1) × J^m/J^(m+1) → J^(n+m)/J^(n+m+1)`,
`(a mod J^(n+1), b mod J^(m+1)) ↦ ab mod J^(n+m+1)`. -/
def associatedGradedMul (J : Ideal A) (n m : ℕ) :
    associatedGradedPiece J n →ₗ[A] associatedGradedPiece J m →ₗ[A]
      associatedGradedPiece J (n + m) :=
  (associatedGradedMulAux J n m).liftQ₂ _ _
    (associatedGradedMulAux_left J n m) (associatedGradedMulAux_right J n m)

/-- The graded multiplication `μ_{n,m}` of `gr_J(A)`. -/
instance associatedGradedGMul (J : Ideal A) :
    GradedMonoid.GMul (associatedGradedPiece J) where
  mul a b := associatedGradedMul J _ _ a b

/-- The unit `1 mod J` in degree zero. -/
instance associatedGradedGOne (J : Ideal A) :
    GradedMonoid.GOne (associatedGradedPiece J) where
  one := Submodule.Quotient.mk (⟨1, by simp⟩ : (J ^ 0 : Ideal A))

private theorem associatedGraded_mk_eq (J : Ideal A) (n m : ℕ) (h : n = m)
    (a : (J ^ n : Ideal A)) (b : (J ^ m : Ideal A)) (hab : a.1 = b.1) :
    GradedMonoid.mk (A := associatedGradedPiece J) n (Submodule.Quotient.mk a) =
      GradedMonoid.mk (A := associatedGradedPiece J) m (Submodule.Quotient.mk b) := by
  subst m
  have : a = b := Subtype.ext hab
  subst b
  rfl

/-- The unit is a left unit. -/
theorem associatedGraded_gone_mul (J : Ideal A)
    (a : GradedMonoid (associatedGradedPiece J)) : 1 * a = a := by
  obtain ⟨n, a⟩ := a
  induction a using Submodule.Quotient.induction_on with
  | _ a =>
    apply associatedGraded_mk_eq J (0 + n) n (Nat.zero_add n)
    simp

/-- The unit is a right unit. -/
theorem associatedGraded_mul_gone (J : Ideal A)
    (a : GradedMonoid (associatedGradedPiece J)) : a * 1 = a := by
  obtain ⟨n, a⟩ := a
  induction a using Submodule.Quotient.induction_on with
  | _ a =>
    apply associatedGraded_mk_eq J (n + 0) n (Nat.add_zero n)
    simp

/-- The graded multiplication is associative. -/
theorem associatedGraded_gmul_assoc (J : Ideal A)
    (a b c : GradedMonoid (associatedGradedPiece J)) :
    a * b * c = a * (b * c) := by
  obtain ⟨n, a⟩ := a
  obtain ⟨m, b⟩ := b
  obtain ⟨k, c⟩ := c
  induction a using Submodule.Quotient.induction_on with
  | _ a =>
    induction b using Submodule.Quotient.induction_on with
    | _ b =>
      induction c using Submodule.Quotient.induction_on with
      | _ c =>
        apply associatedGraded_mk_eq J (n + m + k) (n + (m + k))
          (Nat.add_assoc n m k)
        exact mul_assoc a.1 b.1 c.1

/-- The graded multiplication is commutative. -/
theorem associatedGraded_gmul_comm (J : Ideal A)
    (a b : GradedMonoid (associatedGradedPiece J)) : a * b = b * a := by
  obtain ⟨n, a⟩ := a
  obtain ⟨m, b⟩ := b
  induction a using Submodule.Quotient.induction_on with
  | _ a =>
    induction b using Submodule.Quotient.induction_on with
    | _ b =>
      apply associatedGraded_mk_eq J (n + m) (m + n) (Nat.add_comm n m)
      exact mul_comm a.1 b.1

/-- The graded commutative ring structure on the pieces `J^n/J^(n+1)`, with the integers mapped to
the classes of their images in `A` in degree zero. -/
instance associatedGradedGCommRing (J : Ideal A) :
    DirectSum.GCommRing (associatedGradedPiece J) where
  mul_zero a := map_zero (associatedGradedMul J _ _ a)
  zero_mul b := LinearMap.map_zero₂ (associatedGradedMul J _ _) b
  mul_add a b c := map_add (associatedGradedMul J _ _ a) b c
  add_mul a b c := LinearMap.map_add₂ (associatedGradedMul J _ _) a b c
  one_mul := associatedGraded_gone_mul J
  mul_one := associatedGraded_mul_gone J
  mul_assoc := associatedGraded_gmul_assoc J
  mul_comm := associatedGraded_gmul_comm J
  natCast k := Submodule.Quotient.mk (⟨(k : A), by simp⟩ : (J ^ 0 : Ideal A))
  natCast_zero := by
    rw [← Submodule.Quotient.mk_zero]; congr 1; ext; simp
  natCast_succ k := by
    change _ = _ + Submodule.Quotient.mk _
    rw [← Submodule.Quotient.mk_add]; congr 1; ext; simp
  intCast k := Submodule.Quotient.mk (⟨(k : A), by simp⟩ : (J ^ 0 : Ideal A))
  intCast_ofNat k := by congr 1; ext; simp
  intCast_negSucc_ofNat k := by
    rw [← Submodule.Quotient.mk_neg]; congr 1; ext; simp

/-- The commutative ring `gr_J(A)`: the direct sum with the multiplication induced by that
of `A`. -/
noncomputable instance associatedGradedCommRing (J : Ideal A) :
    CommRing (associatedGraded J) :=
  DirectSum.commRing _

/-- The unit is the degree-zero class of one. -/
theorem associatedGraded_one (J : Ideal A) :
    (1 : associatedGraded J) =
      DirectSum.of (fun n : ℕ => associatedGradedPiece J n) 0
        (Submodule.Quotient.mk (⟨1, by simp⟩ : (J ^ 0 : Ideal A))) := by
  rfl

/-- Products of homogeneous classes are classes of products. -/
theorem associatedGraded_mul (J : Ideal A) (n m : ℕ)
    (a : (J ^ n : Ideal A)) (b : (J ^ m : Ideal A)) :
    DirectSum.of (fun k : ℕ => associatedGradedPiece J k) n
      (Submodule.Quotient.mk a) *
    DirectSum.of (fun k : ℕ => associatedGradedPiece J k) m
      (Submodule.Quotient.mk b) =
    DirectSum.of (fun k : ℕ => associatedGradedPiece J k) (n + m)
      (Submodule.Quotient.mk
        (⟨a.1 * b.1, by
          simpa [pow_add] using Ideal.mul_mem_mul a.2 b.2⟩ :
          (J ^ (n + m) : Ideal A))) := by
  rw [DirectSum.of_mul_of]
  rfl

/-- The degree-zero inclusion `a ↦ ι_0(a mod J)` is multiplicative. -/
theorem associatedGraded_of_zero_mul (J : Ideal A) (a b : A) :
    DirectSum.of (fun k : ℕ => associatedGradedPiece J k) 0
        (Submodule.Quotient.mk (⟨a * b, by simp⟩ : (J ^ 0 : Ideal A))) =
      DirectSum.of (fun k : ℕ => associatedGradedPiece J k) 0
          (Submodule.Quotient.mk (⟨a, by simp⟩ : (J ^ 0 : Ideal A))) *
        DirectSum.of (fun k : ℕ => associatedGradedPiece J k) 0
          (Submodule.Quotient.mk (⟨b, by simp⟩ : (J ^ 0 : Ideal A))) := by
  rw [DirectSum.of_mul_of]
  congr 1

/-- The ring homomorphism `A → gr_J(A)`, `a ↦ ι_0(a mod J)`. -/
noncomputable def associatedGradedRingHom (J : Ideal A) :
    A →+* associatedGraded J where
  toFun a := DirectSum.of (fun k : ℕ => associatedGradedPiece J k) 0
    (Submodule.Quotient.mk (⟨a, by simp⟩ : (J ^ 0 : Ideal A)))
  map_one' := rfl
  map_mul' := associatedGraded_of_zero_mul J
  map_zero' := by
    rw [← map_zero (DirectSum.of (fun k : ℕ => associatedGradedPiece J k) 0),
      ← Submodule.Quotient.mk_zero]
    rfl
  map_add' a b := by
    rw [← map_add, ← Submodule.Quotient.mk_add]
    rfl

/-- The map `A → gr_J(A)` vanishes on `J`. -/
theorem associatedGradedRingHom_ker (J : Ideal A) :
    ∀ a ∈ J, associatedGradedRingHom J a = 0 := by
  intro a ha
  rw [show associatedGradedRingHom J a =
      DirectSum.of (fun k : ℕ => associatedGradedPiece J k) 0
        (Submodule.Quotient.mk (⟨a, by simp⟩ : (J ^ 0 : Ideal A))) by rfl]
  rw [← map_zero (DirectSum.of (fun k : ℕ => associatedGradedPiece J k) 0)]
  congr 1
  apply (Submodule.Quotient.mk_eq_zero _).2
  simpa [pow_succ, pow_zero] using ha

/-- The `A/J`-algebra structure through the degree-zero inclusion `ι_0 : A/J → gr_J(A)`. -/
noncomputable instance associatedGradedAlgebra (J : Ideal A) :
    Algebra (A ⧸ J) (associatedGraded J) :=
  (Ideal.Quotient.lift J (associatedGradedRingHom J)
    (associatedGradedRingHom_ker J)).toAlgebra

/-- The degree-zero inclusion `ι_0 : A/J → gr_J(A)` is injective. -/
theorem algebraMap_associatedGraded_injective (J : Ideal A) :
    Function.Injective (algebraMap (A ⧸ J) (associatedGraded J)) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [RingHom.algebraMap_toAlgebra, Ideal.Quotient.lift_mk,
    show associatedGradedRingHom J a =
      DirectSum.of (fun k : ℕ => associatedGradedPiece J k) 0
        (Submodule.Quotient.mk (⟨a, by simp⟩ : (J ^ 0 : Ideal A))) by rfl,
    ← map_zero (DirectSum.of (fun k : ℕ => associatedGradedPiece J k) 0)] at hx
  have h : a ∈ J ^ (0 + 1) :=
    (Submodule.Quotient.mk_eq_zero (p := Submodule.comap (J ^ 0 : Ideal A).subtype
      (J ^ (0 + 1)))).1 (DirectSum.of_injective 0 hx)
  rw [zero_add, pow_one] at h
  exact Ideal.Quotient.eq_zero_iff_mem.2 h

/-- The action of `A/J` on a homogeneous class is multiplication by a representative in `A`. -/
theorem associatedGraded_smul (J : Ideal A) (a : A) (n : ℕ)
    (x : (J ^ n : Ideal A)) :
    (Ideal.Quotient.mk J a) •
      DirectSum.of (fun k : ℕ => associatedGradedPiece J k) n
        (Submodule.Quotient.mk x) =
    DirectSum.of (fun k : ℕ => associatedGradedPiece J k) n
      (Submodule.Quotient.mk
        (⟨a * x.1, (J ^ n).mul_mem_left a x.2⟩ : (J ^ n : Ideal A))) := by
  rw [Algebra.smul_def]
  change associatedGradedRingHom J a * _ = _
  change DirectSum.of (fun k : ℕ => associatedGradedPiece J k) 0
    (Submodule.Quotient.mk (⟨a, by simp⟩ : (J ^ 0 : Ideal A))) * _ = _
  rw [associatedGraded_mul]
  exact congrArg (fun y : GradedMonoid (associatedGradedPiece J) =>
    DirectSum.of (fun k : ℕ => associatedGradedPiece J k) y.1 y.2)
    (associatedGraded_mk_eq J (0 + n) n (Nat.zero_add n) _ _ rfl)

/-- An ideal of the associated graded ring is homogeneous when it contains every homogeneous
component of each of its elements. -/
def IsHomogeneousAssociatedGraded (J : Ideal A)
    (b : Ideal (associatedGraded J)) : Prop :=
  ∀ (x : associatedGraded J) (n : ℕ), x ∈ b →
    DirectSum.of (fun k : ℕ => associatedGradedPiece J k) n (x n) ∈ b

end Ideal
