/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Unique finite étale morphism lifts to quotient-power thickenings

Source: Stacks Project, Tags 0EL8 and 0BQB.
(blueprint: lem-sbc-finite-etale-adic-unique-lift)
-/

@[expose] public section

noncomputable section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.FiniteEtale.Adic

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The powers defining the infinitesimal neighbourhoods of a quotient section. -/
abbrev ideal (f : R →+* S) (n : ℕ) : Ideal R := (RingHom.ker f) ^ (n + 1)

/-- The `(n+1)`st quotient-power thickening. -/
def base (f : R →+* S) (n : ℕ) : Scheme.{u} := Spec (.of (R ⧸ ideal f n))

/-- The closed immersion of the quotient-power thickening into the ambient spectrum. -/
def baseMap (f : R →+* S) (n : ℕ) : base f n ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (ideal f n)))

/-- The quotient section factors through every infinitesimal neighbourhood. -/
def baseZero (f : R →+* S) (n : ℕ) : Spec (.of S) ⟶ base f n :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift (ideal f n) f
    (fun _a ha ↦ (Ideal.pow_le_self (Nat.succ_ne_zero n)) ha)))

@[simp]
theorem baseZero_comp_baseMap (f : R →+* S) (n : ℕ) :
    baseZero f n ≫ baseMap f n = Spec.map (CommRingCat.ofHom f) := by
  rw [baseZero, baseMap, ← Spec.map_comp]
  rfl

/-- Transition from one infinitesimal neighbourhood to the next. -/
def baseTransition (f : R →+* S) (n : ℕ) : base f n ⟶ base f (n + 1) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))))

@[simp]
theorem baseTransition_comp_baseMap (f : R →+* S) (n : ℕ) :
    baseTransition f n ≫ baseMap f (n + 1) = baseMap f n := by
  rw [baseTransition, baseMap, ← Spec.map_comp]
  rfl

@[simp]
theorem baseZero_comp_baseTransition (f : R →+* S) (n : ℕ) :
    baseZero f n ≫ baseTransition f n = baseZero f (n + 1) := by
  rw [baseZero, baseTransition, baseZero, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

variable (f : R →+* S) (V : (Spec (.of R)).Opens) (P : V.toScheme.FiniteEtale)

/-- Infinitesimal neighbourhoods of the section in the total space of a cover. -/
def cover (n : ℕ) : Scheme.{u} := Limits.pullback (P.obj.hom ≫ V.ι) (baseMap f n)

/-- Projection of an infinitesimal neighbourhood to the total space of the cover. -/
def coverMap (n : ℕ) : cover f V P n ⟶ P.obj.left :=
  pullback.fst (P.obj.hom ≫ V.ι) (baseMap f n)

/-- The cover restricted to the quotient section. -/
def zeroCover : Scheme.{u} :=
  Limits.pullback P.obj.hom ((Spec.map (CommRingCat.ofHom f)) ∣_ V)

/-- Inclusion of the restricted cover in its infinitesimal neighbourhood. -/
noncomputable def zeroMap (n : ℕ) : zeroCover f V P ⟶ cover f V P n :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ ((Spec.map (CommRingCat.ofHom f)) ⁻¹ᵁ V).ι ≫ baseZero f n)
    (by
      simp only [Category.assoc, baseZero_comp_baseMap]
      rw [← morphismRestrict_ι, ← Category.assoc, pullback.condition]
      exact Category.assoc _ _ _)

@[simp]
theorem zeroMap_coverMap (n : ℕ) :
    zeroMap f V P n ≫ coverMap f V P n = pullback.fst _ _ := by
  simp [zeroMap, coverMap]

/-- Inclusion of successive infinitesimal neighbourhoods of a cover. -/
noncomputable def coverTransition (n : ℕ) : cover f V P n ⟶ cover f V P (n + 1) :=
  pullback.lift (coverMap f V P n) (pullback.snd _ _ ≫ baseTransition f n)
    (by rw [Category.assoc, baseTransition_comp_baseMap]; exact pullback.condition)

@[simp]
theorem coverTransition_coverMap (n : ℕ) :
    coverTransition f V P n ≫ coverMap f V P (n + 1) = coverMap f V P n := by
  simp [coverTransition, coverMap]

@[simp]
theorem zeroMap_coverTransition (n : ℕ) :
    zeroMap f V P n ≫ coverTransition f V P n = zeroMap f V P (n + 1) := by
  apply pullback.hom_ext
  · simp [zeroMap, coverTransition, coverMap, Category.assoc]
  · simp [zeroMap, coverTransition, Category.assoc]

end AlgebraicGeometry.Scheme.FiniteEtale.Adic

namespace AlgebraicGeometry.Scheme

/-- A map of finite étale covers on a quotient section lifts uniquely to each
quotient-power thickening.

Source: Stacks Project, Tag 0BQB (invariance under a thickening), as used in
Tag 0EL8. (blueprint: lem-sbc-finite-etale-adic-unique-lift)

Proof: Put I = ker(f). Surjectivity identifies S with R/I. The immersion
Spec(S) into Spec(R/I^(n+1)) has nilpotent ideal I/I^(n+1), whose (n+1)st
power is zero. Restrict to V and base change by P. This is still a nilpotent
closed immersion, from the restricted cover into Adic.cover f V P n.
The structure morphism of Q is étale. On affine opens, its formal étaleness
lifts the given algebra homomorphism uniquely through the nilpotent quotient;
for general nilpotent ideals one iterates square-zero lifting. Uniqueness
makes these affine lifts agree on overlaps, so they glue to a unique map
from Adic.cover f V P n to Q over V. The equality after Adic.zeroMap is
precisely that its restriction is the given morphism. Empty covers and
nonconstant ranks cause no change to this local argument. -/
theorem finiteEtale_adic_unique_lift
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (V : (Spec (.of R)).Opens)
    (P Q : V.toScheme.FiniteEtale)
    (φ : (FiniteEtale.pullback ((Spec.map (CommRingCat.ofHom f)) ∣_ V)).obj P ⟶
      (FiniteEtale.pullback ((Spec.map (CommRingCat.ofHom f)) ∣_ V)).obj Q)
    (n : ℕ) :
    ∃! g : FiniteEtale.Adic.cover f V P n ⟶ Q.obj.left,
      g ≫ Q.obj.hom = FiniteEtale.Adic.coverMap f V P n ≫ P.obj.hom ∧
      FiniteEtale.Adic.zeroMap f V P n ≫ g =
        φ.hom.left ≫ pullback.fst Q.obj.hom
          ((Spec.map (CommRingCat.ofHom f)) ∣_ V) := by sorry

end AlgebraicGeometry.Scheme
