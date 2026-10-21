/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.TameRootTowerExtension
public import Sheaf.Paper.PartialKummerBoundaryUnitModel

/-! # Indexing the actual reduced strata and prime-to-ell inertia
Source: direct-image proof (3), stratum and inertia formulas.
(blueprint: def-sfb-kummer-stratum-geometry).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.ProEtale

/-- The given finite component family, lifted only to the scheme universe.
Source: direct-image proof (3), D = union D_a
(blueprint: def-sfb-kummer-stratum-geometry). -/
def kummerComponents {Y : Scheme.{u}} (D : Y.IdealSheafData)
    (hD : IsStrictNormalCrossingsBoundary D) :
    ULift.{u} (Fin hD.2.2.choose) → Y.IdealSheafData :=
  fun i ↦ hD.2.2.choose_spec.choose i.down

/-- Lift the chosen subset without changing its elements or its cardinality.
Source: direct-image proof (3), subset I
(blueprint: def-sfb-kummer-stratum-geometry). -/
def kummerIndices {Y : Scheme.{u}} (D : Y.IdealSheafData)
    (hD : IsStrictNormalCrossingsBoundary D) (I : Finset (Fin hD.2.2.choose)) :
    Finset (ULift.{u} (Fin hD.2.2.choose)) :=
  I.map ⟨ULift.up, ULift.up_injective⟩

/-- The prime-to-ell subgroup of the given full parameter-root deck group.
Source: direct-image proof (3), H_I
(blueprint: def-sfb-kummer-stratum-geometry). -/
abbrev KummerPrimeToEll (p ℓ : ℕ) (J : Type u) :=
  Multiplicative (J → (q : {q : ℕ // q.Prime ∧ q ≠ p ∧ q ≠ ℓ}) →
    @PadicInt q.val ⟨q.property.1⟩)

/-- Insert zero into the omitted ell-adic coordinates.
Source: direct-image proof (3), H_I subgroup G_I
(blueprint: def-sfb-kummer-stratum-geometry). -/
def kummerPrimeToEllInclusion (p ℓ : ℕ) (J : Type u) :
    KummerPrimeToEll p ℓ J →* ParameterRootDeckGroup p J where
  toFun g := Multiplicative.ofAdd (fun i q ↦
    if h : q.val ≠ ℓ then g.toAdd i ⟨q.val, q.property.1, q.property.2, h⟩ else 0)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext i q
    change (if h : q.val ≠ ℓ then 0 else 0) = 0
    split_ifs <;> rfl
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    funext i q
    change (if hq : q.val ≠ ℓ then
      g.toAdd i ⟨q.val, q.property.1, q.property.2, hq⟩ +
      h.toAdd i ⟨q.val, q.property.1, q.property.2, hq⟩ else (0 : @PadicInt q.val ⟨q.property.1⟩)) =
      (if hq : q.val ≠ ℓ then g.toAdd i ⟨q.val, q.property.1, q.property.2, hq⟩ else 0) +
      (if hq : q.val ≠ ℓ then h.toAdd i ⟨q.val, q.property.1, q.property.2, hq⟩ else 0)
    split_ifs <;> simp

/-- Finite image of order prime to ell, with no faithfulness requirement.
Source: direct-image proof (3), finite prime-to-ell image
(blueprint: def-sfb-kummer-stratum-geometry). -/
def KummerFinitePrimeToEllImage (p ℓ : ℕ) (J : Type u)
    (E : Type) [NormedField E]
    (M : PartialKummer.FiniteRepresentation E (ParameterRootDeckGroup p J)) : Prop :=
  (Set.range (M.representation.obj.ρ.comp (kummerPrimeToEllInclusion p ℓ J))).Finite ∧
    (Nat.card (Set.range
      (M.representation.obj.ρ.comp (kummerPrimeToEllInclusion p ℓ J)))).Coprime ℓ

end AlgebraicGeometry.ProEtale
