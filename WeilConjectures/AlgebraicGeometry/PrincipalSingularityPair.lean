/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.IsRegularScheme

/-! # Principal singularity pairs

Source: Temkin, Non-embedded Desingularization, §3.2 and proof of Proposition 3.3.5,
printed p.25; finite disjoint unions as in §2.1.14
(blueprint: def-per-principal-singularity-pair).
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An affine scheme with a principal non-zero-divisor ideal containing its singular locus.
Regularity of the complement uses the locally Noetherian notion of regular scheme.
Source: Temkin §3.2, Proposition 3.3.5 (blueprint: def-per-principal-singularity-pair). -/
def IsPrincipalSingularityPair (X : Scheme.{u}) (I : X.IdealSheafData) : Prop :=
  IsAffine X ∧
    (∃ π : Γ(X, ⊤), π ∈ nonZeroDivisors Γ(X, ⊤) ∧
      I = Scheme.IdealSheafData.ofIdealTop (Ideal.span {π})) ∧
    IsRegularScheme (Scheme.Opens.toScheme I.support.compl)

/-- A principal singularity pair of finite type over some characteristic-zero field.
The field and structure morphism are existential, so no field compatibility is imposed
on subsequent morphisms of pairs. Source: Temkin Proposition 3.3.5
(blueprint: def-per-principal-singularity-pair). -/
def IsCharZeroVarietySingularityPair (X : Scheme.{u}) (I : X.IdealSheafData) : Prop :=
  IsPrincipalSingularityPair X I ∧
    ∃ (K : CommRingCat.{u}) (s : X ⟶ Spec K),
      IsField K ∧ CharZero K ∧ LocallyOfFiniteType s ∧ QuasiCompact s

/-- A finite disjoint union of principal singularity pairs over characteristic-zero
fields, which may differ among components. The empty union is included. The ideal is
identified on each component by extension, using the existing ideal-sheaf pullback.
Source: Temkin §2.1.14 and Proposition 3.3.5
(blueprint: def-per-principal-singularity-pair). -/
def IsFiniteCharZeroSingularityPair (X : Scheme.{u}) (I : X.IdealSheafData) : Prop :=
  ∃ (n : ℕ) (V : Fin n → Scheme.{u}) (J : ∀ i, (V i).IdealSheafData) (e : X ≅ ∐ V),
    ∀ i, IsCharZeroVarietySingularityPair (V i) (J i) ∧
      I.comap (Sigma.ι V i ≫ e.inv) = J i

end AlgebraicGeometry
