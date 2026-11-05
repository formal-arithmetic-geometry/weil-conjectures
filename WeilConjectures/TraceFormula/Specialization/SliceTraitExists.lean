/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.SliceTrait
public import WeilConjectures.TraceFormula.Specialization.SliceTraitPoint
public import WeilConjectures.AlgebraicGeometry.Sites.StrictLocalizationUniversal
public import WeilConjectures.TraceFormula.Specialization.SliceTraitResidue

/-!

# The strict localization of `𝔸¹_{S₁}` is a slice trait

Let `S₁ = Spec R₁` be a strictly henselian trait with a geometric generic point `a₁ : R₁ ⟶ Ω₁`
(`Ω₁` algebraic over `R₁`) and a point `b₁ : R₁ ⟶ κ₁` with kernel the maximal ideal. The strict
henselization `R` of `𝔸¹_{S₁}` at the geometric point `Spec κ₁(x)^alg ⟶ 𝔸¹_{S₁}` over the generic
point of its special fibre (`AlgebraicGeometry.sliceTraitPoint`) is a slice trait over `S₁`
(`AlgebraicGeometry.sliceTraitOfStrictLocalization`, `AlgebraicGeometry.nonempty_sliceTrait`), with
geometric generic point `R ⟶ Ω' = (Frac R)^alg` and closed point `R ⟶ κ₁(x)^alg`
(SGA 4½, [Th. finitude], 3.3). The embedding `Ω₁ ⟶ Ω'` extends `Frac R₁ ⟶ Frac R`.

-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing

section AlgebraicClosure

variable (R : Type u) [CommRing R] [IsDomain R]

end AlgebraicClosure

namespace AlgebraicGeometry

open Scheme

variable {R₁ : Type u} [CommRing R₁] [IsDomain R₁] [IsDiscreteValuationRing R₁]
  {Ω₁ : Type u} [Field Ω₁] (a₁ : R₁ →+* Ω₁)
  (ha₁ : Function.Injective a₁) (halg : letI := a₁.toAlgebra; Algebra.IsAlgebraic R₁ Ω₁)
  {κ₁ : Type u} [Field κ₁] (b₁ : R₁ →+* κ₁) (hb₁ : RingHom.ker b₁ = maximalIdeal R₁)

variable [IsStrictlyHenselianLocalRing R₁]

section Simp

variable {a₁ b₁}

end Simp

end AlgebraicGeometry
