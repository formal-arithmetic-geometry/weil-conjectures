/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A7
-/
module

public import Sheaf.AlgebraicGeometry.OrdinarySupportedKummerSystem
import Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer

/-!
# Ordinary Chern realization of a normalized supported Kummer class

Source: Stacks 03PL and 0A45; blueprint lem-asd-ordinary-supported-kummer.
(blueprint: lem-asd-ordinary-supported-chern-normalization).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Forgetting support in the uniquely normalized class gives the ordinary divisor Chern class.
Source: Stacks 03PL and 0A45; the unit and scalar-Chern clauses of
`ordinary_supported_kummer` (blueprint: lem-asd-ordinary-supported-chern-normalization).

Proof: take the supported class, its exact derived realization, and ordinary Chern
representative from `ordinary_supported_kummer`. Its uniqueness clause identifies
its supported representative with κ. Substitute the realization equation and the
unit equation. In the definition of `ordinaryFiniteClass`, the inverse Ext/Hom
comparison cancels the realization of the ordinary representative. The remaining
equality is precisely the scalar-Chern clause of the supported theorem. -/
theorem ordinary_supported_kummer_chern (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) {D : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (κ : Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
      (Scheme.finiteEtaleTateLine T N A hA) 2)
    (hκ : SupportedKummerBoundary A N hA i hI hT κ) :
    ordinaryFiniteClass A T (Scheme.finiteEtaleTateLine T N A hA) 2
      (supportedDerivedUnit A i ≫ supportedExactDerivedMap
        (lowerStar (ModuleCat.{u + 1} A) i) (ordinaryFiniteConstant A D)
        (Scheme.finiteEtaleTateLine T N A hA) κ) =
      supportedKummerChern A N hA i hI hT := by
  obtain ⟨κ₀, δ, c, t, hδ, hb, hu, hc, hunit, hbc, hscalar⟩ :=
    ordinary_supported_kummer T N hN A hA hT i hI
  have heq : κ = κ₀ := hu κ hκ
  subst κ₀
  rw [← hδ, hunit]
  unfold ordinaryFiniteClass
  simpa only [Ext.hom, Equiv.symm_apply_apply] using hc

end AlgebraicGeometry.Etale
