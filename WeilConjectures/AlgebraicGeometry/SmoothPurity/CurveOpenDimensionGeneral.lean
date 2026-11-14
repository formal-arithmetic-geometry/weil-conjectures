/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CurveOpenDirectImage

/-!
# Open direct-image dimension on arbitrary curves
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Higher direct images across an arbitrary open immersion into a finite-type scheme of
 dimension at most one over a finite field or its algebraic closure vanish above degree one
 for every module sheaf over a finite prime-power-torsion coefficient ring. -/
theorem isZero_higherDirectImage_of_open_curve
    (k : Type u) [Field k]
    (hk : Finite k ∨ ∃ k₀ : Subfield k, Finite k₀ ∧ IsAlgClosure k₀ k)
    {T U : Scheme.{u}} [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    (hdim : topologicalKrullDim T ≤ 1) (j : U ⟶ T) [IsOpenImmersion j]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (ℓ : ℕ) (hprime : ℓ.Prime) (hinv : IsUnit (ℓ : Γ(T, ⊤)))
    (hkill : ∃ n : ℕ, (ℓ ^ n : ℕ) • (1 : A) = 0)
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
    (q : ℤ) (hq : 1 < q) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) j).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M))) := by
  have _ := hk
  have _ := hprime
  have _ := hinv
  have _ := hkill
  have h := isZero_higherDirectImage_of_isOpenImmersion
    (Λ := A) (aT := (T ↘ Spec (.of k))) isAddTorsion_of_finite hdim j M q.toNat (by omega)
  have hq' : q = (q.toNat : ℤ) := by omega
  rw [hq']
  exact h

end AlgebraicGeometry.Etale
