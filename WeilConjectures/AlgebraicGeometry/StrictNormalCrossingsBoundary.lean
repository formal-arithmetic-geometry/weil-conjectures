/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Strict normal crossings boundaries

Source: ILO, Travaux de Gabber, Expose VIII, 4.1.2, Remark 4.2.2(i), and Lemma 4.2.9,
printed pp. 117--121 (blueprint: def-trf-strict-normal-crossings-boundary).
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
/-- A strict normal-crossings boundary is reduced with finitely many regular components,
whose scheme-theoretic intersections are regular of the expected codimension.
Source: ILO, Exposé VIII, Remark 4.2.2(i) (blueprint: def-trf-strict-normal-crossings-boundary). -/
def IsStrictNormalCrossingsBoundary {X : Scheme.{u}}
    (H : X.IdealSheafData) : Prop :=
  H.IsInvertible ∧ H.radical = H ∧
    ∃ (n : ℕ) (C : Fin n → X.IdealSheafData),
      Function.Injective (fun i ↦ (C i).support) ∧
      (∀ i, IsIntegral (C i).subscheme ∧ IsRegularScheme (C i).subscheme) ∧
      H.support = ⨆ i, (C i).support ∧
      ∀ s : Finset (Fin n),
        ∀ z : (⨆ i ∈ s, C i).subscheme,
          IsRegularScheme ((⨆ i ∈ s, C i).subscheme) ∧
          ringKrullDim (X.presheaf.stalk ((⨆ i ∈ s, C i).subschemeι z)) =
            ringKrullDim ((⨆ i ∈ s, C i).subscheme.presheaf.stalk z) + (s.card : ℕ)

end AlgebraicGeometry
