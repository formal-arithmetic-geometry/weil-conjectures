/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
import WeilConjectures.AlgebraicGeometry.Curve.ConstructiblePrimeFieldFiltration
import WeilConjectures.AlgebraicGeometry.Curve.UnderlyingAbelianAssertions
import WeilConjectures.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions

/-! # Prime devissage for constructible module sheaves

Source: Stacks Project, Theorem 59.83.10 (03SC), second paragraph of the proof.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- On a fixed reduced curve, the eight assertions for constructible prime-field sheaves
imply the assertions for constructible sheaves over any finite coefficient ring.
Source: Stacks Project, Theorem 59.83.10 (03SC), second proof paragraph. -/
theorem IsCurve.assertions_of_constructible_prime_devissage
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f] [IsReduced C]
    (H : ∀ (r : ℕ) [Fact r.Prime]
      (G : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))))
      [Scheme.IsConstructibleSheaf G], IsCurve.Assertions (ULift.{u + 1} (ZMod r)) f G)
    (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsConstructibleSheaf F] : IsCurve.Assertions Λ f F := by
  have hfil := Scheme.constructible_hasPrimeFieldFiltration Λ C F
  induction hfil with
  | prime r F G e =>
    exact IsCurve.assertions_of_underlying_abelian_iso f e (H r G)
  | extension S hS h₁ h₃ ih₁ ih₃ =>
    exact IsCurve.Assertions.of_constructible_shortExact Λ f hS ih₁ ih₃

end AlgebraicGeometry
