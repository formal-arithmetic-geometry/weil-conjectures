/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseAbelian
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseRank
public import WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedFieldExact

/-!
# A rank criterion for lisse cohomology sheaves

TODO
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {T : Scheme.{u}} {Ω : Type u} [Field Ω]

namespace AdicSheaf

variable (l) in
/-- The fibre functor `M ↦ Γ(Spec Ω, s^* M)` at a point `s : Spec Ω ⟶ T`, with values in
`ℚ̄_ℓ`-vector spaces. -/
noncomputable def fibre (s : Spec (.of Ω) ⟶ T) :
    AdicSheaf l T ⥤ ModuleCat.{u + 1} (PadicAlgCl l) :=
  (s)^*ᵃ[l] ⋙ AdicSheaf.forget _ ⋙ Sheaf.Γ _ _ ⋙ WeilCoefficients.toModuleCat l

instance (s : Spec (.of Ω) ⟶ T) : (fibre l s).Additive := by
  have : (Sheaf.Γ (Scheme.ProEt.topology (Spec (.of Ω))) (WeilCoefficients.{u} l)).Additive :=
    Functor.additive_of_preserves_binary_products _
  unfold fibre
  infer_instance

instance (s : Spec (.of Ω) ⟶ T) : PreservesFiniteLimits (fibre l s) := by
  unfold fibre
  infer_instance

instance [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ T) : (fibre l s).PreservesEpimorphisms := by
  unfold fibre
  infer_instance

end AdicSheaf

end AlgebraicGeometry.ProEtale
