/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.IntegralCompactificationRealizationData

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Vertical proper/open transport pasting. This is the corresponding
field of the transported
pasting package, isolated so that its transport proof can be supplied independently.
Source: Stacks 0F7C, 0F7D and 0F7F; Zheng Lemma 4.10.
(blueprint: lem-sf-integral-system-proper-open-transport-pasting-vertical).
Proof: transport the intrinsic equation through the canonical bridge; naturality and
inverse cancellation identify the resulting composite. -/
theorem integralSystemProperOpenTransportPastingVertical
    (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c)
    (gamma : ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
      (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
      [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
      (_h : k ≫ p = r ≫ i),
      Operations.push l E o r ⋙ Operations.shriek l E o i ⟶
        Operations.shriek l E o k ⋙ Operations.push l E o p) :
  ∀ {A C E₀ B₀ D F : Scheme.{u}}
      (k : A ⟶ B₀) (i : C ⟶ D) (j : E₀ ⟶ F)
      (r₁ : A ⟶ C) (r₂ : C ⟶ E₀) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
      [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
      (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
      (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (M : System l E A),
      (Operations.shriek l E o j).map ((c.pushComp l E r₁ r₂).hom.app M) ≫
          (gamma k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app M ≫
          (c.pushComp l E p₁ p₂).inv.app ((Operations.shriek l E o k).obj M) =
        (gamma i r₂ p₂ j h₂).app ((Operations.push l E o r₁).obj M) ≫
          (Operations.push l E o p₂).map ((gamma k r₁ p₁ i h₁).app M) := by
  sorry

end WeilConjectures.IntegralSystemRealization
