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

/-- Base-change proper/open transport pasting. This is the corresponding
field of the transported
pasting package, isolated so that its transport proof can be supplied independently.
Source: Stacks 0F7C, 0F7D and 0F7F; Zheng Lemma 4.10.
(blueprint: lem-sf-integral-system-proper-open-transport-pasting-basechange).
Proof: transport the intrinsic equation through the canonical bridge; naturality and
inverse cancellation identify the resulting composite. -/
theorem integralSystemProperOpenTransportPastingBaseChange
    (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c)
    (gamma : ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
      (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
      [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
      (_h : k ≫ p = r ≫ i),
      Operations.push l E o r ⋙ Operations.shriek l E o i ⟶
        Operations.shriek l E o k ⋙ Operations.push l E o p) :
  ∀ {V W S T V₁ W₁ S₁ T₁ : Scheme.{u}}
      (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
      (k₁ : V₁ ⟶ W₁) (i₁ : S₁ ⟶ T₁) (r₁ : V₁ ⟶ S₁) (p₁ : W₁ ⟶ T₁)
      (aa : W₁ ⟶ W) (bb : T₁ ⟶ T) (cc : S₁ ⟶ S) (d : V₁ ⟶ V)
      [IsOpenImmersion k] [IsOpenImmersion i]
      [IsOpenImmersion k₁] [IsOpenImmersion i₁]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
      [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
      (h : k ≫ p = r ≫ i) (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
      (wk : d ≫ k = k₁ ≫ aa) (wi : cc ≫ i = i₁ ≫ bb)
      (wp : aa ≫ p = p₁ ≫ bb) (wr : d ≫ r = r₁ ≫ cc)
      (sk : IsPullback d k₁ k aa) (si : IsPullback cc i₁ i bb)
      (_sp : IsPullback aa p₁ p bb) (_sr : IsPullback d r₁ r cc) (M : System l E V),
      (pull l E bb).map ((gamma k r p i h).app M) ≫
          (properExchange l E o c aa p₁ p bb wp).app ((Operations.shriek l E o k).obj M) ≫
          (Operations.push l E o p₁).map ((a.beta d k₁ k aa wk sk).hom.app M) =
        (a.beta cc i₁ i bb wi si).hom.app ((Operations.push l E o r).obj M) ≫
          (Operations.shriek l E o i₁).map ((properExchange l E o c d r₁ r cc wr).app M) ≫
          (gamma k₁ r₁ p₁ i₁ h₁).app ((pull l E d).obj M) := by
  sorry

end WeilConjectures.IntegralSystemRealization
