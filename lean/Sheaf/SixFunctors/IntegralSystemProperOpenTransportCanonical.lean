/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.IntegralSystemProperOpenTransportAdjunct

/-! Canonical part of the intrinsic proper/open transport package. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The canonical bridge compatibility for an adjunct-normalized gamma.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 0F7B and 07A7.
(blueprint: lem-sf-integral-system-proper-open-transport-core-canonical).
Proof: substitute the transported gamma and cancel adjacent bridge isomorphisms;
naturality of the bridge and the intrinsic canonical gamma equation leave the
stated canonical clause. -/
theorem integralSystemProperOpenTransportCanonical (o : Operations l E)
    (c : Compositors l E o) (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    (h₀ : ProperOpenTransportAdjunct l E o c a b) :
    ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
      (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
      [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
      (h : k ≫ p = r ≫ i) (M : System l E U),
      (h₀.gamma k r p i h).app M ≫
        (b.push l E p).hom.app ((Operations.shriek l E o k).obj M) ≫
        (ProEtale.SemilinearProperOpen.R (scalarRings l E) (scalarTransitions l E) p).map
          ((b.shriek l E k).hom.app M) =
      (b.shriek l E i).hom.app ((Operations.push l E o r).obj M) ≫
        (ProEtale.SemilinearProperOpen.J (scalarRings l E) (scalarTransitions l E) i).map
          ((b.push l E r).hom.app M) ≫
        (ProEtale.SemilinearProperOpen.gamma (scalarRings l E) (scalarTransitions l E)
          k r p i h).app M := by
  sorry

end WeilConjectures.IntegralSystemRealization
