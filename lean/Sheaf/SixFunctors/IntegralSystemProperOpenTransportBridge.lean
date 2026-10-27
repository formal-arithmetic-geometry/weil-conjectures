/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.SixFunctors.IntegralSystemProperOpenTransportIntrinsicMate

/-! Bridge transport formula for the normalized intrinsic mate. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The transported mate satisfies the bridge component equation.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 07A7.
(blueprint: lem-sf-integral-system-proper-open-transport-core-bridge-mate).
Proof: apply naturality of the four bridge isomorphisms to the mate transport
formula, then cancel the adjacent bridge factors. -/
theorem properOpenTransportMate_bridge
    (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : System l E U) :
    (properOpenTransportMate l E o b k r p i h).app M ≫
        (b.push l E p).hom.app ((Operations.shriek l E o k).obj M) ≫
        (ProEtale.SemilinearProperOpen.R (scalarRings l E)
          (scalarTransitions l E) p).map ((b.shriek l E k).hom.app M) =
      (b.shriek l E i).hom.app ((Operations.push l E o r).obj M) ≫
        (ProEtale.SemilinearProperOpen.J (scalarRings l E)
          (scalarTransitions l E) i).map ((b.push l E r).hom.app M) ≫
        (mateEquiv (ProEtale.SemilinearProperOpen.adj (scalarRings l E)
          (scalarTransitions l E) r) (ProEtale.SemilinearProperOpen.adj
            (scalarRings l E) (scalarTransitions l E) p)
          (TwoSquare.mk _ _ _ _ (ProEtale.SemilinearProperOpen.alpha
            (scalarRings l E) (scalarTransitions l E) k r p i h))).natTrans.app M := by
  sorry

end WeilConjectures.IntegralSystemRealization
