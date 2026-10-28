/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.IntegralCompactificationRealizationData

/-! Bridge cancellation form of the transported adjunct normalization. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/--
The bridge-transported intrinsic gamma has the prescribed adjunct after converting
its codomain to canonical semilinear coordinates.  This is the mate-cancellation
step: expand the four bridge factors, apply the intrinsic `gamma_adjunct` equation,
and identify the resulting composite with `properOpenLambda`; the final item
cancels the displayed canonical pullback isomorphism.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 0F7B and 07A7.
(blueprint: lem-sf-integral-system-proper-open-transport-adjunct-bridge)
-/
theorem transportedGamma_adjunct_bridge (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : System l E U) :
    (o.extension i).adj.homEquiv _ _
        (((Operations.shriek l E o i).map ((b.push l E r).hom.app M) ≫
          (b.shriek l E i).hom.app
            ((ProEtale.SemilinearProperOpen.R (scalarRings l E)
              (scalarTransitions l E) r).obj M) ≫
          (ProEtale.SemilinearProperOpen.gamma (scalarRings l E)
            (scalarTransitions l E) k r p i h).app M ≫
          (b.push l E p).inv.app
            ((ProEtale.SemilinearProperOpen.J (scalarRings l E)
              (scalarTransitions l E) k).obj M) ≫
          (Operations.push l E o p).map
            ((b.shriek l E k).inv.app M))) ≫
      (b.pull l E i).hom.app
        ((Operations.shriek l E o k ⋙ Operations.push l E o p).obj M) =
      (properOpenLambda l E o c a k r p i h).inv.app M ≫
        (b.pull l E i).hom.app
          ((Operations.shriek l E o k ⋙ Operations.push l E o p).obj M) := by
  sorry

end WeilConjectures.IntegralSystemRealization
