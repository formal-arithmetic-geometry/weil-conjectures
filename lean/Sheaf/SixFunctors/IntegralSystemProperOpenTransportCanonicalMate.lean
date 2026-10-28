/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.SixFunctors.IntegralSystemProperOpenTransportAdjunct

/-! Normalized mate used by the canonical proper/open transport equation. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The transported mate of the intrinsic semilinear alpha in bridge coordinates.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 07A7.
(blueprint: lem-sf-integral-system-proper-open-transport-core-canonical-mate).
Proof: expand the mate under the four canonical bridge isomorphisms and use the
adjunction-conjugacy formula. -/
def properOpenTransportMate (o : Operations l E) (b : CanonicalBridge l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    Operations.push l E o r ⋙ Operations.shriek l E o i ⟶
      Operations.shriek l E o k ⋙ Operations.push l E o p :=
  (mateEquiv (o.direct r).adj (o.direct p).adj (TwoSquare.mk _ _ _ _
    (Functor.whiskerRight (b.shriek l E i).hom (pull l E p) ≫
      Functor.whiskerLeft (ProEtale.SemilinearProperOpen.J
        (scalarRings l E) (scalarTransitions l E) i) (b.pull l E p).hom ≫
      ProEtale.SemilinearProperOpen.alpha (scalarRings l E)
        (scalarTransitions l E) k r p i h ≫
      Functor.whiskerRight (b.pull l E r).inv
        (ProEtale.SemilinearProperOpen.J
          (scalarRings l E) (scalarTransitions l E) k) ≫
      Functor.whiskerLeft (pull l E r) (b.shriek l E k).inv))).natTrans

/-- The transported mate has the prescribed proper/open adjunct.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 07A7.
(blueprint: lem-sf-integral-system-proper-open-transport-core-canonical-mate-adjunct).
Proof: expand the mate under the canonical bridge, transpose with the open
adjunction, and cancel the bridge isomorphisms against the defining proper/open
lambda. The resulting equation is the adjunct characterization of the displayed
transported mate. -/
theorem properOpenTransportMate_adjunct (o : Operations l E)
    (c : Compositors l E o) (a : OpenComparisons l E o c)
    (b : CanonicalBridge l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : System l E U) :
    (o.extension i).adj.homEquiv _ _
        ((properOpenTransportMate l E o b k r p i h).app M) =
      (properOpenLambda l E o c a k r p i h).inv.app M := by
  sorry

/-- The adjunct-normalized gamma is this transported mate.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 07A7.
(blueprint: lem-sf-integral-system-proper-open-transport-core-canonical-mate-normalized).
Proof: transpose the gamma with the chosen open adjunction, identify its prescribed
proper/open lambda, and apply uniqueness of mates after canonical bridge transport. -/
theorem properOpenTransportMate_normalized (o : Operations l E)
    (c : Compositors l E o) (a : OpenComparisons l E o c)
    (b : CanonicalBridge l E o)
    (h₀ : ProperOpenTransportAdjunct l E o c a b)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : System l E U) :
    (h₀.gamma k r p i h).app M =
      (properOpenTransportMate l E o b k r p i h).app M := by
  apply ((o.extension i).adj.homEquiv _ _).injective
  rw [h₀.adjunct k r p i h M]
  exact (properOpenTransportMate_adjunct l E o c a b k r p i h M).symm

end WeilConjectures.IntegralSystemRealization
