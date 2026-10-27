/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.IntegralPullbackStrictRoosData
/-! # Integral Roos resolving counits

Source: det-lem-int-tensor-pullback.proof.md, first and comparison paragraphs;
Stacks 093M, 0941, 099M and 099N.
(blueprint: lem-sfb-integral-roos-resolving-counits).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.pbcIntegralDatum AlgebraicGeometry.Scheme.completedAdicChangeData

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralPullbackStrictRoos

/-- Pullback and scalar restriction preserve the resolving class, and its four
canonical representative comparisons are invertible.

Source: det-lem-int-tensor-pullback.proof.md, first and comparison paragraphs;
Stacks 093M and 0G7E. (blueprint: lem-sfb-integral-roos-resolving-counits).

Proof: completed coefficients are flat over constant coefficients by constant
completion equivalence. Flat scalar restriction and ringed-topos pullback preserve
flat-term K-flat complexes, giving the three Good predicates. Their reduction and
ordinary pullback counits are invertible by the K-flat computation laws. For the
pulled tower use exactness of completed-coefficient inverse image: it preserves
quasi-isomorphisms levelwise. Apply its derived computation to a strict diagram
K-flat replacement of the quotient tower. Compose its comparison with the source
reduction counit to obtain towerCounit. This argument applies even when the individual
finite quotient terms are not K-flat over the completed ring. -/
theorem integralRoosResolvingCounits
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [g.IsOver (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))] :
    ∀ (P : complexesR l E Y), GoodR l E Y P →
      (GoodR l E X ((cxPullR l E g).obj P) ∧
        GoodC l E Y ((cxRes l E Y).obj P) ∧
        GoodC l E X ((cxPullC l E g).obj ((cxRes l E Y).obj P))) ∧
      (IsIso (towerCounit l E g P) ∧
        IsIso (completedOrdinaryPullbackComplexCounit g (datum l E) P) ∧
        IsIso (completedReductionTowerComplexCounit X (datum l E)
          ((cxPullR l E g).obj P)) ∧
        IsIso (OrderedExchange.reductionComplexCounit (datum l E) X
          (((res l E Y ⋙ pullC l E g).mapHomologicalComplex (.up ℤ)).obj P))) := by sorry

end WeilConjectures.IntegralPullbackStrictRoos
