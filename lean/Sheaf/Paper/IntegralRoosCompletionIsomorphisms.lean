/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.IntegralPullbackStrictRoosNormalization
public import Sheaf.CategoryTheory.StrictRoosComparison

/-! # Descent of normalized Roos comparisons to completion isomorphisms

Source: main-20261015, det-lem-int-tensor-pullback, first paragraph and
Comparison with the Stacks Project; Stacks proetale.tex, Tags 099M and 099N (2),(5).
(blueprint: lem-sfb-integral-roos-completion-isomorphisms).

The strict towers, quotient augmentations and normalized cone coordinates are reused
from their existing owning module. Index n is the positive quotient exponent n+1.
The two completion isomorphisms are natural on the full category of flat-term
K-flat representatives, and their target categories retain the distinct coefficients.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] CategoryTheory.catToReflQuiver
attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.pbcIntegralDatum AlgebraicGeometry.Scheme.completedAdicChangeData

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralPullbackStrictRoos

/-- Descent of the two localized representative identities to natural completion
isomorphisms, keeping completed and constant coefficients separate.

Source: det-lem-int-tensor-pullback.proof.md, first paragraph and Comparison with the
Stacks Project; Stacks 099M and 099N.
(blueprint: lem-sfb-integral-roos-completion-isomorphisms).

Proof: the universal reduction counits are natural in complexes. Restrict them along
the pullback functors to the full category GoodR. Their components are invertible by
hR and hC, so they define natural isomorphisms there. For completed coefficients,
compose kappaR with the inverse reduction counit under Rlim and with the inverse of
the unit-preserving actual/quotient completion comparison. For constant coefficients,
compose kappaC with Rlim of the specified constantTowerIso and the inverse constant
reduction counit. These constructions are natural because all factors are natural.
The constant-tower derived adjunction unit agrees with completedConstantRlimUnit by
its defining unique normalization. Postcompose the two desired unit equations with
the invertible counits; for the first also postcompose with the reflector comparison.
Associativity and functoriality cancel each inverse. The resulting equations are
exactly hU and hV. No inverse of an input completion unit is used, so the argument
applies without input completeness, boundedness or constructibility.
This step asserts no existence of normalized chain data, no resolving-class
preservation, no coefficient equality and no completed-pullback comparison. -/
theorem integralRoosCompletionIsomorphisms
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [g.IsOver (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (d : pullR l E g ⋙ res l E X ≅ res l E Y ⋙ pullC l E g)
    (a : T l E g ≅ U l E g)
    (e : T l E g ⋙ towerRes l E X ≅ V l E g)
    (αU : alphaUType l E g) (αV : alphaVType l E g)
    (κR : kappaType X (R l E X)) (κC : kappaType X (C l E X))
    (hR : ∀ (P : complexesR l E Y), GoodR l E Y P →
      IsIso (completedReductionTowerComplexCounit X (datum l E)
        ((cxPullR l E g).obj P)))
    (hC : ∀ (P : complexesR l E Y), GoodR l E Y P →
      IsIso (OrderedExchange.reductionComplexCounit (datum l E) X
        (((res l E Y ⋙ pullC l E g).mapHomologicalComplex (.up ℤ)).obj P)))
    (hU : ∀ (P : complexesR l E Y), GoodR l E Y P →
      DerivedCategory.Q.map (αU P) ≫ κR.hom.app ((cxU l E g).obj P) =
        unitR l E X (DerivedCategory.Q.obj ((cxPullR l E g).obj P)) ≫
          (completedRlim X (R l E X)).map
            (completedReductionTowerComplexCounit X (datum l E)
              ((cxPullR l E g).obj P)))
    (hV : IsConstantUnitNormalized l E g d a e αV κC) :
    ∃ (eR : ObjectProperty.ι (GoodR l E Y) ⋙ cxU l E g ⋙ roosF ⋙ DerivedCategory.Q ≅
        ObjectProperty.ι (GoodR l E Y) ⋙ cxPullR l E g ⋙ DerivedCategory.Q ⋙
          pbcActualCompletion (datum l E) X)
      (eC : ObjectProperty.ι (GoodR l E Y) ⋙ cxV l E g ⋙ roosF ⋙ DerivedCategory.Q ≅
        ObjectProperty.ι (GoodR l E Y) ⋙ cxRes l E Y ⋙ cxPullC l E g ⋙
          DerivedCategory.Q ⋙ OrderedExchange.completion (datum l E) X),
      ∀ (P : complexesR l E Y) (hP : GoodR l E Y P),
        (DerivedCategory.Q.map (αU P) ≫ eR.hom.app ⟨P, hP⟩ =
          (pbcActualCompletionUnit (datum l E) X).app
            (DerivedCategory.Q.obj ((cxPullR l E g).obj P))) ∧
        (DerivedCategory.Q.map (αV P) ≫ eC.hom.app ⟨P, hP⟩ =
          (OrderedExchange.unit (datum l E) X).app
            (DerivedCategory.Q.obj ((cxPullC l E g).obj ((cxRes l E Y).obj P)))) := by sorry

end WeilConjectures.IntegralPullbackStrictRoos
