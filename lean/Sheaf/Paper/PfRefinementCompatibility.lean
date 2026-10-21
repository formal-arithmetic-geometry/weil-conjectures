/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q76
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.RefinementComparisonIsomorphism
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
import Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence
import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
import Sheaf.AlgebraicGeometry.ProperOpenComparison
import Sheaf.AlgebraicGeometry.OpenSectionClopen
import Sheaf.Paper.FiniteDirectImageComposition
import Sheaf.Paper.ProEtaleProperOpenComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
import Sheaf.AlgebraicGeometry.ProperOpenComparisonSiteNormalization
import Sheaf.Paper.CompactificationCoherence
import Sheaf.Paper.DerivedPullbackTensorIso
import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions
import Sheaf.SixFunctors.ProperOpenProjectionMate

/-!
# Refinement compatibility of finite projection transformations

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-prop-sf-pf-coherence/
prop-sf-pf-coherence.proof.md, compactification independence
(blueprint: lem-pur-pf-refinement-compatibility).

The helper definitions specialize the recorded coefficient realization, normalized comparison,
and projection square to the fixed purity datum. They contain only the canonical constructions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- Finiteness of the lifted positive-level purity coefficient quotient.
Source: def-pur-conventions and coefficient-extension finiteness
(blueprint: lem-pur-pf-refinement-compatibility). -/
instance pfRefinementCoefficientFinite (P : WeilConjectures.PurityFiniteSetting.{u}) :
    Finite P.Coefficient :=
  @Finite.of_equiv P.Coefficient P.Ring
    (Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos)
    Equiv.ulift.symm

/-- The retained bounded-below object and its etale-origin witness at the purity coefficients.
Source: def-pur-conventions and def-weil-pbc-etale-origin-witness
(blueprint: lem-pur-pf-refinement-compatibility). -/
abbrev PfRefinementOrigin (P : WeilConjectures.PurityFiniteSetting.{u}) (X : Scheme.{u}) :=
  RefinementFiniteLevelOrigin P.coefficients.l P.extension P.level P.level_pos X

/-- The existing canonical fixed-scalar realization of a retained witness.
Source: def-sf-refinement-comparison-isomorphism, coefficient realization
(blueprint: lem-pur-pf-refinement-compatibility). -/
def pfRefinementObject (P : WeilConjectures.PurityFiniteSetting.{u})
    (X : Scheme.{u}) (O : PfRefinementOrigin P X) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) :=
  refinementFiniteLevelFixedObject P.coefficients.l P.extension P.level P.level_pos X O

/-- The specified normalized comparison: direct-image composition followed by the proper
image of the inverse proper/open comparison, with the retained witness transported exactly
as in the recorded definition. This is `refinementComparisonAtWitness` specialized to A.
Source: prop-compactification-coherence-detailed and def-sf-refinement-comparison-isomorphism
(blueprint: lem-pur-pf-refinement-compatibility). -/
def pfRefinementComparison (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c₁ c₂ : Compactification f}
    (r : c₁ ⟶ c₂) (O : PfRefinementOrigin P X) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c₁).obj
      (pfRefinementObject P X O) ≅
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c₂).obj
      (pfRefinementObject P X O) :=
  letI : TopologicalSpace P.Coefficient := ⊥
  letI : DiscreteTopology P.Coefficient := discreteTopology_bot _
  refinementComparisonAtWitness P.Coefficient r O

/-- The actual tensor K ⊗ Lf*L in the ambient fixed-scalar presentation.
Source: def-exchange-projection, projection transformation
(blueprint: lem-pur-pf-refinement-compatibility). -/
def pfRefinementTensor (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) (O_K : PfRefinementOrigin P X)
    (O_L : PfRefinementOrigin P Y) :=
  ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj (pfRefinementObject P X O_K)).obj
    (L((f)^*[ModuleCat.{u + 1} P.Coefficient]).obj (pfRefinementObject P Y O_L))

/-- The square written as equality of its specified finite pro-etale composites.
The tensor witness is transported by `hT`; its source is exactly K ⊗ Lf*L, so this is the
retained etale-origin witness on that tensor, including its bounded-below assertion.
The arguments `thetaK` and `thetaT` are instantiated below only by the normalized comparisons.
Source: prop-sf-pf-coherence.proof.md, compactification independence
(blueprint: lem-pur-pf-refinement-compatibility). -/
def PfRefinementSquare (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c₁ c₂ : Compactification f)
    (O_K : PfRefinementOrigin P X) (O_L : PfRefinementOrigin P Y)
    (O_T : PfRefinementOrigin P X)
    (hT : pfRefinementTensor P f O_K O_L ≅ pfRefinementObject P X O_T)
    (thetaK :
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c₁).obj
        (pfRefinementObject P X O_K) ≅
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c₂).obj
        (pfRefinementObject P X O_K))
    (thetaT :
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c₁).obj
        (pfRefinementObject P X O_T) ≅
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c₂).obj
        (pfRefinementObject P X O_T)) : Prop :=
  ((projectionMapOfCompactification (ModuleCat.{u + 1} P.Coefficient) c₁).app
      (pfRefinementObject P X O_K)).app (pfRefinementObject P Y O_L) ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c₁).map
      hT.hom ≫ thetaT.hom ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c₂).map
      hT.inv =
  ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).map thetaK.hom).app
      (pfRefinementObject P Y O_L) ≫
    ((projectionMapOfCompactification (ModuleCat.{u + 1} P.Coefficient) c₂).app
      (pfRefinementObject P X O_K)).app (pfRefinementObject P Y O_L)

/-- The specified finite projection maps commute with every proper refinement, and with
comparison through every common refinement, on precisely the witnessed bounded-below domain.
There is no constructibility or Tor-amplitude hypothesis and no inversion of a projection map.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-prop-sf-pf-coherence/
prop-sf-pf-coherence.proof.md, sentence beginning “Independence of the compactification”
(blueprint: lem-pur-pf-refinement-compatibility).

Proof plan:
1. Finite type over k makes the compactifications Noetherian, so their open immersions are
   quasi-compact. Expand the normalized comparison as the direct-image compositor followed
   by the proper image of beta = Gamma inverse. The etale proper/open interchange and strict
   tower calculus identify Gamma with the proper/open projection mate on nu*L; the explicit
   site-normalization formula gives this identification for the specified comparison maps.
   Naturality along the retained alpha gives the same identification for K and its tensor
   (lem-cbc-proper-open-interchange-coherence, lem-cbc-strict-tower-proper-open-calculus,
   lem-sf-proper-open-comparison-site-normalization, lem-sf-proper-open-projection-mate,
   def-sf-refinement-comparison-isomorphism, prop-compactification-coherence-detailed).
2. Apply the proper/open projection-mate equation to the refinement square with the identity
   on X. Its identity projection is the identity by the counit definition, and the remaining
   open tensor maps are exactly those in def-exchange-projection. Thus the mate equation is
   the equality of the actual normalized open/proper composites, on K and the tensor.
3. Expand the counit-defined proper projection for p₂v. The pasted counit formula and the
   composition-compatible tensor and direct-image comparisons give its composition law.
   Naturality of proper projection along beta combines this law with Step 2 to give the
   first square (fix-prop-adjunctions, lem-pur-derived-pullback-tensor-iso,
   lem-weil-derived-direct-image-composition, def-exchange-projection).
4. Apply that square to both legs of an arbitrary common refinement, invert only the
   comparison isomorphisms, and compose. Identity, transitivity and the cocycle from
   prop-compactification-coherence-detailed cancel the middle comparisons and give the
   second square independently of the common refinement. -/
theorem pf_refinement_compatibility (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c₁ c₂ : Compactification f)
    (O_K : PfRefinementOrigin P X) (O_L : PfRefinementOrigin P Y)
    (O_T : PfRefinementOrigin P X)
    (hT : pfRefinementTensor P f O_K O_L ≅ pfRefinementObject P X O_T) :
    (∀ r : c₁ ⟶ c₂, PfRefinementSquare P c₁ c₂ O_K O_L O_T hT
      (pfRefinementComparison P r O_K) (pfRefinementComparison P r O_T)) ∧
    (∀ (d : Compactification f) (r₁ : d ⟶ c₁) (r₂ : d ⟶ c₂),
      PfRefinementSquare P c₁ c₂ O_K O_L O_T hT
        ((pfRefinementComparison P r₁ O_K).symm ≪≫ pfRefinementComparison P r₂ O_K)
        ((pfRefinementComparison P r₁ O_T).symm ≪≫ pfRefinementComparison P r₂ O_T)) := by
  sorry

end AlgebraicGeometry.ProEtale
