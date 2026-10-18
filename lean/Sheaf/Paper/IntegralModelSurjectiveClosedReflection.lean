/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.Paper.CondensedConstantConstructibility
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.CategoryTheory.SiteInverseImageTensor
import Sheaf.Paper.ProEtaleSurjectiveClosedCoverRefinement
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import Sheaf.Paper.CondensedSurjectiveClosedEquivalence

/-!
# Reflection of integral finite constant models across surjective closed immersions

Source: Stacks Project, Tags 09AB and 09BK; blueprint main-20261015,
`det-lem-int-ext-formula`, proof (1)
(blueprint: lem-sfb-integral-model-surjective-closed-reflection).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The condensed valuation ring of the finite p-adic extension, with continuous-function
sections and the topology of the unique extending spectral absolute value. This merely
specializes the existing continuous coefficient construction.
Source: blueprint det-lem-int-ext-formula, proof (1)
(blueprint: lem-sfb-integral-model-surjective-closed-reflection). -/
noncomputable def integralModelCondensedCoefficients (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  letI := spectralNorm.normedField (Padic l) E
  Mon.mk (Profinite.continuousCoefficientRingObj (Padic.coefficientExtensionIntegers l E))

/-- The integral condensed coefficient ring is commutative, by its pointwise operations.
Source: blueprint det-lem-int-ext-formula, proof (1)
(blueprint: lem-sfb-integral-model-surjective-closed-reflection). -/
noncomputable instance integralModelCondensedCoefficients_isCommMonObj
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    IsCommMonObj (integralModelCondensedCoefficients l E).X :=
  letI := spectralNorm.normedField (Padic l) E
  inferInstanceAs (IsCommMonObj
    (Profinite.continuousCoefficientRingObj (Padic.coefficientExtensionIntegers l E)))

/-- A module has finite constant integral local models exactly when its pullback across a
surjective closed immersion does. In the existing `HasFiniteConstantLocalModel` interface,
scalar models are finite presentations on the point. Their matrices have entries in
`A = O_E`, and their pullbacks are `B_U ⊗_{A_U} P_U` through the constant-section map.
Since A is a DVR, its finitely generated modules are exactly its finitely presented modules;
thus this includes torsion modules and allows a different module on each cover member.

Source: Stacks Project Tags 09AB and 09BK; blueprint det-lem-int-ext-formula, proof (1)
(blueprint: lem-sfb-integral-model-surjective-closed-reflection).

Proof:
1. Write C_T(P) for the scalar-extension model. The abelian inverse image is strong
monoidal and preserves colimits (`lem-weil-pbc-left-exact-site-inverse-image-tensor`).
It preserves constant abelian sheaves by their presentations by sums of copies of Z.
Apply it to the relative tensor coequalizer of `sk-def-sfb-change-of-scalars`. The
untwisted coefficient isomorphism of `sk-prop-sfb-cartesian-coefficients` identifies
f^* C_T(P) with C_S(P), without flatness or freeness assumptions on P.
2. Pull the covering in (a) back to Z using `def-weil-proetale-inverse-image`.
The composition isomorphisms of `sk-def-sfb-module-pushforward-pullback` and step 1 give
(b), using the same scalar modules.
3. Conversely apply `new-lem-weil-pbc-proetale-surjective-closed-cover-refinement` to
the cover in (b). It gives a cover T_gamma of X whose closed fibres W_gamma refine
that cover of Z. The projections W_gamma -> T_gamma are surjective closed immersions,
by `lem-weil-pbc-surjective-closed-immersion-universal-homeomorphism`.
4. Pull the models in (b) to W_gamma and use step 1 and composition of module pullbacks.
By `new-lem-weil-pbc-condensed-surjective-closed-equivalence`, pullback from T_gamma to
W_gamma is fully faithful. Lift each model isomorphism and its inverse by fullness;
faithfulness verifies their composites are identities. This gives (a) on the cover
T_gamma without gluing different models. No Noetherianity or nilpotence bound is used. -/
theorem integralModel_surjective_closed_reflection
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [Surjective i]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralModelCondensedCoefficients l E).X X)) :
    HasFiniteConstantLocalModel (integralModelCondensedCoefficients l E).X X F ↔
      HasFiniteConstantLocalModel (integralModelCondensedCoefficients l E).X Z
        ((CondensedRing.upperStar (integralModelCondensedCoefficients l E).X i).obj F) := by
  sorry

end AlgebraicGeometry.ProEtale
