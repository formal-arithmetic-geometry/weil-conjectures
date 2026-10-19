/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.LatticeSheafLocallyConstant
public import Sheaf.NumberTheory.Padics.CoefficientExtension
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Sheaf.Topology.ContinuousMapCondensedRing
import Sheaf.AlgebraicGeometry.CondensedFieldRankDescent
import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.FieldTheory.CommonExtensionFields
import Sheaf.LinearAlgebra.ContinuousIntegralMatrixLocalSmith
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.ContinuousIntegralCoefficients
import Sheaf.Paper.GeometricFieldProEtaleEvaluation
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal

/-!
# Integral local finite presentation and constant models

Source: Hemo--Richarz--Scholbach, Example 3.1 and Theorems 4.13, 6.2 and 6.12
(blueprint: lem-sfb-integral-lfp-constant-model-comparison).

The coefficient ring is the valuation-topology ring of integers in a finite extension of
`Q_l`.  The two predicates in the equivalence are the canonical general local-finite-
presentation and finite-constant-model predicates from the pro-etale framework.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory MonObj

namespace AlgebraicGeometry.ProEtale

/-- The condensed ring `A̲` with sections `C(S, O_E)`, for the valuation ring `O_E` of the
finite extension `E / Q_l` with its valuation topology. The universe-polymorphic
continuous-map construction is used because the ring of integers has the same universe as
the base scheme. Source: Hemo--Richarz--Scholbach, Example 3.1; item statement, "Give `A` its
valuation topology" [sk-def-sfb-condensed-ring]
(blueprint: lem-sfb-integral-lfp-constant-model-comparison). -/
noncomputable def integralCondensedRing (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (ℚ_[l]) E]
    [FiniteDimensional (ℚ_[l]) E] :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  Profinite.continuousMapRingObjOfUniverse
    (latticeCoefficientIntegers l E)

/-- The canonical ring-object structure of `A̲`, from the continuous-map condensed ring.
Source: Hemo--Richarz--Scholbach, Example 3.1 [sk-def-sfb-condensed-ring]
(blueprint: lem-sfb-integral-lfp-constant-model-comparison). -/
noncomputable instance integralCondensedRingMonObj (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (ℚ_[l]) E]
    [FiniteDimensional (ℚ_[l]) E] :
    MonObj (integralCondensedRing l E) :=
  Profinite.continuousMapRingObjOfUniverseMonObj
    (latticeCoefficientIntegers l E)

/-- The ring object `A̲` is commutative, since `O_E` is commutative.
Source: Hemo--Richarz--Scholbach, Example 3.1 [sk-def-sfb-condensed-ring]
(blueprint: lem-sfb-integral-lfp-constant-model-comparison). -/
noncomputable instance integralCondensedRingComm (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (ℚ_[l]) E]
    [FiniteDimensional (ℚ_[l]) E] :
    IsCommMonObj (integralCondensedRing l E) :=
  Profinite.isCommMonObj_continuousMapRingObjOfUniverse
    (latticeCoefficientIntegers l E)

/-- The integral coefficient ring `B_X = p_X^* A̲` on the small pro-etale site of `X`.
Source: Hemo--Richarz--Scholbach, Example 3.1; item statement, "put `B_X = p_X^* A̲`"
[sk-def-sfb-pulled-back-coefficients]
(blueprint: lem-sfb-integral-lfp-constant-model-comparison). -/
noncomputable def integralCoefficientRing (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (ℚ_[l]) E]
    [FiniteDimensional (ℚ_[l]) E] (X : Scheme.{u}) :
    Mon (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
  AlgebraicGeometry.ProEtale.coefficientRing X (Mon.mk (integralCondensedRing l E))

/-- The ring-object structure of `B_X`, carried by the bundled pulled-back ring object.
Source: item statement, [sk-def-sfb-pulled-back-coefficients]
(blueprint: lem-sfb-integral-lfp-constant-model-comparison). -/
noncomputable instance integralCoefficientRingMonObj (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (ℚ_[l]) E]
    [FiniteDimensional (ℚ_[l]) E] (X : Scheme.{u}) :
    MonObj ((integralCoefficientRing l E X).X) :=
  (integralCoefficientRing l E X).mon

/-- For integral continuous coefficients on a Noetherian scheme, general local finite
presentations are equivalent to finite constant scalar local models.

Source: Hemo--Richarz--Scholbach, Example 3.1, Theorems 4.13, 6.2(2)--(3), Lemma 6.10,
Corollary 6.11(1), and Theorem 6.12(2); compare Bhatt--Scholze Definition 6.8.10 and
Proposition 6.8.11(3).

Proof (node steps):
1. `|X|` is Noetherian (minimal closed subsets), hence so is every stratum `|T|`. Given (i),
   fix a stratum `T` and a pro-etale cover `V_i → T` with presentations
   `B_{V_i}^{m_i} → B_{V_i}^{n_i} → M|_{V_i} → 0`; pullback preserves them (Cartesian
   coefficients), and the cover is flat and jointly surjective.
2. `O_E` is totally disconnected, so `B_{V_i}(U) = C(|U|, O_E)`; the entries of `F_i` are
   continuous. The class `r_i(v)` of `A^{n_i} / F_i(v) A^{m_i}` in the set of isomorphism
   classes of finite scalar cokernels is specialization invariant, as `A` is Hausdorff.
3. Over a common point `x ∈ T`, a common algebraically closed field `Ω` gives
   `Spec Ω → V_i ×_T V_j`; geometric-field evaluation, point coefficients and the
   integral regular-coefficient pullback give `r_i(v) = r_j(w)`.
4. Flat descent of specialization-invariant functions on Noetherian `|T|` makes `r_i`
   locally constant.
5. `O_E` is a DVR; continuous local Smith elimination gives an open cover with
   `L F_i R = D` for a fixed scalar diagonal `D`, so `M` is locally
   `coker D = B ⊗_A P` with `P = coker(D)` finitely presented; this gives (ii).
6. Conversely, a scalar presentation `A^u → A^v → P → 0` gives the presentation
   `B^u → B^v → B ⊗_A P → 0` by the relative-tensor universal property, so (ii) gives (i);
   this direction does not use Noetherianity.
Torsion, zero matrices, empty strata, and rank-zero presentations are included.
(blueprint: lem-sfb-integral-lfp-constant-model-comparison). -/
theorem integralLfpConstantModelComparison
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (ℚ_[l]) E]
    [FiniteDimensional (ℚ_[l]) E]
    (X : Scheme.{u}) [CompactSpace X] [IsLocallyNoetherian X]
    (M : Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (integralCoefficientRing l E X).X) :
    IsConstructibleModuleObject
        (integralCoefficientRing l E X).X M ↔
      IsConstantModelConstructible
        (integralCondensedRing l E) X M := by
  sorry

end AlgebraicGeometry.ProEtale
