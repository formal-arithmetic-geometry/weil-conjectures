/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionTowerCurrentStatement
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.IntegralConstructibleHeart
import WeilConjectures.AlgebraicGeometry.StrictCoefficientTensor.StrictCoefficientTensorDescent
import WeilConjectures.AlgebraicGeometry.Picard.SuccessiveDerivedQuotientNormalization
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.CategoryTheory.Site.SiteDerivedTensorRestriction
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafOperations
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafClosedLocalization
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafBaseChangeMates
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import WeilConjectures.CategoryTheory.Sites.FixedCoefficientDerivedChangeOfRings
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientSerre
import WeilConjectures.CategoryTheory.TruncationTriangle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection

/-!
# Normalized reduction towers in the integral-heart setting

Source: blueprint latest, part-duality-trace-formula/sec-smooth-purity/sec-sp-grp-setup/
sec-coefficients/sk-prop-sp-integral-towers/`sk-prop-sp-integral-towers-reduction.md`
and its proof, Construction, Normalization, and Constructibility
(blueprint: det-sp-reduction-tower-normalized).

The source of `red` is the ordinary unbounded derived category of modules over the
pulled-back condensed valuation ring. Its comparison with the existing strict
construction is through the exact internal/section-module equivalence. Construction
and normalization have no geometric hypotheses. Constructibility uses precisely the
separated finite-type field setting of `sk-lem-int-integral-heart`. The current
Q42 statement and its proof apply over every field with `l` invertible; the former
finite-or-algebraically-closed restriction is not part of this setting.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

-- The general instances have an unconstrained coefficient-size parameter.
-- Use the existing fixed-size pro-etale instances for this declaration only.
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralReductionSiteEssentiallySmall in
/-- Derived reductions form a functorial normalized strict coefficient tower for every
scheme. In the integral-heart setting, bounded constructible integral complexes give
normalized constructible finite-Tor towers, retaining every Tor interval.

Source: blueprint latest, part-duality-trace-formula/sec-smooth-purity/sec-sp-grp-setup/
sec-coefficients/sk-prop-sp-integral-towers/`sk-prop-sp-integral-towers-reduction.md`
and its proof, all three paragraphs; part-six-operations/sec-constructibility-upper-shriek/
sec-ladic-summary/sec-i-heart/`sk-lem-int-integral-heart`, standing field and finite-type setting
(blueprint: det-sp-reduction-tower-normalized).

Proof:
1. Choose a flat-term K-flat representative P over the pulled-back condensed integral
ring. Strict coefficient-tensor descent (lem-sp-strict-coefficient-tensor-descent)
forms the complex of towers with levels P tensor R_n and quotient-induced transitions.
It preserves quasi-isomorphisms between these representatives, and hence descends
independently of representatives to a functor on ordinary derived categories. Exact
evaluation (det-sp-coefficient-towers-abelian) gives M tensor^L R_n. The exact
internal/section-module equivalence identifies this construction with r.red.
2. Successive derived scalar extension
(lem-sfb-successive-derived-quotient-normalization) is the associativity isomorphism
(x tensor c) tensor d mapped to x tensor c-bar d, with inverse x tensor d mapped to
(x tensor 1) tensor d. Its quotient-transition normalization identifies it with the
specified reduction map, including the identity case m = n. Thus every M is normalized.
3. Now assume the integral-heart field and geometric hypotheses, over any field
with l invertible (Q42 general-field audit of sk-lem-int-integral-heart). By
sk-lem-int-integral-heart and finite truncation triangles
(lem-weil-pbc-truncation-triangle), M is a finite extension of shifted stratum sheaves
a_!C. Exact open/closed sequences (det-sf-open-closed-sequence-ring-sheaf) and the finite
stratified scalar models give these pieces with stratum Tor amplitude [-1,0]. A
length-one finite free DVR resolution reduces to finite free quotient modules, whose
cohomology is constructible. Open and closed immersion tensor projection
(lem-sfb-open-immersion-derived-tensor-projection and
lem-sfb-closed-immersion-derived-tensor-projection) identifies the reductions of a_!C
with a_! of its reductions. Extension by zero and the constructible Serre property
(lem-weil-constructible-coefficient-serre) preserve constructibility. Derived coefficient
change (lem-pur-derived-change-of-rings) preserves the finite extension and shift steps;
their number and shifts are independent of n.
4. The same projection formulas give the Tor bounds of the shifted stratum pieces;
finite shifts and extensions give finite Tor amplitude for M
(det-def-sfb-constructible-tor-amplitude). For every Tor interval [a,b] of M, balanced
derived tensor/restriction (lem-trf-site-derived-tensor-restriction) identifies tensor
of its nth reduction with a quotient-module N with M tensor Res N. This transfers the
same interval to every level. Testing with the quotient ring bounds cohomology in the
same interval. Combined with constructibility and normalization, these uniform bounds
are precisely sk-def-sp-normalized-towers.
-/
theorem sp_reduction_tower_integral_heart_statement
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T) :
    ∃ r : SpReductionTowerConstruction l E T D,
      ∃ red : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
            (condensedRingObj (spIntegralCondensed l E) T)) ⥤
          spDerivedCoefficientTowers l E T D,
        Nonempty (spIntegralInternalization l E T ⋙ red ≅ r.red) ∧
        (∀ M, IsSpNormalizedTower l E T D (red.obj M)) ∧
        (∀ (k : Type u) [Field k], IsUnit (l : k) →
          ∀ [T.Over (Spec (.of k))]
            [IsSeparated (T ↘ Spec (.of k))]
            [LocallyOfFiniteType (T ↘ Spec (.of k))]
            [QuasiCompact (T ↘ Spec (.of k))],
            ∀ M, constantModelBoundedConstructible (spIntegralCondensed l E) T M →
              DerivedCategory.finiteTorAmplitude.{u + 1, u + 1, u + 2}
                (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
                  (condensedRingObj (spIntegralCondensed l E) T)) M ∧
              spNormalizedConstructibleTorTowers l E T D (red.obj M) ∧
              ∀ (a b : ℤ), a ≤ b →
                DerivedCategory.torAmplitudeIn.{u + 1, u + 1, u + 2}
                  (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
                    (condensedRingObj (spIntegralCondensed l E) T)) a b M →
                ∀ n : ℕ,
                  Scheme.HasProEtaleTorAmplitude T
                    (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))
                    ((spDerivedCoefficientEvaluation l E T D n).obj (red.obj M)) a b ∧
                  ∀ i : ℤ, (i < a ∨ b < i) → IsZero
                    ((@DerivedCategory.homologyFunctor
                      (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T
                        (Padic.coefficientExtensionIntegers l E ⧸
                          spEllIdeal l E ^ (n + 1))))
                      _ _ (HasDerivedCategory.standard _) i).obj
                      ((spDerivedCoefficientEvaluation l E T D n).obj (red.obj M)))) := by
  sorry

end AlgebraicGeometry.ProEtale
