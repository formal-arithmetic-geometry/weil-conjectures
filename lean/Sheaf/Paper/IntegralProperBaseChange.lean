/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.Paper.CondensedAmbientExchange
public import Sheaf.Paper.ModuleObjectProjectionMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison
import Sheaf.AlgebraicGeometry.IntegralConstantCompletion
import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.BasicOperationsCoefficientReduction
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Paper.DerivedNakayamaFirstReduction
import Sheaf.Paper.DerivedNakayamaResolution
import Sheaf.Paper.FiniteProperBaseChange
import Sheaf.Paper.IntegralCriterionReductions
import Sheaf.Paper.ProjectionFormulaBaseChangeNaturality
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Sheaf.Paper.IntegralModels
/-!
# Proper base change with integral adic coefficients

Source: blueprint main-20261015, sec-six-functors-basics,
`sk-thm-sfb-proper-base-change/sk-thm-sfb-proper-base-change-integral.md`
(blueprint: det-thm-sfb-proper-base-change-integral).

## Main statements

* `integralProperDirectImageAndFormulas`: proper direct image, derived Nakayama, and the
  proper base change and projection formula isomorphisms for integral coefficients.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Proper direct image, derived Nakayama, and the two canonical proper formulas
for bounded constructible integral adic complexes.
Source: blueprint main-20261015, sec-six-functors-basics,
`sk-thm-sfb-proper-base-change/sk-thm-sfb-proper-base-change-integral.md`
(blueprint: det-thm-sfb-proper-base-change-integral).

Proof (the node's ten steps):
1. The coefficients are the pulled-back continuous ring `O_E` of the adic datum
   `(A, I) = (O_E, (π))`: `O_E` is a Noetherian complete DVR with finite residue field
   `κ` killed by `ℓ`, the quotients `P_n = O_E/π^n` are finite and perfect, and the
   pulled-back ring is identified with the completed coefficient sheaf.
2. For `L ∈ Dbc(T, O_E)` put `L_n = L ⊗^L P_n`. By the integral-models lemma (2), `L`
   is derived complete and `L_1` is bounded constructible, classical and of finite Tor
   dimension, so `L_1 ∈ Dctf(T, κ)`; conversely a complete `L` with bounded
   constructible classical `L_1` lies in `Dbc`. The reductions `L_n` are bounded
   constructible in one interval independent of `n`.
3. The completed direct-image theorem gives the canonical projection comparisons
   `ρ_{p,n} : (Rp_*K) ⊗^L P_n ≅ Rp_*(K_n)`, compatible with the transitions, and
   `Rp_*K ≅ R lim_n Rp_*K_n`. Hence `Rp_*K` is derived complete, and `n = 1` gives the
   reduction isomorphism of clause (1); the two-term resolution identifies the
   coefficient quotient with the cone of `π`.
4. The finite theorem (1) gives `Rp_*K_1 ∈ Dctf(Y, κ)`, classical by the constructible
   comparison. The direct-image reduction comparison identifies it with `(Rp_*K)_1`
   in `D(κ_Y)`, so the converse integral criterion gives `Rp_*K ∈ Dbc(Y, O_E)`.
5. Derived Nakayama: for complete `C` with `C_1 = 0`, the triangles
   `C_1 → C_{n+1} → C_n → C_1[1]` give `C_n = 0` by induction, and completeness gives
   `C ≅ R lim_n C_n = 0`; no boundedness is used.
6. In the square, `p'` is proper by permanence, `X'` is a standing scheme, and the
   integral-models lemma (3) with step 4 puts `g^*Rp_*K`, `Rp'_*g'^*K`,
   `Rp_*K ⊗^L M` and `Rp_*(K ⊗^L p^*M)` in `Dbc`, hence derived complete.
7. The ambient exchange `β_K` is the unit, pullback comparison, counit composite; the
   operation-reduction lemma preserves units, counits and the comparison, so
   `(β_K)_1` is the finite-coefficient exchange `β_{K_1}`.
8. The projection map `α_{K,M}` is the adjunct of `(ε_K ⊗ 1) ∘ t_p`; the same lemma and
   the balancing isomorphism identify `(α_{K,M})_1` with `α_{K_1,M_1}`.
9. The finite theorem (2) and (3) make `β_{K_1}` and `α_{K_1,M_1}` isomorphisms.
10. The cones of `β_K` and `α_{K,M}` are complete, with zero first reduction by
    exactness of reduction and step 9; step 5 kills them, proving clause (3).
-/
theorem integralProperDirectImageAndFormulas
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] :
    (∀ (K : DerivedCategory (AdicCompletion.Modules l E X)),
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K →
      IsDerivedComplete l E Y
        ((moduleObjectDerivedPushforward (DerivedNakayama.integerRing l E) p).obj K) ∧
      Nonempty
        ((AdicCompletion.derivedReduction l E Y 0).obj
            ((moduleObjectDerivedPushforward (DerivedNakayama.integerRing l E) p).obj K) ≅
          (moduleObjectDerivedPushforward
              (DerivedNakayama.quotientRing l E 1) p).obj
            ((AdicCompletion.derivedReduction l E X 0).obj K)) ∧
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) Y
        ((moduleObjectDerivedPushforward (DerivedNakayama.integerRing l E) p).obj K)) ∧
    (∀ (C : DerivedCategory (AdicCompletion.Modules l E X)),
      IsDerivedComplete l E X C →
      IsZero ((AdicCompletion.derivedReduction l E X 0).obj C) → IsZero C) ∧
    (∀ {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (p' : X' ⟶ Y') (g' : X' ⟶ X)
      (sq : ChosenCartesianSquare g' p' p g)
      (K : DerivedCategory (AdicCompletion.Modules l E X)),
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K →
      IsIso ((condensedAmbientExchange (DerivedNakayama.integerRing l E) sq).app K)) ∧
    (∀ (K : DerivedCategory (AdicCompletion.Modules l E X))
      (M : DerivedCategory (AdicCompletion.Modules l E Y)),
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K →
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) Y M →
      IsIso (moduleObjectProjectionMap (DerivedNakayama.integerRing l E) p K M)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
