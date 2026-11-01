/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import Mathlib.AlgebraicGeometry.Sites.Proetale

import WeilConjectures.AlgebraicGeometry.Native.NativeFiniteTwistLocalLine
import WeilConjectures.AlgebraicGeometry.Native.NativeIntegralTwistLocalLine
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTateBasis
import WeilConjectures.AlgebraicGeometry.Native.NativeSignedLine
import WeilConjectures.Algebra.Homology.LineUnbounded.LineUnboundedDerivedTensor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Homology.ProperBaseChange.AlgebraicInverseImageOfTransport
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonConstruction
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory

/-! # Tate twists preserve finiteness conditions

Source: `literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors-basics/
sec-ctf-finite-foundations/sk-prop-ctf-finite-comparison/sk-prop-sp-et-proet/
prop-weil-twist-preserves.md` (blueprint: prop-weil-twist-preserves).

The four coefficient families are the finite, integral, rational and algebraically closed
pulled-back condensed rings from `def-coefficient-twists-detailed`. The statement records,
for every signed twist, local triviality, invertibility, preservation of finite constant
scalar-model bounded constructibility, and preservation of finite Tor amplitude.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/--
For a prime `l`, a finite extension `E` of `ℚ_[l]`, and a scheme `X` on which `l` is
invertible, every signed coefficient twist is locally trivial and invertible. Tensoring
by its degree-zero derived object preserves the finite constant scalar-model bounded
constructibility predicate and finite Tor amplitude.

Source: blueprint `prop-weil-twist-preserves`, entire proposition
(blueprint: prop-weil-twist-preserves). The four conjuncts render the finite, integral,
rational, and algebraically closed coefficient cases from `def-coefficient-twists-detailed`.

Proof steps for stage 3:
1. On the pro-etale site, use the first lines from `def-coefficient-twists-detailed`.
   The finite and integral lines have local regular bases by
   `lem-twist-native-finite-local-line` and `lem-twist-native-integral-local-line`;
   scalar extension carries an integral basis to an `E`-basis, while
   `lem-poincare-integral-tate-local-basis` trivializes the actual `ℤ_l(1)` line;
   scalar extension then trivializes the prescribed algebraically closed coefficient line.
2. By `lem-twist-native-signed-line`, signed tensor and internal-Hom powers are locally
   regular and invertible, with the opposite power as dual. Applying
   `lem-pur-line-unbounded-derived-tensor` to the pulled-back coefficient ring gives the
   ordinary tensor comparison and the homology formula for every unbounded complex.
3. Refine each finite constant scalar-model cover from `sk-def-sfb-constructible` by a
   trivializing cover for the twist. Pullback commutes with tensor by
   `lem-weil-pbc-ringed-topoi-module-pullback-tensor`, so the finite scalar model remains
   valid; the same argument on affine opens handles arbitrary schemes. At finite
   coefficients this keeps the finite strata, local constancy and finite stalks of
   `def-weil-finite-torsion-constructibility`. Step 2 preserves constructible cohomology
   and its finite vanishing interval, which proves bounded constructibility.
4. For finite Tor amplitude from `def-weil-finite-tor-amplitude`, derived associativity
   from `lem-sfb-derived-monoidal` identifies tensoring first by the twist and then by any
   degree-zero module with the reverse order. Step 2 preserves the cohomological vanishing
   interval, so the same interval proves the finite Tor clause for all four coefficient rings.
-/
theorem twist_preserves_finiteness
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] :
    (∀ n : ℕ,
      (∀ m : ℤ, ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
        Nonempty (((upperStar Ab.{u + 1} (𝒰.f i)).mapMod
          (condensedRingObj (twistFiniteRing l E n) X)).obj
            (coefficientSignedTwist X (condensedRingObj (twistFiniteRing l E n) X)
              (coefficientFiniteTwistOne l E X n) m) ≅
          Mod.regular ((upperStar Ab.{u + 1} (𝒰.f i)).obj
            (condensedRingObj (twistFiniteRing l E n) X)))) ∧
      (∀ m : ℤ, IsInvertible
        (coefficientSignedTwist X (condensedRingObj (twistFiniteRing l E n) X)
          (coefficientFiniteTwistOne l E X n) m)) ∧
      (∀ (m : ℤ) (K : DerivedCategory.{u + 1}
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (condensedRingObj (twistFiniteRing l E n) X))),
        constantModelBoundedConstructible (twistFiniteRing l E n) X K →
          constantModelBoundedConstructible (twistFiniteRing l E n) X
            (K ⊗ (_root_.DerivedCategory.singleFunctor.{u + 1, u + 1, u + 2} _ 0).obj
              (coefficientSignedTwist X (condensedRingObj (twistFiniteRing l E n) X)
                (coefficientFiniteTwistOne l E X n) m))) ∧
      (∀ (m : ℤ) (K : DerivedCategory.{u + 1}
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (condensedRingObj (twistFiniteRing l E n) X))),
        _root_.DerivedCategory.finiteTorAmplitude.{u + 1, u + 1, u + 2} _ K →
          _root_.DerivedCategory.finiteTorAmplitude.{u + 1, u + 1, u + 2} _
            (K ⊗ (_root_.DerivedCategory.singleFunctor.{u + 1, u + 1, u + 2} _ 0).obj
              (coefficientSignedTwist X (condensedRingObj (twistFiniteRing l E n) X)
                (coefficientFiniteTwistOne l E X n) m)))) ∧
    ((∀ m : ℤ, ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
        Nonempty (((upperStar Ab.{u + 1} (𝒰.f i)).mapMod
          (condensedRingObj (twistIntegralRing l E) X)).obj
            (coefficientSignedTwist X (condensedRingObj (twistIntegralRing l E) X)
              (coefficientIntegralTwistOne l E X) m) ≅
          Mod.regular ((upperStar Ab.{u + 1} (𝒰.f i)).obj
            (condensedRingObj (twistIntegralRing l E) X)))) ∧
      (∀ m : ℤ, IsInvertible
        (coefficientSignedTwist X (condensedRingObj (twistIntegralRing l E) X)
          (coefficientIntegralTwistOne l E X) m)) ∧
      (∀ (m : ℤ) (K : DerivedCategory.{u + 1}
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (condensedRingObj (twistIntegralRing l E) X))),
        constantModelBoundedConstructible (twistIntegralRing l E) X K →
          constantModelBoundedConstructible (twistIntegralRing l E) X
            (K ⊗ (_root_.DerivedCategory.singleFunctor.{u + 1, u + 1, u + 2} _ 0).obj
              (coefficientSignedTwist X (condensedRingObj (twistIntegralRing l E) X)
                (coefficientIntegralTwistOne l E X) m))) ∧
      (∀ (m : ℤ) (K : DerivedCategory.{u + 1}
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (condensedRingObj (twistIntegralRing l E) X))),
        _root_.DerivedCategory.finiteTorAmplitude.{u + 1, u + 1, u + 2} _ K →
          _root_.DerivedCategory.finiteTorAmplitude.{u + 1, u + 1, u + 2} _
            (K ⊗ (_root_.DerivedCategory.singleFunctor.{u + 1, u + 1, u + 2} _ 0).obj
              (coefficientSignedTwist X (condensedRingObj (twistIntegralRing l E) X)
                (coefficientIntegralTwistOne l E X) m)))) ∧
    ((∀ m : ℤ, ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
        Nonempty (((upperStar Ab.{u + 1} (𝒰.f i)).mapMod
          (condensedRingObj (twistRationalRing l E) X)).obj
            (coefficientSignedTwist X (condensedRingObj (twistRationalRing l E) X)
              (coefficientRationalTwistOne l E X) m) ≅
          Mod.regular ((upperStar Ab.{u + 1} (𝒰.f i)).obj
            (condensedRingObj (twistRationalRing l E) X)))) ∧
      (∀ m : ℤ, IsInvertible
        (coefficientSignedTwist X (condensedRingObj (twistRationalRing l E) X)
          (coefficientRationalTwistOne l E X) m)) ∧
      (∀ (m : ℤ) (K : DerivedCategory.{u + 1}
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (condensedRingObj (twistRationalRing l E) X))),
        constantModelBoundedConstructible (twistRationalRing l E) X K →
          constantModelBoundedConstructible (twistRationalRing l E) X
            (K ⊗ (_root_.DerivedCategory.singleFunctor.{u + 1, u + 1, u + 2} _ 0).obj
              (coefficientSignedTwist X (condensedRingObj (twistRationalRing l E) X)
                (coefficientRationalTwistOne l E X) m))) ∧
      (∀ (m : ℤ) (K : DerivedCategory.{u + 1}
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (condensedRingObj (twistRationalRing l E) X))),
        _root_.DerivedCategory.finiteTorAmplitude.{u + 1, u + 1, u + 2} _ K →
          _root_.DerivedCategory.finiteTorAmplitude.{u + 1, u + 1, u + 2} _
            (K ⊗ (_root_.DerivedCategory.singleFunctor.{u + 1, u + 1, u + 2} _ 0).obj
              (coefficientSignedTwist X (condensedRingObj (twistRationalRing l E) X)
                (coefficientRationalTwistOne l E X) m)))) ∧
    ((∀ m : ℤ, ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
        Nonempty (((upperStar Ab.{u + 1} (𝒰.f i)).mapMod
          (condensedRingObj (Profinite.padicAlgClRingObj l) X)).obj
            (tateTwist X l m) ≅
          Mod.regular ((upperStar Ab.{u + 1} (𝒰.f i)).obj
            (condensedRingObj (Profinite.padicAlgClRingObj l) X)))) ∧
      (∀ m : ℤ, IsInvertible (tateTwist X l m)) ∧
      (∀ (m : ℤ) (K : DerivedCategory.{u + 1}
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (condensedRingObj (Profinite.padicAlgClRingObj l) X))),
        constantModelBoundedConstructible (Profinite.padicAlgClRingObj l) X K →
          constantModelBoundedConstructible (Profinite.padicAlgClRingObj l) X
            (K ⊗ (_root_.DerivedCategory.singleFunctor.{u + 1, u + 1, u + 2} _ 0).obj
              (tateTwist X l m))) ∧
      (∀ (m : ℤ) (K : DerivedCategory.{u + 1}
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (condensedRingObj (Profinite.padicAlgClRingObj l) X))),
        _root_.DerivedCategory.finiteTorAmplitude.{u + 1, u + 1, u + 2} _ K →
          _root_.DerivedCategory.finiteTorAmplitude.{u + 1, u + 1, u + 2} _
            (K ⊗ (_root_.DerivedCategory.singleFunctor.{u + 1, u + 1, u + 2} _ 0).obj
              (tateTwist X l m)))) := by
  sorry

end AlgebraicGeometry.ProEtale
