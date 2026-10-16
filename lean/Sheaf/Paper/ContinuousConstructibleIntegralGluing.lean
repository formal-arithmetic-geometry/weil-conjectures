/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ContinuousIntegralCoefficients

/-! # Assembling given integral models on a finite stratification

Source: Bhatt--Scholze, Lemmas 6.8.12--6.8.13 and Proposition 6.8.14(2).
(blueprint: lem-weil-pbc-continuous-constructible-integral-gluing)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]

/-- Constructible ordinary integral models on the parts of a finite stratification
suffice to construct an ordinary integral model of the whole rational sheaf.
Source: Bhatt--Scholze, the filtration and Ext1 argument at the end of Lemma 6.8.13
and the essential-surjectivity argument of Proposition 6.8.14(2).
(blueprint: lem-weil-pbc-continuous-constructible-integral-gluing)

Proof in words. Refine the given finite stratification to a finite filtration by
closed subsets, and restrict the supplied integral models to the new pieces.
Exact extension by zero for an open piece and exact direct image for a closed piece
preserve constructibility: stratify its support by the given integral strata and
use the zero module on the complementary strata. These extension functors commute
with localization, since localization is the filtered colimit of multiplication by
ℓ and closed direct image commutes with these colimits. Thus their degree-zero
complexes lie in the essential image of integral bounded constructible scalar
extension. Each open--closed short exact sequence gives a distinguished triangle.
The triangulated-closure theorem for that essential image (the denominator-clearing
consequence of Lemma 6.8.12) and induction through the filtration give an integral
bounded constructible complex K whose scalar extension is F in degree zero.
Take N = H⁰(K). This is constructible by the definition of bounded constructibility.
Integral scalar localization is exact, so taking H⁰ of the isomorphism gives the
required ordinary scalar-extension isomorphism for N. This argument permits
rescaling the supplied models and does not require them to glue unchanged. Zero
and empty pieces use zero; a stratification with no pieces forces X to be empty.
Constructing the initial models of the strata is a separate obligation. -/
theorem continuousConstructible_integral_gluing (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (S : Scheme.Stratification X)
    (hmodels : ∀ a : Fin S.n,
      ∃ N : Mod (Sheaf (Scheme.ProEt.topology (S.domain a)) Ab.{u + 1})
          ((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).obj
            (condensedRingObj (integralCoeff ℓ E) X)),
        ProEtale.IsConstructibleModuleObject
          ((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).obj
            (condensedRingObj (integralCoeff ℓ E) X)) N ∧
        Nonempty ((Mod.extendScalars
          ((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).map
            (coefficientMap (integralScalarMap ℓ E) X))).obj N ≅
          ((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).mapMod
            (condensedRingObj (Profinite.continuousMapRingObj E) X)).obj F)) :
    ∃ N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X),
      ProEtale.IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) X) N ∧
      Nonempty ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj N ≅ F) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
