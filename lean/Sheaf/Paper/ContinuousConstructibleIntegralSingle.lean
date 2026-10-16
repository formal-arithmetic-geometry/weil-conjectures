/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.Paper.ContinuousIntegralCoefficients
import Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed

/-! # Integral models for constructible sheaves in degree zero

Source: Bhatt--Scholze, Lemma 6.8.13 and the sheaf case of Proposition 6.8.14(2).
(blueprint: lem-weil-pbc-continuous-constructible-integral-single)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]

/-- A constructible continuous E module, placed in degree zero, has an integral model.
Source: Bhatt--Scholze, Lemmas 6.8.12--6.8.13 and Proposition 6.8.14(2).
(blueprint: lem-weil-pbc-continuous-constructible-integral-single)

Proof in words. On each of the finitely many constructible strata, identify local finite
presentations over the continuous E coefficient sheaf with finite-rank local systems.
Lemma 6.8.13 supplies a constructible integral lattice on that stratum. Refine the
stratification to a finite filtration by closed subsets, and use the open--closed exact
sequences to reconstruct the sheaf from the extensions by zero of its restrictions.
These exact extension functors preserve integral constructibility. To lift an extension
between two integral models, Lemma 6.8.12 identifies its rational Ext1 group with the
localization of integral Ext1. Multiply the extension class by a power of ℓ to lift it;
that scalar is invertible over E, so the new extension rationalizes to the original one.
Induction through the finite filtration gives a constructible integral sheaf whose
rationalization is the given module. Place it in degree zero. Exactness of coefficient
localization identifies this with derived integralScalarExtension. The compact profinite
continuous-function localization calculation, pulled back from the point, identifies the
coefficient map with the actual one used here. The zero sheaf and empty scheme use zero.
-/
theorem continuousConstructible_integral_single_model (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hF : ProEtale.IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj E) X) F) :
    ∃ M : integralConstructible ℓ E X,
      Nonempty ((integralScalarExtension ℓ E X).obj M.obj ≅
        (DerivedCategory.singleFunctor _ 0).obj F) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
