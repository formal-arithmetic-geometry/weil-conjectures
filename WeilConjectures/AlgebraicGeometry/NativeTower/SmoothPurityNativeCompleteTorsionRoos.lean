/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeTower.SmoothPurityNativeTowerLimitData
public import WeilConjectures.AlgebraicGeometry.NativeTower.SmoothPurityNativeEllRegular
public import WeilConjectures.CategoryTheory.RingedPowerTorsion.RingedPowerTorsionLimitModels

/-! # Native completeness and the principal ell-completion unit

Source: current blueprint sk-lem-sp-tower, first paragraph and native completion step 2.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.NativeTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- A native complete object is a strict Roos limit of raw ell-power-torsion rows.
The rows retain their actual finite quotient module actions before any replacement.
Source: current blueprint sk-lem-sp-tower, native completion step 2; Bhatt--Scholze
3.5.7; Stacks 0940
(blueprint: lem-sp-native-complete-torsion-roos).

Proof: use equality of the continuous integer-ring presentations and the supplied
heterogeneous equality to represent K by a native uniformizer-complete complex.
Choose its K-flat representative P with invertible quotient-Roos augmentation.
Take the actual strict uniformizer quotients of P and transfer these raw rows
through the exact internal/section module equivalence. Its product comparison and
its signed cone comparison identify their strict Roos complex with the image of the
native quotient-Roos complex. Invertibility of the specified native augmentation
therefore gives the stated isomorphism from the section image of K.
Row j is termwise killed by pi^(j+1). The coefficient factorization ell=u*pi^e,
e positive, makes ell^(j+1) a multiple of pi^(j+1), proving the displayed zero map
on the unchanged raw row. No K-flat replacement of the rows is taken.
The same construction applies to zero complexes, empty schemes, ramified
extensions and unbounded complexes. -/
theorem complete_torsion_roos (K : Integral l E T) (hK : Complete l E T K) :
    ∃ U : CochainComplex (ℕᵒᵖ ⥤ spIntegralSectionModules l E T) ℤ,
        (∀ (n : ℕ) (a : ℤ),
          endoPow ((SheafOfModules.RegularQuotientCone.scalar
            (spIntegralSectionRing l E T) (ellSection l E T)).app
              ((U.asFunctor.obj (Opposite.op n)).X a)) (n + 1) = 0) ∧
        Nonempty (((sectionEquivalence l E T).functor.obj K) ≅
          DerivedCategory.Q.obj (roosF.obj U)) := by
  sorry

end AlgebraicGeometry.ProEtale.NativeTower
