/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.DirectImageConeTowerNormalizationDefs

/-! # Derived normalization of the strict direct-image cone comparison -/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.CompleteDerivedCompletion

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesDerived AdicCompletion.finiteRingMonoidalObject
  AdicCompletion.finiteRingCommutative AdicCompletion.finiteModulesDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The summand-normalized strict comparison has the canonical K-injective
right-derived normalization.
Source: literature/blueprint/latest/blueprint/sec-proper-base-change/
sk-prop-pbc-complete/prop-weil-pbc-direct-image-limits.proof.md, proof (2).
(blueprint: lem-weil-pbc-direct-image-cone-tower-k-injective-normalization).

Proof in words: write L ⊣ R for module pullback/direct image and L_T ⊣ R_T
for the induced tower adjunction. At the complex level transpose e.inv
under L_T ⊣ R_T. Compose with the reduction of the module-adjunction unit.
The cone summand equations for e and strictPullReduction identify this
transpose with the canonical strict pullback/reduction comparison: on each
summand the assertion is the ordinary adjunction triangle identity and the
scalar coefficient square. Biprod extensionality proves the complex identity.
Localize it using redFactors. IsPullReduction identifies the localized strict
pullback map with the chosen pullReduction. The canonical derived adjunction
has unit characterized by the localization of the ordinary unit followed by
the right-derived unit; this is the derived adjunction unit factorization.
Apply that factorization to the module and tower adjunctions, and naturality
of rightDerivedFunctorUnitQ to the strict cone map. The mate unit identity
then yields exactly the displayed equation. On a K-injective I the module
right-derived unit is the inverse of the canonical K-injective comparison.
The tower unit is retained as a morphism: no K-injectivity of strictRed(I)
and no invertibility of its tower right-derived unit is needed. This also
covers zero I, empty schemes and unbounded complexes. -/
theorem strictDirectImageConeTower_normalized
    (e : strictRed l E X ⋙ (push l E f).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      Functor.mapHomologicalComplex
        (CondensedRing.lowerStar (DerivedNakayama.integerRing l E) f)
          (ComplexShape.up ℤ) ⋙ strictRed l E Y)
    (he : IsStrictDirectImageConeTower l E f e) :
    IsKInjectiveDirectImageNormalization l E f e := by
  sorry


end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
