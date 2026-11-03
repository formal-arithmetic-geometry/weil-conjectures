/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

import WeilConjectures.AlgebraicGeometry.CondensedFourierTransform
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NoetherianStalk
import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreierProjectorFacts
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Affine-line lisse irreducibility and upper weights

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-fourier-transform/sec-wft-perverse/sk-lem-wft-curve-heart/
rem-dl-a1-conventions.md (blueprint: rem-dl-a1-conventions).
The finite field, geometric fibre, Weil modules, lissity, purity and ordinary middle
image are the imported definitions; the two predicates below give the conventions
used in the boundary-sequence assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeL2

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- Nonzero lisse Weil sheaves have no proper nonzero lisse Weil subobject.
The subobject quantifier is in Weil modules, and its source is required to be lisse.
Source: rem-dl-a1-conventions.md, irreducible-lisse paragraph
(blueprint: rem-dl-a1-conventions). -/
def IsIrreducibleLisse (M : WeilModule D l X₀) : Prop :=
  IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left M.carrier ∧
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier ∧
    ¬ IsZero M ∧
    ∀ (N : WeilModule D l X₀) (f : N ⟶ M),
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) N.carrier →
        Mono f → IsZero N ∨ IsIso f

/-- The upper-weight convention uses every closed point, every geometric lift, and
all eigenvalues of the actual local geometric Frobenius.
Source: rem-dl-a1-conventions.md, upper-bound sentence
(blueprint: rem-dl-a1-conventions). -/
def HasWeightsAtMost (M : WeilModule D l X₀) (iota : PadicAlgCl l →+* ℂ)
    (w : ℝ) : Prop :=
  ∀ (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    (α : ULift.{u + 1} (PadicAlgCl l)),
    Module.End.HasEigenvalue (closedOperator D l X₀ M x i hi).hom α →
      ‖iota α.down‖ ^ 2 ≤ (Nat.card (X₀.left.residueField x.val) : ℝ) ^ w

end WeilConjectures.NativeL2
