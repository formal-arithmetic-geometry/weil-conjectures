/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OpenCoefficientDirectImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull

/-!
# Direct image along an open immersion

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/sec-ladic-summary/sk-prop-open-coefficients/_section.md,
node sk-prop-open-coefficients, order 355; Stacks Project Tags 099L and 09A6.
(blueprint: sk-prop-open-coefficients)

The statement uses the existing condensed coefficient sheaves and the total derived
module-object pushforward. The field hypothesis is written explicitly as the finite-or-
algebraically-closed convention, so characteristic-zero algebraically closed fields remain
included.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Direct image along a quasi-compact open immersion preserves bounded constructibility
for the integral, finite-extension, and algebraic-closure coefficient sheaves.

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/sec-ladic-summary/sk-prop-open-coefficients/_section.md,
node sk-prop-open-coefficients, order 355; Stacks Project Tags 099L and 09A6.
The proof is the integral criterion and open-finiteness argument, followed by integral-model
cone and shift generators, coefficient-change comparisons, and triangulated closure
(blueprint: sk-prop-open-coefficients).
-/
theorem constantModelBoundedConstructible_open_coefficient_direct_image_stage2
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (_hbase : Finite k ∨ IsAlgClosed k)
    (_hchar : ringChar k ≠ ℓ)
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {U X : Scheme.{u}} [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j] [QuasiCompact j] :
    (∀ K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) U)),
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) U K →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X
        ((CondensedRing.moduleObjectDerivedPushforward
          (Profinite.padicIntegersRingObj ℓ E.val) j).obj K)) ∧
    (∀ K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E) U)),
      constantModelBoundedConstructible (Profinite.continuousMapRingObj E) U K →
      constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X
        ((CondensedRing.moduleObjectDerivedPushforward
          (Profinite.continuousMapRingObj E) j).obj K)) ∧
    (∀ K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) U)),
      constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) U K →
      constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X
        ((CondensedRing.moduleObjectDerivedPushforward
          (Profinite.padicAlgClRingObj ℓ) j).obj K)) := by
  let : Fact (Finite k ∨ IsAlgClosed k) := ⟨_hbase⟩
  let : Fact (ringChar k ≠ ℓ) := ⟨_hchar⟩
  exact constantModelBoundedConstructible_open_coefficient_direct_image ℓ k E j

end AlgebraicGeometry.ProEtale
