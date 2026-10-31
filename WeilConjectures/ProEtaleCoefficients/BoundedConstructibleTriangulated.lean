/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.FiniteDiscreteCoefficientTriangulated

/-!
# Bounded constructible complexes form a triangulated subcategory

Source: `literature/blueprint/slopmaster2-20261029-2300/blueprint/sec-proetale-coefficients/`
`sk-prop-sf-open-closed-triangle/prop-sfb-bounded-constructible-triangulated.md`,
node `prop-sfb-bounded-constructible-triangulated`, order 1195.
(blueprint: prop-sfb-bounded-constructible-triangulated)

The four coefficient cases of the node, for the pulled-back ring object
`Λ_X = condensedRingObj Λ X` with its canonical commutative ring-object structure
(`Profinite.isCommMonObj_continuousMapRingObj`, `Profinite.isCommMonObj_padicIntegersRingObj`,
`Profinite.isCommMonObj_padicAlgClRingObj`, transported along the monoidal `p_X^*` by the
scoped instance of `CategoryTheory.Obj` and `isCommMonObj_condensedRingObj`):
`E̲` for a finite normed extension `E` of `ℚ_ℓ`, `𝒪̲_E`, `ℚ̲̄_ℓ` (continuous maps into finite
subextensions) and `T̲` for a finite discrete ring `T` killed by a power of `ℓ`.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

set_option linter.unusedVariables false in
/-- For a noetherian scheme, bounded constructible complexes are triangulated for each
allowed coefficient ring: a finite extension field, its ring of integers, the algebraic closure,
or a finite discrete ring killed by a power of the fixed prime. The ring objects carry their
canonical commutative ring-object structures.

Source: the current blueprint, `prop-sfb-bounded-constructible-triangulated`, order 1195.

Proof: each of the four clauses, its parameters introduced, is an instance of the library,
found by typeclass inference. Each instance is the weak-Serre argument of the blueprint proof:
the constructible modules (`IsConstructibleModuleObject`) contain `0`, are stable under
isomorphisms, and are closed under kernels, cokernels and extensions, so by Stacks 06UQ
(lem-sbc-cohomology-in-weak-serre-subcategory) the bounded complexes with constructible
cohomology form a triangulated subcategory.
1. `E̲`, `𝒪̲_E`, `ℚ̲̄_ℓ`: the instances `isTriangulated_boundedConstructible_continuousMapRingObj`,
   `_padicIntegersRingObj`, `_padicAlgClRingObj`
   (lem-sfb-bounded-constructible-triangulated-finiteness), with the closures from
   lem-weil-pbc-condensed-constructible-serre and lem-weil-pbc-integral-constructible-serre.
2. `T̲`: the instance `isTriangulated_boundedConstructible_finiteDiscreteRingObj`, with kernels by
   lem-sfb-finite-discrete-internal-constructible-kernels and cokernels and extensions by
   lem-weil-pbc-constructible-cokernels-extensions; the hypothesis `ℓ ^ n T = 0` is not needed.
(blueprint: prop-sfb-bounded-constructible-triangulated) -/
theorem isTriangulated_boundedConstructible
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] :
    (∀ (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
      [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
      [Algebra E (PadicAlgCl ℓ)] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)],
      (boundedConstructible
        (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X)).IsTriangulated) ∧
    (∀ (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E]
      [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
      [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E],
      (boundedConstructible
        (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) X)).IsTriangulated) ∧
    (∀ (ℓ : ℕ) [Fact ℓ.Prime],
      (boundedConstructible
        (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X)).IsTriangulated) ∧
    (∀ (ℓ : ℕ) [Fact ℓ.Prime] (T : Type) [CommRing T] [TopologicalSpace T]
      [IsTopologicalRing T] [DiscreteTopology T] [Finite T]
      (hT : ∃ n : ℕ, ∀ t : T, (ℓ : T) ^ n * t = 0),
      (boundedConstructible
        (condensedRingObj (Profinite.continuousMapRingObj.{u} T) X)).IsTriangulated) := by
  constructor
  · intro ℓ instℓ E _ _ _ _ _
    infer_instance
  constructor
  · intro ℓ instℓ E _ _ _ _ _
    infer_instance
  constructor
  · intro ℓ instℓ
    infer_instance
  · intro ℓ instℓ T _ _ _ _ _ _
    infer_instance

end AlgebraicGeometry.ProEtale
