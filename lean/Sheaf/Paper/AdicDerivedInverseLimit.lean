/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.Paper.CompleteCoefficientDatum
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Adic derived inverse limits with a chosen Roos triangle

Source: literature/blueprint/master/blueprint/sec-proper-base-change/
sk-thm-properbasechange/def-weil-pbc-adic-derived-inverse-limit.md, order 1256;
Stacks Project, Derived Categories, Tags 08TC and 0H9J
(blueprint: def-weil-pbc-adic-derived-inverse-limit).

## Main definitions

- `adicReductionSequence`: the scalar-restricted reductions, indexed from zero.
- `adicReductionStep`: the quotient-induced successive transition maps.
- `adicReductionTower`: the resulting inverse system.
- `AdicDerivedInverseLimit`: an object and chosen maps forming its Roos triangle.

The model parameter uses the recorded coefficient construction. Every derived object
admits such a model by `adicKFlatModel_exists`; no boundedness condition is imposed.
No derived-limit object, morphism between triples, or functor is selected.
-/

@[expose] public section

universe t

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The reductions of K, with scalars restricted to Λ, reindexed by n ↦ n + 1.
The quotient-coefficient version is `adicReduction`; this uses its underlying object.
Source: blueprint order 1256, reduction tower
(blueprint: def-weil-pbc-adic-derived-inverse-limit). -/
noncomputable def adicReductionSequence (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (n : ℕ) : proEtaleDerivedCategory X Λ :=
  adicReductionUnderlying X d M ⟨n + 1, Nat.succ_pos n⟩

/-- The transition from reduction modulo I^(n+2) to reduction modulo I^(n+1), induced
by the quotient ring map, in the original coefficient derived category.
Source: blueprint order 1256, reduction tower
(blueprint: def-weil-pbc-adic-derived-inverse-limit). -/
noncomputable def adicReductionStep (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (n : ℕ) :
    adicReductionSequence X d M (n + 1) ⟶ adicReductionSequence X d M n :=
  adicTransition X d M ⟨(n + 1) + 1, Nat.succ_pos (n + 1)⟩
    ⟨n + 1, Nat.succ_pos n⟩ (Nat.le_succ (n + 1))

/-- The reduction tower as an inverse-system functor. Its successive arrows are exactly
`adicReductionStep`; longer arrows are their composites.
Source: blueprint order 1256, reduction tower; Stacks Tag 08TC
(blueprint: def-weil-pbc-adic-derived-inverse-limit). -/
noncomputable def adicReductionTower (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) : ℕᵒᵖ ⥤ proEtaleDerivedCategory X Λ :=
  Functor.ofOpSequence (adicReductionStep X d M)

/-- A chosen adic derived inverse limit is a triple (obj, p, δ) whose triangle
obj → ∏ K_n → ∏ K_n → obj[1] is distinguished, with middle arrow 1 minus the
product shift induced by the quotient transitions. The generic predicate includes
exactly this condition. Only the product of this reduction sequence is assumed to exist.
Source: blueprint order 1256; Stacks Tags 08TC and 0H9J
(blueprint: def-weil-pbc-adic-derived-inverse-limit). -/
structure AdicDerivedInverseLimit (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) [HasProduct (adicReductionSequence X d M)] where
  obj : proEtaleDerivedCategory X Λ
  p : obj ⟶ ∏ᶜ (adicReductionSequence X d M)
  δ : ∏ᶜ (adicReductionSequence X d M) ⟶ obj⟦(1 : ℤ)⟧
  distinguished : IsDerivedLimitTriangle (adicReductionStep X d M) obj p δ

end AlgebraicGeometry.Scheme
