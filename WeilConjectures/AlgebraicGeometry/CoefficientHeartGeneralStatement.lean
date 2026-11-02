/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartFiltration
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSmall
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Extensions

/-!
# Constructible coefficient sheaves over a general field

Source: blueprint latest,
`part-six-operations/sec-reduction-finite-coefficients/`
`sec-constructible-sheaves-with-field-coefficients/sk-lem-coefficient-heart/_section.md`,
and `sk-lem-coefficient-heart.proof.md`, clauses (1)--(3), with the standing
field hypothesis `char(k) ≠ ℓ` (blueprint: sk-lem-coefficient-heart).

This file states the current coefficient-heart lemma. The coefficient ring is either a
finite extension inside the algebraic closure of `ℚ_ℓ` or the finite-subextension-valued
condensed algebraic closure. The proof is postponed; its route is the three clauses of the
blueprint: closure and exactness, essential smallness, and finite locally closed lisse
filtrations.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Constructible coefficient sheaves over any field of characteristic different from `ℓ`
form an exact essentially small abelian heart and admit finite filtrations by canonical
locally closed extensions of lisse sheaves.

Source: blueprint latest,
`part-six-operations/sec-reduction-finite-coefficients/`
`sec-constructible-sheaves-with-field-coefficients/sk-lem-coefficient-heart/_section.md`,
clauses (1)--(3), and
`sk-lem-coefficient-heart.proof.md`, steps (1)--(3)
(blueprint: sk-lem-coefficient-heart).

Proof plan, following the node's eight steps:
1. Finite type over k makes X Noetherian. Finite scalar presentations are finite free;
   choose common adapted strata and use exact restriction to check closure on strata.
2. For extensions, trivialize the ends and locally lift the quotient basis. The resulting
   local splitting identifies the middle term with a finite free direct sum.
3. Over E use the lattice atlas on connected affine etale neighborhoods. The qcqs
   finitely presented Hom/filtered-colimit calculation clears one common denominator.
4. Recover the lattices as limits of their finite reductions. The connected pro-etale
   tower identifies the map with its completed-fibre matrix, whose kernel and cokernel
   become finite free after inverting the uniformizer and choosing linear algebra bases.
5. Over Qbar_l descend the two lisse objects and their map to a finite E. Flat scalar
   extension preserves kernels, and the left adjoint preserves cokernels. Return to strata.
6. Zero has rank zero and extensions give finite sums. Closure under ambient kernels and
   cokernels gives the abelian full subcategory and its exact inclusion.
7. In the fixed universe encode finite stratifications and finite-rank descent/gluing
   data by a set of representatives, giving essential smallness.
8. Refine to ordered open prefixes. Their open-extension counit images form a filtration
   from zero to F, with quotients the canonical locally closed extensions of lisse
   restrictions. Repeated terms, rank zero and empty schemes are allowed.
-/
theorem coefficientHeartGeneralStatement (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj L)]
    (hL : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ L = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      L = Profinite.padicAlgClCondensedRing ℓ)
    (k : Type u) [Field k] (hchar : ringChar k ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] :
    ObjectProperty.IsClosedUnderKernels
        (IsConstantModelConstructible (coefficientHeartRingObj L) X) ∧
      ObjectProperty.IsClosedUnderCokernels
        (IsConstantModelConstructible (coefficientHeartRingObj L) X) ∧
      ObjectProperty.IsClosedUnderExtensions
        (IsConstantModelConstructible (coefficientHeartRingObj L) X) ∧
      Nonempty (Abelian (ConstantModelConstructible (coefficientHeartRingObj L) X)) ∧
      PreservesFiniteLimits
        (ObjectProperty.ι (IsConstantModelConstructible
          (coefficientHeartRingObj L) X)) ∧
      PreservesFiniteColimits
        (ObjectProperty.ι (IsConstantModelConstructible
          (coefficientHeartRingObj L) X)) ∧
      EssentiallySmall.{u + 1} (ConstantModelConstructible (coefficientHeartRingObj L) X) ∧
      @CoefficientHeartFiltrationAssertions (coefficientHeartRingObj L) _ _ X
        { toIsLocallyNoetherian :=
            LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
          toCompactSpace :=
            QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k)) } := by
  sorry

end AlgebraicGeometry.ProEtale
