/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q8
-/
module

public import Sheaf.SixFunctors.IntegralDualizingMappingTower

/-! # Natural scalar comparison on the entire input derived category -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The scalar Hom comparison for a prescribed quotient-system complex is natural
on the entire completed-coefficient derived category, before constructible restriction.

Source: blueprint prop-coef-integral-dualizing, second paragraph, first mapping
comparison; Stacks 07A6, 08J9 and 0941.
(blueprint: lem-coef-hom-scalar-naturality).

Proof: apply the sequence-site derived extension--restriction internal-Hom
adjunction to the constant completed input and Q. The constant-sequence
section-preserving equivalence identifies restriction on the sequence site with
the inverse realization of coefficientSequenceDerivedRestriction. The normalized
reduction adjunction identifies derived extension of the constant input with
S.reduction: both are left adjoint to the same total derived limit, and the
unique adjunction comparison carries their units to one another. Substitute this
natural comparison in the contravariant argument of internal Hom. The ordinary
scalar-section square and its derived comparison identify constant-ring sections
of restricted quotient Hom with coefPairingSections of quotient Hom, retaining
the actual R action and the full tower index. Compose these natural isomorphisms.
Naturality is inherited from the bifunctorial scalar internal-Hom comparison,
the adjunction comparison, and the derived section square; it is not inferred
from finite evaluations or from unrelated objectwise isomorphisms. No inverse
limit of Hom towers or exceptional adjunction is used. All comparisons apply to
zero complexes and to the empty scheme. -/
theorem coefHom_scalar_naturality
    (Q : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (S : CoefficientDerivedSystemCalculus l E X) :
    Nonempty (
      (coefHomDerivedConstant l E X).op ⋙
        (Functor.curry.obj (coefHomConstantInternalHom l E X)).flip.obj
          ((coefHomEquivalence l E X).inverse.mapDerivedCategory.obj
            ((coefficientSequenceDerivedRestriction l E X).obj (coefTraceInput l E X Q))) ⋙
        coefHomConstantDerivedSections l E X ≅ coefPairingHom l E X S Q) := by sorry

end WeilConjectures
