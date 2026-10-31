/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.WeilMixedUpperBounds
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Canonical immersion cohomology

Source: blueprint restriction argument for open--closed reduction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Qbar : Type v) [Field Qbar] [Algebra (Padic l) Qbar]
  [IsAlgClosure (Padic l) Qbar]
  (W₀ X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom] [IsSeparated W₀.hom]
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]

/-- Cohomology compatibility for the specified canonical immersion
pullback, with the normalized Frobenius square used by the weight predicates.
The assertion has no embedding, purity, mixedness or weight hypothesis.

Source: blueprint restriction paragraph of lem-zl-morphism-open-closed-reduction;
lem-zl-immersion-weil-local-behavior(1), Bhatt--Scholze 6.8.11(3), 6.8.14--6.8.15,
and BBD 1.3.3 for the truncation comparisons.
(blueprint: lem-zl-canonical-immersion-cohomology).

Proof: the actual common-stage inverse image preserves both standard halves by
constructible_pullback_t_exact. Its induced Weil structure is zlFrobeniusSquare,
formed from the localized integral composition comparisons.
The canonical cohomology comparison is the composite of the upper and lower
truncation comparisons and the prescribed shift comparison. Truncation-unit and
counit uniqueness makes these comparisons natural for the Frobenius square;
shift compatibility follows at integral representatives from signed reindexing,
and descends through rationalization and common finite coefficient enlargement.
Consequently the comparison is a Weil isomorphism for sfWeilCohomologyFrobenius,
not only an underlying isomorphism. Lift it through the fully faithful heart
inclusion to obtain the stated iso. All finite diagrams descend over a common
finite coefficient field, so no equality of scheme and coefficient universes is
needed. For identity and empty immersions the same construction applies. -/
theorem zlCanonicalImmersionCohomology (h₀ : W₀ ⟶ X₀) [IsImmersion h₀.left] :
    ∀ (a : ℤ) (K : sfCommonStageWeilComplex D l hl X₀ Qbar),
      Nonempty
        (((sfWeilCohomology D l hl Qbar W₀ a).obj
          ((IsoAlgebra.mapOfNatIso (zlFrobeniusSquare D l hl Qbar h₀)).obj K)) ≅
          (zlWeilPull D l hl Qbar h₀).obj ((sfWeilCohomology D l hl Qbar X₀ a).obj K)) := by
  sorry

end WeilConjectures
