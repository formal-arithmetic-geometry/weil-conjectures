/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Sheaf.Paper.AdicRealizationFamilyData

/-! # Tensor reindexing on the ambient K-flat models

Source: Bhatt--Scholze, Remark 6.8.15; Hemo--Richarz--Scholbach, Lemma 7.9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime]

/-- Scheme-isomorphism reindexing carries the specified ambient tensor models to each other.
Source: BS Remark 6.8.15; Stacks 07A4; the K-flat part of lem-sf-adic-reindexing-core
(blueprint: lem-sf-adic-tensor-reindexing-models).

Proof: The sectionwise site equivalence and the coefficient isomorphism B give an exact
monoidal equivalence of ordinary module categories. Its tensor comparison sends a pure
tensor of sections to the same tensor at the reindexed object. Extend this comparison
by the coproduct injections in each total degree; additivity preserves the differential,
including its Koszul sign. The inverse sectionwise comparison gives the inverse total
map. The exact monoidal equivalence preserves acyclic complexes and all tensor tests
for K-flatness. Thus the total comparison descends through the two supplied K-flat model
presentations A.models and C.models. The descended comparison satisfies precisely their
representative equation, by naturality of the exact-derived factorization. Finally the
coefficient isomorphism gives the map of degree-zero coefficient-unit complexes, and its
section formula is the B formula. This argument concerns the ambient module categories
and does not use or assert compatibility with common-stage realization. -/
theorem exists_tensor_reindexing_models {X Y : Scheme.{u}} (g : X ≅ Y)
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : At l X R) (C : At l Y S) (B : RingReindex l X g.hom R S) :
    Nonempty (ReindexTensor l X g.hom A C B) := by
  sorry

end WeilConjectures.AdicQbarRealization
