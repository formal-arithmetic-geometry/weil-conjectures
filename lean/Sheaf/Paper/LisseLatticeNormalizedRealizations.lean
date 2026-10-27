/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U9
-/
module

public import Sheaf.Paper.LisseLatticeHeartLiftData

/-! # Normalized completed and rational presentations with the balanced tensor restriction. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme TensorProduct
namespace WeilConjectures.LisseLattice
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Normalized completed and rational presentations with the balanced tensor restriction.
Source: Bhatt--Scholze, Lemma 6.8.2 and Remark 6.8.15.

Proof: identify the completed constant quotient tower with continuous integral functions.
The identification is fixed by every residue projection, so the constant uniformizer maps
to the continuous constant uniformizer. The universal property of sheafified localization
then identifies rationalRing with continuous rational functions and identifies the units.
Exact scalar localization induces J on the full integral constructible subcategory:
on objects use derived extension and on a pure tensor a tensor f use a times F(f).
The balanced tensor relation and a common denominator prove that this descends to the
raw rationalization. The integral factorization and fraction formula follow on generators.
For an etale map, inverse image is slice restriction. Associativity of extension of
scalars gives the balance isomorphism. On a pulled-back pure tensor it sends b tensor n
to the pulled-back b tensor the pulled-back n, giving balance_sections. Construct these
maps for every scheme; neither noetherianity nor constructibility is used in this scalar
construction. Inverse identities follow from the localization and tensor universal
properties, rather than choices of arbitrary equivalences.
(blueprint: lem-tw-lisse-lattice-normalized-realizations). -/
theorem normalized_realizations : Nonempty (Realizations l E) := by sorry

end WeilConjectures.LisseLattice
