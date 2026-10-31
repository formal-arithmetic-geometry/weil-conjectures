/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleExceptionalOriginTransfer
import WeilConjectures.AlgebraicGeometry.ProEtaleResidueComparison

/-! The zero-object half of finite-ring residue conservativity on the pro-etale site.
(blueprint: lem-sf-proetale-residues-zero-characterization)

The missing proof is the cone/zero specialization of the comparison argument: transport a
classical pro-etale object to an etale origin, apply etale residue conservativity, and reflect
the resulting zero object through the comparison. The statement is kept separate so the main
conservativity theorem only combines this zero criterion with the independent stalk-perfectness
criterion.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- Residue tensors detect zero classical pro-etale objects.

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-lem-sf-kunneth-star/
sk-lem-sf-kunneth-star.proof.md, cone and zero specialization
(blueprint: lem-sf-proetale-residues-zero-characterization).

Proof: the forward implication follows by functoriality of derived tensor. For the reverse,
choose the bounded-below etale origin, apply the residue comparison helper to the zero
endomorphism, and use etale residue conservativity to show that the origin is zero. Comparison
of the origin with the given object then reflects zero through the isomorphism. The argument
also covers the zero ring and empty scheme. -/
theorem proEtale_residues_zero_iff
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    (C : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)))
    (_hC : exceptionalTransportProEtaleObjects A S C)
    (_hclassicalC : ∃ E : Etale.DerivedCategoryModule A S,
      _root_.DerivedCategory.TStructure.t.plus E ∧
        Nonempty ((comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.obj E ≅ C)) :
    IsZero C ↔ ∀ m : Ideal A, m.IsMaximal →
      IsZero (((derivedTensor (ModuleCat.{u + 1} A) S).obj C).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)).obj
            (ModuleCat.of A (A ⧸ m))))) := by
  sorry

end AlgebraicGeometry.ProEtale
