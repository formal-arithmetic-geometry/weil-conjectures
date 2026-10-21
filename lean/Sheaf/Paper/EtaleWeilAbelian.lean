/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P6
-/
module

public import Sheaf.Paper.EtaleWeilFundamentalRepresentation
import Sheaf.Paper.LisseAutomorphismEquivalence
import Sheaf.Paper.GaloisLisseRepresentations
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.EndoFunctor

/-! # Abelian operations on actual etale Weil sheaves

Source: Weil II (1.1.12), step 7 of the etale Weil equivalence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
open FiniteEtale

variable (l : ℕ) [Fact l.Prime] (Q : Type (u + 1)) [Field Q]
  [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
  {Y : Scheme.{u}} [IsNoetherian Y] [Y.IsSeparated]
  [∀ x : Y, Invertible (l : Y.residueField x)]
  (h : Y ≅ Y) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (t : Spec (.of Ω) ⟶ Y) {G : Type v} [Group G]
  (d : Monodromy.DegreeDatum G) (D : EtaleWeilDegreeData h t G d)

include t in
/-- Kernels and cokernels of etale Weil morphisms carry their induced descent.
Source: Weil II (1.1.12); step 7 of
prop-wf-weil-sheaf-representation-equivalence.
(blueprint: new-p6-etale-weil-abelian)

Proof: the algebraic coefficient clause of cor-galois-lisse-representations
makes the underlying lisse category abelian. Reindexing by h has inverse
reindexing by h^-1 at finite levels, and both commute with scalar extension
and the coefficient localization. Consequently h^* is an additive equivalence
and preserves kernels and cokernels. For a Weil morphism u, its descent square
induces h^*ker(u) to ker(u); applying the inverse descent squares gives the
inverse map by uniqueness in the kernel universal property. The same construction
on cokernels gives inverse descent there. Their universal maps and factorizations
satisfy the descent squares by the uniqueness of underlying factorizations.
The zero object and binary biproducts have componentwise descent. The underlying
coimage-to-image comparison is a Weil morphism by uniqueness and is invertible
because it is so in the lisse category. This gives the abelian structure by the
standard coimage-to-image criterion, including all zero-object cases. Equivalently,
apply IsoAlgebra.abelian to the exact additive reindexing endofunctor. -/
theorem etaleWeilAbelian [ConnectedSpace Y] :
    Nonempty (Abelian (EtaleLisseWeilSheaf l Q h)) := by
  obtain ⟨P, act, hP⟩ := exists_isFundamentalGroup t
  let := act
  let := hP
  obtain ⟨c, hc⟩ := galois_lisse_representations t P
  obtain ⟨a⟩ := hc l Q
  obtain ⟨aL⟩ := a.algebraicSheavesAbelian
  let : Abelian (LisseAlgebraicSheaf l Y Q) := aL
  let : (lisseAlgebraicAutomorphismPullback h l Q).IsEquivalence :=
    lisseAlgebraicAutomorphismPullback_isEquivalence l Q h
  let : (lisseAlgebraicAutomorphismPullback h l Q).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact ⟨inferInstance⟩

end AlgebraicGeometry.Scheme
