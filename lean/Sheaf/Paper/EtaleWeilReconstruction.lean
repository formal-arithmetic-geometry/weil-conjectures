/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P6
-/
module

public import Sheaf.Paper.EtaleWeilRealization

/-! # Reconstruction of etale Weil descent from a Weil representation

Source: Weil II (1.1.12); step 6 of the etale Weil equivalence.
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

/-- Every l-adic Weil representation is realized by an etale lisse sheaf with descent.
Source: Weil II (1.1.6), (1.1.12); step 6 of
prop-wf-weil-sheaf-representation-equivalence.
(blueprint: new-p6-etale-weil-reconstruction)

Proof: restrict V to the geometric group using D.geom and use the algebraic
coefficient clause of cor-galois-lisse-representations to choose its underlying
lisse sheaf F and a geometric equivariant identification of its fibre with V.
The finite evaluation normalization identifies this action with the actual
etaleGeometricRep: compare on germs, then limit projections and scalar tensors.
Put T = rho(s). The finite path conjugation rule in D, extended through the
same three coefficient stages, says L rho_pull(g) = rho(s^-1 g s) L, with
L the inverse of the path used by etaleWeilFrobenius. Thus T L intertwines
the geometric action on h^*F with that on F. Fullness of the underlying lisse
dictionary lifts T L to a sheaf map h^*F to F, and lifts its inverse as well.
Faithfulness gives the two inverse identities, providing the descent isomorphism.
By construction its degree-one operator is T. Uniqueness in
etaleFundamentalRep_exists identifies its action with rho on the whole group:
the actions agree on geometric elements and on s, and every w is a s^n.
The chosen fibre identification therefore yields the asserted representation
isomorphism. Zero representations reconstruct the zero sheaf by the same argument;
no stable integral lattice for T, nor a preferred finite coefficient model of T,
is imposed. This result is only essential surjectivity, independently of the
Hom dictionary or the exact and tensor structures. -/
theorem etaleWeilReconstruction [ConnectedSpace Y]
    (V : etaleLisseWeilRepresentations l Q h t d D) :
    ∃ F : EtaleLisseWeilSheaf l Q h,
      Nonempty ((etaleWeilRealization l Q h t d D).obj F ≅ V) := by sorry

end AlgebraicGeometry.Scheme
