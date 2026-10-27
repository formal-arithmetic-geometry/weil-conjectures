module

public import Sheaf.AlgebraicGeometry.AffineGroupFrobeniusVerschiebung
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.GroupTheory.Finiteness
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Naturality of Verschiebung and diagonalizable groups

Source: Milne, Algebraic Groups (2017), Definition 11.39(a)–(c), pp. 224–225,
and Chapter 12(b), pp. 231–232
(blueprint: lem-sfb-verschiebung-naturality-diagonalizable).

The statements use the coordinate construction of the recorded dependency. Since Spec is
fully faithful on affine schemes, coordinate equalities express the scheme equalities.
The twist comparisons are specified on all pure tensors, including their scalar factors.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace AlgebraicGeometry.AffineGroupFrobeniusVerschiebung

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The coordinate function of the canonical Verschiebung: invariant projection after
iterated coproduct. This uses exactly the existing construction, without choosing a map.
Source: Milne, Definition 11.39, p. 224
(blueprint: lem-sfb-verschiebung-naturality-diagonalizable). -/
noncomputable def verschiebungCoordinate (C : Type u) [CommRing C] [HopfAlgebra k C] :
    C →ₗ[k] twist k p C :=
  (projection k p C).comp (iteratedComul k C p)

variable (G H : Scheme.{u})
  [G.Over (Spec (.of k))] [H.Over (Spec (.of k))] [IsAffine G] [IsAffine H]
  [GrpObj (G.asOver (Spec (.of k)))] [GrpObj (H.asOver (Spec (.of k)))]
  [gComm : IsCommMonObj (G.asOver (Spec (.of k)))]
  [hComm : IsCommMonObj (H.asOver (Spec (.of k)))]
  [gft : LocallyOfFiniteType (G ↘ Spec (.of k))]
  [gqc : QuasiCompact (G ↘ Spec (.of k))]
  [hft : LocallyOfFiniteType (H ↘ Spec (.of k))]
  [hqc : QuasiCompact (H ↘ Spec (.of k))]
include gComm hComm gft gqc hft hqc in
/-- Naturality: `f V_G = V_H f^(p)`, written contravariantly on coordinates.
The twist map is fixed by its values on every pure tensor.
Source: Milne, Definition 11.39(a), p. 224
(blueprint: lem-sfb-verschiebung-naturality-diagonalizable).

Proof: step 1 of the node pulls multiplication compatibility back to
Delta_G f* = (f* tensor f*) Delta_H. Iterate to p factors, then use the naturality
of the invariant projection (lem-sfb-symmetric-invariant-frobenius-projection).
The construction in lem-sfb-affine-group-frobenius-verschiebung gives the equality
below. The tensor pushout gives the specified twist map. Fully faithful Spec
reverses the equality to the claimed group homomorphism identity. -/
theorem verschiebung_naturality
    (f : G.asOver (Spec (.of k)) ⟶ H.asOver (Spec (.of k))) [IsMonHom f] :
    ∃ ft : twist k p Γ(H, ⊤) →+* twist k p Γ(G, ⊤),
      (∀ (a : Γ(H, ⊤)) (b : k),
        ft (pure k p Γ(H, ⊤) a b) = pure k p Γ(G, ⊤) (f.left.appTop a) b) ∧
      (∀ a : Γ(H, ⊤),
        ft (verschiebungCoordinate k p Γ(H, ⊤) a) =
          verschiebungCoordinate k p Γ(G, ⊤) (f.left.appTop a)) := by
  sorry
include gComm gft gqc in
/-- Formation of V commutes with every field extension. The scalar factor a is raised
only in the twist comparison; no inverse of Frobenius is used.
Source: Milne, Definition 11.39(c), p. 225
(blueprint: lem-sfb-verschiebung-naturality-diagonalizable).

Proof: steps 2–3 identify the twist of K tensor C with K tensor the twist of C
by (a tensor c) tensor b mapping to (a^p b) tensor (c tensor 1).
The inverse sends a tensor (c tensor d) to (1 tensor c) tensor (a d).
Extend a k-basis of C to K. This identifies the orbit-sum bases of invariant
p-fold tensors. On constant orbits both projections give the same first-factor
generator, and on nonconstant orbits both give zero. Base-changed coproducts
are scalar extensions of the original ones, giving the second displayed formula.
Use lem-sfb-affine-group-frobenius-verschiebung and the tensor pushout correspondence. -/
theorem verschiebung_baseChange
    (K : Type u) [Field K] [Algebra k K] [CharP K p] :
    ∃ θ : twist K p (K ⊗[k] Γ(G, ⊤)) ≃ₐ[K] K ⊗[k] twist k p Γ(G, ⊤),
      (∀ (a b : K) (c : Γ(G, ⊤)),
        θ (pure K p (K ⊗[k] Γ(G, ⊤)) (a ⊗ₜ[k] c) b) =
          (a ^ p * b) ⊗ₜ[k] first k p Γ(G, ⊤) c) ∧
      (∀ (a : K) (c : Γ(G, ⊤)),
        θ (verschiebungCoordinate K p (K ⊗[k] Γ(G, ⊤)) (a ⊗ₜ[k] c)) =
          a ⊗ₜ[k] verschiebungCoordinate k p Γ(G, ⊤) c) := by
  sorry
include gComm hComm gft gqc hft hqc in
/-- Binary products: after the canonical twist identification V is the product of the
factor Verschiebungs. Together with `verschiebung_emptyProduct`, this gives all finite products.
Source: Milne, Definition 11.39(b), p. 225
(blueprint: lem-sfb-verschiebung-naturality-diagonalizable).

Proof: step 4 identifies coordinate rings of products with tensor products by
lem-weil-pbc-algebra-tensor-pushout-universal-property. The displayed pure-tensor
formula specifies the twist comparison. Apply step 1 to each projection; their
components characterize the product map. Iterate to every nonempty finite product. -/
theorem verschiebung_product :
    ∃ θ : twist k p (Γ(G, ⊤) ⊗[k] Γ(H, ⊤)) ≃ₐ[k]
        twist k p Γ(G, ⊤) ⊗[k] twist k p Γ(H, ⊤),
      (∀ (a : Γ(G, ⊤)) (b : Γ(H, ⊤)) (c : k),
        θ (pure k p (Γ(G, ⊤) ⊗[k] Γ(H, ⊤)) (a ⊗ₜ[k] b) c) =
          pure k p Γ(G, ⊤) a 1 ⊗ₜ[k] pure k p Γ(H, ⊤) b c) ∧
      (∀ (a : Γ(G, ⊤)) (b : Γ(H, ⊤)),
        θ (verschiebungCoordinate k p (Γ(G, ⊤) ⊗[k] Γ(H, ⊤)) (a ⊗ₜ[k] b)) =
          verschiebungCoordinate k p Γ(G, ⊤) a ⊗ₜ[k]
            verschiebungCoordinate k p Γ(H, ⊤) b) := by
  sorry
/-- The empty product is the trivial group, whose V is its unique map.
Source: Milne, Definition 11.39(b), p. 225
(blueprint: lem-sfb-verschiebung-naturality-diagonalizable).

Proof: the last case of step 4 uses the terminal group. On its coordinate algebra k,
the unique k-algebra map into its twist is the scalar structure map. -/
theorem verschiebung_emptyProduct (a : k) :
    verschiebungCoordinate k p k a = pure k p k 1 a := by
  sorry
include gComm hComm gft gqc hft hqc in
/-- If V_G is zero, V_N is zero for each closed subgroup N. The coordinate map of the
zero group homomorphism is the scalar structure map composed with the counit.
Source: Milne, Definition 11.39(a), p. 224, and Chapter 5
(blueprint: lem-sfb-verschiebung-naturality-diagonalizable).

Proof: step 5 applies naturality to the inclusion N = H into G. Both composites
with the inclusion are zero. IsSubgroupScheme gives injectivity on every algebra-valued
point. Evaluate at the coordinate ring of N^(p) and its universal point to recover
V_N = 0 by the affine spectrum correspondence; field-valued points alone do not suffice. -/
theorem verschiebung_closedSubgroup
    (i : H.asOver (Spec (.of k)) ⟶ G.asOver (Spec (.of k)))
    [IsClosedSubgroupScheme i]
    (hG : ∀ a : Γ(G, ⊤), verschiebungCoordinate k p Γ(G, ⊤) a =
      algebraMap k (twist k p Γ(G, ⊤)) (Coalgebra.counit (R := k) a)) :
    ∀ a : Γ(H, ⊤), verschiebungCoordinate k p Γ(H, ⊤) a =
      algebraMap k (twist k p Γ(H, ⊤)) (Coalgebra.counit (R := k) a) := by
  sorry
include gComm hComm gft gqc hft hqc in
/-- Vanishing descends along faithfully flat finitely presented quotient homomorphisms.
For affine schemes these are precisely the stated conditions on the coordinate ring map.
Source: Milne, Definition 11.39(a), p. 224, and Chapter 5
(blueprint: lem-sfb-verschiebung-naturality-diagonalizable).

Proof: step 6 writes u = q*. Its twist is the base change of u along the
first-factor inclusion of the quotient coordinate ring into its twist. Thus
lem-weil-pbc-faithfully-flat-base-change makes u^(p) faithfully flat, and
lem-weil-pbc-faithfully-flat-universally-injective makes it injective. Naturality
and hG give u^(p) v_Q = u^(p) zero*. Cancel this injection and use faithful Spec.
Finite presentation records the represented fppf quotient convention. -/
theorem verschiebung_quotient
    (q : G.asOver (Spec (.of k)) ⟶ H.asOver (Spec (.of k))) [IsMonHom q]
    (hflat : q.left.appTop.hom.FaithfullyFlat)
    (hfp : q.left.appTop.hom.FinitePresentation)
    (hG : ∀ a : Γ(G, ⊤), verschiebungCoordinate k p Γ(G, ⊤) a =
      algebraMap k (twist k p Γ(G, ⊤)) (Coalgebra.counit (R := k) a)) :
    ∀ a : Γ(H, ⊤), verschiebungCoordinate k p Γ(H, ⊤) a =
      algebraMap k (twist k p Γ(H, ⊤)) (Coalgebra.counit (R := k) a) := by
  sorry
/-- For D_k(M), V is an isomorphism with coordinate formula e_m ↦ e_m tensor 1.
Source: Milne, Definition 11.39 and Chapter 12(b), pp. 224, 231–232
(blueprint: lem-sfb-verschiebung-naturality-diagonalizable).

Proof: step 7 uses Delta_p(e_m) = e_m tensor ... tensor e_m and the singleton-orbit
formula of lem-sfb-affine-group-frobenius-verschiebung. The inverse sends
(sum a_m e_m) tensor c to sum a_m^p c e_m. Finite support makes this an actual
sum, Frobenius additivity gives additivity and multiplicativity, and the twist
balancing relation proves well-definedness. Check both composites on pure tensors
and basis vectors. The affine spectrum correspondence reverses this algebra
isomorphism to the claimed group scheme isomorphism. This allows p-torsion in M. -/
theorem verschiebung_diagonalizable
    (M : Type u) [AddCommGroup M] [AddGroup.FG M] :
    ∃ v : AddMonoidAlgebra k M ≃ₐ[k] twist k p (AddMonoidAlgebra k M),
      (∀ a : AddMonoidAlgebra k M,
        v a = verschiebungCoordinate k p (AddMonoidAlgebra k M) a) ∧
      (∀ m : M, v (AddMonoidAlgebra.single m 1) =
        first k p (AddMonoidAlgebra k M) (AddMonoidAlgebra.single m 1)) := by
  sorry

end AlgebraicGeometry.AffineGroupFrobeniusVerschiebung
