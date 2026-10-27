module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Order.Zorn

/-! # Maximal homogeneous ideals and graded-field quotients

Source: Stacks Project, Algebra, Tag 00JM (section-proj), homogeneous-ideal convention;
the independent abelian-group-graded Zorn argument retained in the Q112 report
`lem-sfb-graded-stabilizer-strong-products`, "Complete proof retained for the new node".
(blueprint: lem-sfb-homogeneous-maximal-graded-field-quotient)
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Ideal

/-- A proper homogeneous ideal lies in a maximal proper homogeneous ideal, and its quotient
has the image grading and inverses in opposite degrees for all nonzero homogeneous elements.
Source: Stacks Project, Algebra, Tag 00JM (section-proj), componentwise homogeneity;
the independent argument retained in the Q112 report, "Complete proof retained for the new node".
(blueprint: lem-sfb-homogeneous-maximal-graded-field-quotient)

Proof: consider the proper homogeneous ideals containing L. This family contains L. The union
of a nonempty chain is an ideal because any two elements lie in a common member. Each component
of an element lies in that same member, so the union is homogeneous. It is proper because
membership of 1 would put 1 in one proper member. The empty chain has upper bound L.
Apply Zorn's lemma [lem-weil-pbc-zorn-lemma] to obtain H. Every proper homogeneous ideal above H
also contains L, so maximality in this family gives maximality among all such ideals.
Form the quotient q : A → A/H [def-weil-pbc-algebra-hom-quotient]. The image subgroups span by
surjectivity of q. If a finite sum of homogeneous lifts maps to zero, the sum lies in H;
homogeneity puts each lift in H, proving uniqueness of the quotient expansion. The unit and
products have the required degrees by lifting them to A. Properness of H makes A/H nonzero.
For nonzero d in degree n choose a lift a in A_n outside H. The ideal H+(a) is homogeneous:
the degree-r component of h+ax is h_r+a x_(r-n), since translation by n is injective in the
grading group. It strictly contains H and hence is the whole ring. Write 1=h+ax. Its degree-zero
component is 1=h_0+a x_(-n), where h_0 lies in H. Applying q gives d q(x_(-n))=1, and this inverse
belongs to the degree-(-n) image subgroup. -/
theorem exists_homogeneous_maximal_gradedField_quotient
    {M : Type u} [AddCommGroup M] [DecidableEq M] {A : Type v} [CommRing A]
    (𝒜 : M → AddSubgroup A) [GradedRing 𝒜]
    (L : Ideal A) (hL : L.IsHomogeneous 𝒜) (hL_proper : L ≠ ⊤) :
    ∃ H : Ideal A,
      L ≤ H ∧ H ≠ ⊤ ∧ H.IsHomogeneous 𝒜 ∧
      (∀ J : Ideal A, H ≤ J → J ≠ ⊤ → J.IsHomogeneous 𝒜 → J = H) ∧
      Nontrivial (A ⧸ H) ∧
      Nonempty (GradedRing (fun n : M ↦ (𝒜 n).map (Ideal.Quotient.mk H).toAddMonoidHom)) ∧
      ∀ (n : M) (d : A ⧸ H),
        d ∈ (𝒜 n).map (Ideal.Quotient.mk H).toAddMonoidHom → d ≠ 0 →
        ∃ e : A ⧸ H,
          e ∈ (𝒜 (-n)).map (Ideal.Quotient.mk H).toAddMonoidHom ∧ d * e = 1 := by
  sorry

end Ideal
