module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Abelian
import WeilConjectures.Topology.AbelianSheafShortExactStalkwise
import Mathlib.Topology.ShrinkingLemma
import Mathlib.Order.Zorn

/-!
# Lifting sections along closed subsets through a soft kernel

Source: Demailly, Complex Analytic and Differential Geometry, IV §4.B, Definition (4.9)
and Proposition (4.14), printed pp.204–205
(blueprint: lem-sfb-soft-kernel-closed-sections).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace TopCat.Sheaf

/-- Source: Demailly, Complex Analytic and Differential Geometry, IV §4.B,
Definition (4.9) and Proposition (4.14), printed pp.204–205
(blueprint: lem-sfb-soft-kernel-closed-sections).

Softness is written using the inverse-image adjunction unit at the top open, exactly
as in `lem-sfb-soft-abelian-sheaf-acyclic`. Pullback to the closed subspace is inverse
image, whose sections are locally represented families of ambient germs.

Proof:
1. Fix a closed subset S and a section c of C along S. For the empty subset its unique
   section lifts. Otherwise stalkwise short exactness
   (`lem-sc-abelian-sheaf-short-exact-stalkwise`) gives local ambient lifts near each
   point of S: represent a preimage germ, then shrink until its image agrees with a
   representative of c. No surjectivity on arbitrary open sections is asserted.
2. Add X minus S to these opens and take a locally finite open refinement U_i of X.
   Choose local lifts on its members meeting S; use zero on members assigned to
   X minus S. The point-finite shrinking lemma
   (`lem-sfb-paracompact-point-finite-shrinking`) gives opens V_i covering X with
   closure V_i contained in U_i. The sets D_i = S intersect closure V_i are a locally
   finite closed cover of S, carrying lifts b_i of c.
3. Every subfamily union of a locally finite closed family is closed. Compatible
   sections along that family paste: near each point only finitely many members
   occur; avoid those not containing the point and shrink the representatives of
   the others until they agree. The sheaf axiom of
   `def-weil-pbc-sites-and-cohomology` gives the resulting locally represented germs.
4. Order partial lifts (J,b) on the union of D_i for i in J by extension. The empty
   lift exists. For a chain, restrict its comparable members to each D_i and use
   step 3 to paste an upper bound. Encode each partial lift by its index markers
   and germ graph in a subset of I disjoint-union the stalks of B along S.
   `lem-weil-pbc-zorn-lemma` gives a maximal partial lift.
5. To add an omitted D_i, the difference of the partial lift and b_i on their closed
   intersection lies in the kernel of p. Stalkwise exactness gives unique preimages
   in A. Represent them locally; uniqueness makes these representatives a section
   along the intersection. Softness of A extends it globally. Correct b_i by its
   image in B and paste with the partial lift using step 3, contradicting maximality.
6. Thus the maximal lift is defined along all of S. This gives surjectivity for every
   closed S, including S = X.
7. If B is soft, first lift c along S to B by step 6, extend that lift globally using
   softness of B, and apply p. Naturality of restriction gives a global extension
   of c, proving softness of C.
-/
theorem surjective_closedSections_and_soft_of_soft_kernel
    {X : TopCat.{u}} [ParacompactSpace X] [T2Space X]
    (K : ShortComplex (X.Sheaf AddCommGrpCat.{u})) (hK : K.ShortExact)
    (hA : ∀ (S : Set X), IsClosed S →
      Function.Surjective
        (((pullbackPushforwardAdjunction AddCommGrpCat.{u}
          (TopCat.ofHom ⟨(Subtype.val : S → X), continuous_subtype_val⟩)).unit.app K.X₁).hom.app
            (op (⊤ : Opens X)))) :
    (∀ (S : Set X), IsClosed S →
      Function.Surjective
        (((pullback AddCommGrpCat.{u}
          (TopCat.ofHom ⟨(Subtype.val : S → X), continuous_subtype_val⟩)).map K.g).hom.app
            (op (⊤ : Opens S)))) ∧
    ((∀ (S : Set X), IsClosed S →
      Function.Surjective
        (((pullbackPushforwardAdjunction AddCommGrpCat.{u}
          (TopCat.ofHom ⟨(Subtype.val : S → X), continuous_subtype_val⟩)).unit.app K.X₂).hom.app
            (op (⊤ : Opens X)))) →
      ∀ (S : Set X), IsClosed S →
        Function.Surjective
          (((pullbackPushforwardAdjunction AddCommGrpCat.{u}
            (TopCat.ofHom ⟨(Subtype.val : S → X), continuous_subtype_val⟩)).unit.app K.X₃).hom.app
              (op (⊤ : Opens X)))) := by
  sorry

end TopCat.Sheaf
