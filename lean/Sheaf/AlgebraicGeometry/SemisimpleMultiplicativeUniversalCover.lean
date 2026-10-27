module

public import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple
public import Sheaf.AlgebraicGeometry.FiniteDiagonalizableGroupScheme
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Sheaf.AlgebraicGeometry.StandardGroupSchemes
import Sheaf.AlgebraicGeometry.SemisimpleCharactersTrivial
import Sheaf.AlgebraicGeometry.CharacterPicardIsogenySequence
import Sheaf.AlgebraicGeometry.ConnectedGroupCharactersTorsionFree
import Sheaf.AlgebraicGeometry.SemisimpleCentralIsogenyMultiplicative
import Sheaf.AlgebraicGeometry.MultiplicativeIsogenyComposition
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # Multiplicative universal covers of semisimple algebraic groups

Source: Milne, Algebraic Groups (2017), Theorem 18.25 and Remark 18.27, printed p.393;
Definitions 18.5 and 18.7, printed pp.388--389; Lemma 19.14 and Proposition 19.15,
printed pp.400--401 (blueprint: lem-sfb-semisimple-multiplicative-universal-cover).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonObj

namespace AlgebraicGeometry

/-- A semisimple group admits a semisimple simply connected cover by a faithfully flat
homomorphism with finite diagonalizable central kernel. Simple connectedness is stated
as the universal condition on surjective homomorphisms with finite central kernel.
Centrality is tested on every scheme over the field, retaining infinitesimal points.

Source: Milne, Algebraic Groups (2017), Theorem 18.25 and Remark 18.27, printed p.393;
Definitions 18.5 and 18.7, printed pp.388--389; Lemma 19.14 and Proposition 19.15,
printed pp.400--401 (blueprint: lem-sfb-semisimple-multiplicative-universal-cover).

Proof plan:
1. Apply lem-sfb-picard-trivial-multiplicative-cover to H, obtaining P with Pic(P) = 0
   and a multiplicative isogeny pi : P → H. By lem-sfb-semisimple-isogeny-invariance,
   P is semisimple. Put N = ker pi.
2. Write N = D(M) for a finite abelian M. A character corresponds to a group-like
   element of F[M]. By lem-sfb-group-algebra-group-like-basis these are exactly its
   basis elements, so X*(N) is M and is finite. The affine spectrum correspondence
   def-weil-affine-spectrum and the multiplicative group def-sc-gm-ga identify the
   character and group-like descriptions, including for nonreduced N.
3. By lem-sfb-semisimple-characters-trivial, X*(H) = 0. Exactness of
   lem-sfb-character-picard-isogeny-sequence injects X*(P) into the finite X*(N).
   By lem-sfb-connected-group-characters-torsion-free its source is torsion free,
   hence X*(P) = 0 as well as Pic(P) = 0.
4. Let q : Q → P be a surjective homomorphism from semisimple Q with finite central
   kernel K. By lem-sfb-semisimple-central-isogeny-multiplicative, q is faithfully
   flat with finite diagonalizable kernel. Apply lem-sfb-character-picard-isogeny-sequence:
   X*(Q) is X*(K) since X*(P) = Pic(P) = 0. The former is torsion free by
   lem-sfb-connected-group-characters-torsion-free and the latter is finite by step 2.
   Thus X*(K) = 0; writing K = D(M_K), step 2 gives M_K = 0 and K = 1 as a scheme.
5. On every test algebra, Q ×[P] Q → Q is an isomorphism: its inverse is the diagonal,
   since q(y) = q(x) implies yx⁻¹ lies in K = 1. These formulas are natural and give
   inverse scheme maps. The morphism q is flat and surjective by step 4 and
   quasi-compact since it is between affine schemes. Apply
   lem-weil-pbc-fpqc-descend-isomorphism to descend this isomorphism along q.
   Hence q is an isomorphism, giving the asserted simple connectedness of P.
6. The identity of H is a multiplicative isogeny with trivial kernel D(0). Apply
   lem-sfb-multiplicative-isogeny-composition to pi and this identity to obtain
   centrality of ker pi. Take Htilde = P. The trivial group is allowed throughout,
   and no reducedness assumption on finite kernels or characteristic restriction occurs.
-/
theorem exists_semisimple_multiplicative_universalCover
    {F : Type u} [Field F] [IsAlgClosed F]
    (H : Over (Spec (.of F))) [GrpObj H] (hH : IsSemisimpleGroupScheme H) :
    ∃ (Htilde : Over (Spec (.of F))) (_ : GrpObj Htilde),
      IsSemisimpleGroupScheme Htilde ∧
      (∀ (H1 : Over (Spec (.of F))) [GrpObj H1],
        IsSemisimpleGroupScheme H1 → ∀ (q : H1 ⟶ Htilde) [IsMonHom q],
          Surjective q.left → IsFinite (GrpObj.ker q).hom →
          (∀ (T : Over (Spec (.of F))) (x : T ⟶ GrpObj.ker q) (g : T ⟶ H1),
            (x ≫ GrpObj.kerι q) * g = g * (x ≫ GrpObj.kerι q)) → IsIso q) ∧
      ∃ (pi : Htilde ⟶ H) (_ : IsMonHom pi),
        pi.left.appTop.hom.FaithfullyFlat ∧ IsFinite (GrpObj.ker pi).hom ∧
        IsFiniteDiagonalizableGroupScheme (GrpObj.ker pi) ∧
        ∀ (T : Over (Spec (.of F))) (x : T ⟶ GrpObj.ker pi) (g : T ⟶ Htilde),
          (x ≫ GrpObj.kerι pi) * g = g * (x ≫ GrpObj.kerι pi) := by
  sorry

end AlgebraicGeometry
