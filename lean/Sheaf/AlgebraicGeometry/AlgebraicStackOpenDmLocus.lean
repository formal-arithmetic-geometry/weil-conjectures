module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack

/-! # The largest open with unramified relative diagonal

Source: Stacks Project, stacks-morphisms.tex, Tag 0DSM (lemma-open-DM-locus),
DM part; Tag 050N(1) identifies the absolute and relative-base conventions
(blueprint: lem-sfb-algebraic-stack-open-dm-locus).

The conclusion uses the existing full open-substack and relative-diagonal notions.
No quasi-compactness, nonemptiness, or restriction on the base is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry

namespace CategoryTheory

/-- Every algebraic stack has a largest full open substack with unramified
relative diagonal over the original base scheme.
Source: Stacks Project, stacks-morphisms.tex, Tag 0DSM (lemma-open-DM-locus),
DM part, with Tag 050N(1) for the relative diagonal convention
(blueprint: lem-sfb-algebraic-stack-open-dm-locus).

Proof:
1. By lem-sfb-open-substack-unions, choose a set of representatives of all opens
whose relative diagonal is unramified, and form their algebraic open union U.
For every scheme T mapping to U, their pullbacks T_i form an open covering of T.
2. By lem-sfb-unramified-diagonal-etale-atlas, each such open U_i has a
representable surjective etale scheme atlas W_i -> U_i.
3. Form W = coproduct_i W_i using lem-weil-pbc-scheme-coproduct-family.
Stack descent glues the objects over the disjoint open summands to W -> U.
Representability follows by base changing the algebraic-space diagonal of U.
4. On any scheme test T -> U and etale chart P of W x_U T, the inverse images
P_i of the summands W_i cover P. Fullness identifies the corresponding open part
with W_i x_{U_i} T_i. Thus P_i -> T_i is etale. Its composite with T_i -> T is
etale by lem-weil-pbc-etale-composition-cancellation. By
lem-weil-pbc-etale-local-on-source, P -> T is etale.
5. The T_i cover T, and each W_i x_{U_i} T_i -> T_i is surjective. These are
open parts of W x_U T, so W x_U T -> T is surjective on all scheme tests.
6. The reverse direction of lem-sfb-unramified-diagonal-etale-atlas now gives
unramified relative diagonal for U. The empty index family gives the empty
union and the empty atlas, with the same vacuous scheme tests.
7. Every other open V with unramified relative diagonal is represented in the
chosen family, hence is contained in U. Containment of full substacks is
invariant under equivalence over the ambient stack. -/
theorem exists_largest_open_unramified_moduli_diagonal {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S))
    (hstack : IsModuliStack F) (hdiag : HasAlgebraicSpaceDiagonal F)
    (hatlas : ∃ (U : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj U)) F),
      ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) F),
        ∃ (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
          HasSpaceBaseChange a T t Z p ∧ SpaceMapIsSurjective Z T p ∧
          ∀ (V : Over S) (b : yoneda.obj V ⟶ Z.obj.obj), AlgebraicSpace.IsEtale b →
            AlgebraicGeometry.Smooth ((yoneda.preimage (b ≫ p)).left)) :
    ∃ U : OpenModuliSubstack F, HasUnramifiedModuliDiagonal U.category ∧
      ∀ V : OpenModuliSubstack F,
        HasUnramifiedModuliDiagonal V.category → V.IsContainedIn U := by
  sorry

end CategoryTheory
