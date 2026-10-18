module

public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver

import Mathlib.CategoryTheory.Sites.Limits
import Sheaf.CategoryTheory.SiteCoveringAxioms

/-!
# Effective descent for sheaves of sets on a covering

Source: Stacks Project, `sites.tex`, Tags 04TR and 04TQ
(blueprint: lem-pe-set-sheaf-cover-descent).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Effective descent and unique gluing for sheaves of sets along a covering.

Source: Stacks Project, `sites.tex`, Tags 04TR and 04TQ
(blueprint: lem-pe-set-sheaf-cover-descent).

The sheaves on the slice sites form the pseudofunctor
`GrothendieckTopology.pseudofunctorOver`.  Its descent-data category for the
covering family consists of sheaves `F_a` on the slices, overlap isomorphisms
`φ_ab`, and the triple-overlap cocycle.  The asserted equivalence says exactly
that such data is induced by a sheaf `F` on `C/U`, with isomorphisms
`e_a : F|_{U_a} ≅ F_a` satisfying `e_b = φ_ab ≫ e_a` on overlaps.  Full
faithfulness of the same equivalence is the final assertion: compatible local
maps between two sheaves glue to one and only one global map.

Proof: construct the compatible-tuples sheaf by the sectionwise equalizer of
products, verify the local graph maps are inverse isomorphisms using the
cocycle, and glue compatible morphisms by the sheaf equalizer axiom, as in
Tags 04TR and 04TQ. More precisely: (1) base-change the local sheaves to
the slices over `U` and verify that the resulting component presheaves are
sheaves; (2) take the sectionwise limit of their products and equalize the
two overlap maps, obtaining the compatible-tuples sheaf; (3) restrict the
cocycle to the triple diagonal and cancel the resulting automorphism to get
the diagonal normalization; (4) define the local comparison maps by pulling
back along graph sections, and define their inverses from the cocycle; (5)
check both inverse identities and naturality, hence obtain the local
isomorphisms; (6) pull the tuple equations back along the double-overlap
graph to obtain `e_b = φ_ab ≫ e_a`; (7) for compatible local morphisms,
amalgamate their values using the sheaf equalizer axiom and prove
naturality by separatedness; (8) prove restriction and uniqueness by the
same equalizer axiom. The component-sheaf and equalizer steps use
`def-weil-pbc-sites-and-cohomology`, `def-pur-localized-ringed-site`,
`def-weil-size-convention`, and
`lem-weil-pbc-site-sheaf-sets-limits-sectionwise`. -/
theorem setSheafCoverDescent
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    (J : GrothendieckTopology C)
    {I : Type (max u v)} (U : C) (X : I → C)
    (f : ∀ i, X i ⟶ U)
    (hcov : Sieve.ofArrows X f ∈ J U) :
    (∀ D : (J.pseudofunctorOver (Type (max u v))).DescentData f,
      ∃ F : Sheaf (J.over U) (Type (max u v)),
        Nonempty (D ≅
          ((J.pseudofunctorOver (Type (max u v))).toDescentData f).obj F)) ∧
      Nonempty (((J.pseudofunctorOver (Type (max u v))).toDescentData f).FullyFaithful) := by
  sorry

end CategoryTheory
