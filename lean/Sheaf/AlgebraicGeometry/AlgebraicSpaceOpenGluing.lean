/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q64
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
import Sheaf.AlgebraicGeometry.FppfAffineRefinement
import Sheaf.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability

/-!
# Gluing algebraic spaces along open subfunctors

Source: Stacks Project, Spaces, Tag 02WR (blueprint: lem-trf-algebraic-space-open-gluing).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A sheaf covered by algebraic-space open subfunctors is an algebraic space.

Source: Stacks Project, Spaces, Tag 02WR, lemma-glueing-algebraic-spaces
(blueprint: lem-trf-algebraic-space-open-gluing).

Proof: representable maps are sheaves for the fppf topology by affine refinement and
fpqc representable descent.  The sheaf coproduct of the open algebraic subspaces is
locally represented by one summand, so its pullback to every scheme test is represented
by the coproduct of the corresponding open subschemes and is surjective.  Pullbacks of
two scheme tests are covered by representable open pieces coming from the summands;
the scheme representability criterion gives representability of the diagonal.  The
coproduct map is therefore representable, étale, and surjective.  Composing it with
a representable surjective étale atlas of the algebraic-space coproduct gives such an
atlas for the target sheaf, proving the conclusion by the definition of algebraic space.
The proof uses the statement dependencies `def-pc-scheme`, `def-pc-fppf-site`,
`def-weil-pbc-sheafification`, `def-trf-algebraic-space`, `def-pc-subfunctor`, and
`def-weil-open-immersion`; its proof dependencies are recorded in the DAG node. -/
theorem algebraicSpace_of_open_gluing {S : Scheme.{u}}
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u)) (I : Type w)
    (Fi : I → Sheaf (Scheme.fppfTopology.over S) (Type u))
    (H : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (j : ∀ i : I, (Fi i) ⟶ H)
    (hcol : IsColimit (Cofan.mk H j))
    (ι : ∀ i : I, (Fi i) ⟶ F)
    (q : H ⟶ F)
    (hfac : ∀ i : I, j i ≫ q = ι i)
    (hmono : ∀ i : I, Mono (ι i))
    (hFi : ∀ i : I, AlgebraicSpace.IsAlgebraicSpace (Fi i))
    (hopen : ∀ i : I,
      AlgebraicSpace.IsRepresentableWith
        (fun _ _ p ↦ IsOpenImmersion p.left) (ι i).hom)
    (hq : Epi q)
    (hcop : AlgebraicSpace.IsAlgebraicSpace H) :
    AlgebraicSpace.IsAlgebraicSpace F := by
  sorry

end AlgebraicGeometry
