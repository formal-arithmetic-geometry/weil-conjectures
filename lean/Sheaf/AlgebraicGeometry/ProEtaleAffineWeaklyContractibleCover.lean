/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
import Sheaf.RingTheory.IndEtaleStability
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Affine weakly contractible covering families on the small pro-etale site

Source: Stacks Project, proetale.tex, Tags 0990 and 098I; sites.tex, Tags 090L and 090K
(blueprint: lem-weil-pbc-proetale-affine-wcontractible-covering-family).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- Every object of the small pro-etale site has a covering family of affine objects
weakly contractible for sheaves on the full small site of `X`.
Source: Stacks Project, Tags 0990, 098I, 090L and 090K
(blueprint: lem-weil-pbc-proetale-affine-wcontractible-covering-family).

Proof for stage 3:
1. Cover `U` by arbitrary affine opens `T_j = Spec A_j`, using the affine basis of a
   scheme (def-pc-scheme). No finiteness of this cover is required.
2. For each `A_j`, choose an infinite small cardinal bounding its size. Apply
   lem-weil-pbc-wcontractible-ring-extension to get an ind-etale faithfully flat
   extension `A_j → D_j` with splitting property, explicit cardinal bound, and
   a singleton pro-etale cover `Spec D_j → T_j`.
3. By def-weil-size-convention, closure under power sets and function sets makes
   the cardinal bound small. The spectrum is small too (def-weil-affine-spectrum).
   Replace by representatives in the chosen skeleton, conjugating the arrows.
4. Open immersions are etale (lem-weil-pbc-open-immersion-etale), hence flat, and
   have isomorphic diagonals (def-weil-open-immersion, def-weil-etale-morphism).
   They are weakly etale (def-weil-weakly-etale-morphism). Composition stability
   (lem-weil-pbc-ind-etale-stability) makes `Spec D_j → X` full-site objects.
5. For each affine open `W` of `U`, refine its intersections with the `T_j` by
   affine opens inside `W`. Affine quasi-compactness (lem-weil-pbc-affine-scheme-qcqs)
   selects finitely many. The singleton covering clause of the ring-extension lemma
   supplies finitely many affine opens upstairs with images exactly these opens.
   Their images cover exactly `W`, proving def-weil-pbc-proetale-covering. For empty
   `W`, take no witnesses.
6. The splitting property and full-site membership allow
   lem-weil-pbc-wcontractible-affine-weakly-contractible to give surjectivity on
   every full-site sheaf epimorphism. This proves the claim for arbitrary `U`;
   the empty object admits the empty family.
-/
theorem exists_affine_weaklyContractible_covering_family
    (X : Scheme.{u}) (U : X.ProEt) :
    ∃ (I : Type (u + 1)) (V : I → X.ProEt) (f : ∀ i : I, V i ⟶ U),
      Presieve.ofArrows V f ∈ precoverage X U ∧
      (∀ i : I, IsAffine (V i).left) ∧
      (∀ (i : I) (F G : Sheaf (topology X) (Type (u + 1))) (e : F ⟶ G),
        Epi e → Function.Surjective (e.hom.app (op (V i)))) := by
  sorry

end AlgebraicGeometry.Scheme.ProEt
