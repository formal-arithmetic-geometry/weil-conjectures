/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory

/-!
# An affine weakly contractible singleton cover

Source: Stacks Project, proetale.tex, Tag 0F4P, last sentence; sites.tex, Tags 090K, 090L
(blueprint: lem-weil-pbc-proetale-qc-affine-contractible-cover).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- Every quasi-compact object has a singleton pro-etale covering by an affine object
weakly contractible in the full site. Source: Stacks Project, Tag 0F4P, last sentence,
and Tags 090K (2), 090L
(blueprint: lem-weil-pbc-proetale-qc-affine-contractible-cover).

Proof for stage 3:
1. Use lem-weil-pbc-proetale-affine-wcontractible-covering-family to cover `T` by
   affine objects weakly contractible in the full site.
2. Choose a finite affine open cover of `T`. For each member, the affine-open
   witnesses in def-weil-pbc-proetale-covering involve only finitely many covering
   indices. Retain their union. The witnesses restrict to principal opens and then
   to arbitrary affine opens; composition and refinement in def-weil-pbc-proetale-site
   show that the retained finite subfamily still covers. For empty `T`, retain no indices.
3. Take the finite disjoint union `V` of this family. By
   lem-weil-pbc-proetale-qcqs-finite-family-geometry it is an affine object of the site.
   The induced map to `T` is weakly etale: flatness is checked on each summand, and
   the diagonal is flat on equal-summand pieces and empty on distinct-summand pieces
   (def-weil-weakly-etale-morphism). The same affine-open witnesses establish the
   singleton covering criterion of def-weil-pbc-proetale-covering.
4. The finite-family geometry lemma identifies sheaf evaluation at `V` naturally
   with the product of evaluations at the summands. For any epimorphism of sheaves,
   choose a preimage in each factor by weak contractibility. This proves surjectivity
   at `V`. Empty products are singletons, so the argument also covers empty `T`. -/
theorem exists_affine_weaklyContractible_cover (X : Scheme.{u}) (T : X.ProEt)
    [CompactSpace T.left] :
    ∃ (V : X.ProEt) (f : V ⟶ T),
      Presieve.singleton f ∈ precoverage X T ∧
      IsAffine V.left ∧
      ∀ (F G : Sheaf (topology X) (Type (u + 1))) (η : F ⟶ G),
        Epi η → Function.Surjective (η.hom.app (op V)) := by
  sorry

end AlgebraicGeometry.Scheme.ProEt
