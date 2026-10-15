/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Sheaf.RingTheory.IndPrincipalZariski
import Sheaf.RingTheory.IndEtaleStability
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Weakly contractible covers in the affine ind-etale basis

Source: Stacks Project, proetale.tex, Tag 0990, affine `S_app` clause;
sites.tex, Tags 090L and 090K (2)
(blueprint: lem-weil-pbc-ind-etale-basis-wcontractible-cover).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.AffineProEt

/-- Every object of the affine ind-etale basis of an affine scheme admits a covering
by objects that are weakly contractible in this same basis site.
Source: Stacks Project, Tag 0990, affine `S_app` clause, and Tags 090L, 090K (2)
(blueprint: lem-weil-pbc-ind-etale-basis-wcontractible-cover).

Proof for stage 3:
1. Write `U = Spec A`. Choose the bounded faithfully flat ind-etale extension `A → D`
   of lem-weil-pbc-wcontractible-ring-extension. Its spectrum `V` covers `U`.
   By lem-weil-pbc-ind-etale-stability its composite to `S` is ind-etale, so `V`
   lies in the affine basis. The size bound keeps it in the object universe
   (def-weil-size-convention); this singleton is an induced basis covering.
2. For an epimorphism `P → Q` and a section in `Q(V)`, use
   lem-weil-pbc-site-sheaf-sets-epi-locally-surjective to find local lifts on a
   basis covering `T_i → V`. Its underlying scheme family is a pro-etale covering.
   The retraction property of `D` and lem-weil-pbc-wcontractible-cover-section
   give a section `V → ∐ T_i` of its covering map. The coproduct need not be affine.
3. By lem-weil-pbc-scheme-coproduct-family the inverse images `O_i` of the
   components form a disjoint open covering of `V`. Their inclusions are weakly
   etale, by lem-weil-pbc-open-immersion-etale and
   lem-weil-pbc-weakly-etale-composition-base-change. Quasi-compactness of affine
   test opens makes this a pro-etale covering; the opens need not lie in the basis.
4. Apply lem-weil-pbc-ind-etale-basis to refine this covering by finitely many
   basis objects `W_k → V`, each factoring through an `O_i`. Composing with
   `O_i → T_i` pulls the local lifts back to sections of `P(W_k)`.
5. The same basis lemma supplies basis fibre products for the overlaps. Those
   over different disjoint opens are empty; a sheaf has a unique section on the
   empty scheme, since the empty family covers it. Over the same open, the two
   maps to `T_i` agree by uniqueness of factorization through an open immersion.
   Hence the pulled-back sections agree on overlaps and glue to a section of `P(V)`.
   Naturality and sheaf separatedness show that it maps to the chosen section of
   `Q(V)`. This also treats empty `U`, using the empty refinement and unique section.
-/
theorem exists_weaklyContractible_cover (S : Scheme.{u}) [IsAffine S]
    (U : S.AffineProEt) :
    ∃ (I : Type (u + 1)) (V : I → S.AffineProEt) (f : ∀ i, V i ⟶ U),
      Presieve.ofArrows V f ∈ precoverage (S := S) U ∧
      ∀ (i : I) (P Q : Sheaf (topology S) (Type (u + 1))) (φ : P ⟶ Q),
        Epi φ → Function.Surjective (φ.hom.app (op (V i))) := by
  sorry

end AlgebraicGeometry.Scheme.AffineProEt
