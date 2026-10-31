/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.PresheafBarResolutionData
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Existence of the augmented presheaf bar resolution

Source: Stacks Project, Tag 08PG, Example `example-left-derived-colimits`
(blueprint: lem-trf-augmented-presheaf-bar-resolution).
The real formulas and normalized record are owned by
`def-trf-presheaf-bar-resolution-data`; this module states their existence.
-/

@[expose] public section

set_option autoImplicit false
universe u v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.PresheafBar

/-- The explicit augmented presheaf bar resolution, evaluation contraction, exactness
and normalized colimit comparison all exist simultaneously, for every small category
and every commutative coefficient ring.

Source: Stacks Project, Tag 08PG (`example-left-derived-colimits`), explicit augmented
presheaf-resolution expansion (blueprint: lem-trf-augmented-presheaf-bar-resolution).

Proof:
1. Extend the generator formulas linearly over the small direct sums. Associativity
of composition proves the restriction laws. Naturality of coefficient maps proves
compatibility with the last face and augmentation, and additivity holds on generators.
2. Two vertex deletions satisfy d_i d_j = d_(j-1) d_i. Nonadjacent deletions commute;
adjacent ones use composition associativity, and the terminal pair uses contravariance
of F. Opposite signs then cancel every pair in d². The degree -1 augmentation equation
is F(fa)x = F(a)F(f)x. The same argument constructs K and its differential.
3. Insert the evaluation object with its identity arrow. The first face removes it,
and each later face is insertion after the preceding old face. Their alternating sum
gives d s + s d = 1. In degree zero the two faces are (a,x) and (1,F(a)x); the
augmentation of (1,x) is x. No naturality of this insertion in V is needed.
4. A negative-degree cycle is d(s z). In degree zero the augmentation is split
surjective, and its kernel is im(d) by the same contraction. Positive terms vanish.
The objectwise homology computation and evaluation detection of isomorphisms in
lem-weil-pbc-site-module-presheaf-sheafification-exact imply QuasiIso of the augmentation.
5. For both B and K, each evaluated degree is a direct sum of coefficient sequences.
Injections are checked coordinatewise. Lift the finitely many nonzero coordinates to
prove kernel equals image and surjectivity, so both functors preserve short exactness.
6. Forget the incoming arrow to obtain a colimit cocone with value K^(-n). A cocone
factors through it by evaluating its chain generator on the identity incoming arrow
at U_n. The cocone relation along a recovers every other representative; identity
summands force uniqueness. This gives the canonical colimit isomorphism in each degree.
7. This comparison commutes with every face and coefficient map, hence gives a natural
isomorphism of cochain complexes. In degree zero its augmentation is normalized by
ι_V F(a)x = ι_U x, the defining colimit cocone relation. -/
theorem exists_resolution (E : Type u) [SmallCategory E] (R : Type r) [CommRing R] :
    Nonempty (Resolution.{u, v, r} E R) := by
  sorry

end CategoryTheory.PresheafBar
