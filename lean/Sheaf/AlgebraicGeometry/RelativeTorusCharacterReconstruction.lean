module

public import Sheaf.AlgebraicGeometry.RelativeCharacterDualityData
import Sheaf.AlgebraicGeometry.RelativeSplitTorusMatrixSheaf
import Sheaf.Paper.ConstantSheafSectionsLocallyConstant
import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.AlgebraicGeometry.FpqcLabelledClopenDescent
import Sheaf.AlgebraicGeometry.FppfAffineRefinement
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.AffineFpqcDescent
import Sheaf.AlgebraicGeometry.FpqcAffineDescent
import WeilConjectures.AlgebraicGeometry.FpqcMorphismsDescend
import Sheaf.AlgebraicGeometry.ExistsSchemeOfZariskiCocycle
import Sheaf.AlgebraicGeometry.PullbackConstantModule
import Sheaf.AlgebraicGeometry.FpqcFinerThanEtale
import Mathlib.CategoryTheory.Yoneda
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.MorphismProperty.Descent
import WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.GeometricLifts
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # Character reconstruction of relative tori

Source: Lan, §3.1.1, Definitions 3.1.1.1, 3.1.1.4--5 and Lemma 3.1.1.6;
Milne, Algebraic Groups, Lemma 12.4 and Theorem 12.9(a), pp.232--234;
Stacks, Tags 022U, 0245, 02L5 and 02VL
(blueprint: lem-sfb-relative-torus-character-reconstruction).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace AlgebraicGeometry.RelativeCharacter

/-- Tori and etale lattices are contravariantly equivalent by the character functor,
with the representing quasi-inverse, evaluation identifications, arbitrary coherent
base change, local split models, smooth affine faithfully flat finite-presentation
structure maps and split geometric fibres of the stalk rank.

Source: Lan, §3.1.1, Lemma 3.1.1.6; Milne, Lemma 12.4 and Theorem 12.9(a);
Stacks, Tags 022U, 0245, 02L5 and 02VL
(blueprint: lem-sfb-relative-torus-character-reconstruction).

Proof:
1. Use lem-sfb-relative-split-torus-matrix-sheaf on the Laurent Hopf models.
   Homomorphisms are locally constant integer matrices, including over disconnected
   and nonreduced rings. Use lem-weil-pbc-constant-sheaf-sections-locally-constant
   and def-weil-pbc-sheafification to identify maps of finite free constant sheaves
   with those matrices. Composition is substitution, and addition adds exponents.
2. For an fppf torus, inverse transition matrices identify the ranks on overlaps
   (reduce modulo 2 to check equal ranks). Apply lem-sfb-fpqc-labelled-clopen-descent
   after lem-pc-fppf-affine-refinement to descend rank strata. Its frame functor is
   an fppf sheaf by lem-weil-pbc-fpqc-representable-descent, locally a coproduct of
   copies of the base indexed by GL_r(Z), using lem-weil-pbc-scheme-coproduct-family.
   By lem-sfb-fppf-local-algebraic-space and
   lem-sfb-representable-fppf-etale-open-descent it is an etale surjective algebraic
   space. Apply lem-sfb-smooth-space-cover-etale-sections to obtain etale frames.
   Thus the character sheaf is a lattice.
3. Trivialize a lattice on an etale cover. If a_ij changes lattice coordinates,
   transport functionals by h to h composed with a_ij inverse. The matrix theorem
   represents these as split-torus isomorphisms satisfying the descent cocycle.
   Over each affine base open apply lem-pc-fppf-affine-refinement and
   lem-galois-fpqc-affine-descent-effective; affineness follows from
   lem-weil-pbc-fpqc-descend-affine and lem-weil-pbc-affine-morphism-permanence.
   Descend group operations by lem-galois-fpqc-morphisms-descend. Compare on affine
   covers of intersections and glue by lem-galois-glue, without assuming affine
   intersections. This constructs the commutative group scheme D.
4. For every test scheme pull back the splitting cover. Constant sheaves pull back
   by lem-kun-pullback-constant. The sheafification universal property identifies
   functionals on Z^r with r units, represented by the split Laurent model.
   These tuples have exactly the inverse-dual transitions of step 3. Sheaf maps
   glue by the sheaf axiom; scheme maps glue by
   lem-weil-pbc-fpqc-representable-descent and lem-weil-pbc-fpqc-finer-than-etale.
   The resulting point equivalences preserve operations and test-scheme pullback.
   The same argument proves the split model for every trivializing base change.
5. Evaluation m to (h to h(m)) is an isomorphism on every split chart.
   Evaluation p to (chi to chi(p)) is also a split-chart isomorphism by step 2.
   Descent and lem-pc-yoneda give the two evaluation isomorphisms globally.
   Precomposition defines both functors on morphisms. The identities h(b(m)) and
   chi(f(p)) prove naturality and the equivalence triangle identities.
6. Pull back a splitting cover along any scheme morphism. Both constructions have
   the same split models and inverse-dual transitions; the identity maps on those
   models glue to comparison isomorphisms. Character pullback is likewise the
   identity on the pulled-back constant lattice, so it is invertible. Evaluation
   formulas are unchanged. Uniqueness gives identity and successive-base-change
   coherence and identifies the dual comparison as the evaluation mate.
   This never assumes that arbitrary inverse image preserves the units sheaf.
7. The local model has the finite presentation A[x_i,y_i]/(x_i*y_i-1).
   Units lift across square-zero ideals by correcting a lifted inverse with 1-e;
   hence the model is smooth. Its identity section gives surjectivity.
   Apply lem-trf-smooth-fpqc-base-descent on affine refinements and Zariski locality;
   lem-pc-smooth-flat gives flatness and local finite presentation. Affine descent
   gives affineness, hence quasi-compactness and quasi-separatedness, so finite
   presentation. A geometric splitting chart has a section by
   lem-exc-etale-lift-separably-closed-factorization; the fibre is the split torus
   of the lattice stalk rank. Rank zero gives the trivial group S, and an empty
   base gives the empty scheme. All assertions include these cases. -/
theorem reconstruction : Nonempty Reconstruction.{u} := by
  sorry

end AlgebraicGeometry.RelativeCharacter
