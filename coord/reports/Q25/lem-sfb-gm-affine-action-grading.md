## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.GmAffineActionGrading` states
`AlgebraicGeometry.exists_grading_of_gm_affine_action`. Its only theorem has the
required `sorry` proof; there are no new definitions or auxiliary postponed lemmas.
The mathematical statement is unchanged. The already-landed node
`def-sfb-split-torus-over-ring` is added to `stmt_deps` to use its canonical
`AlgebraicGeometry.RingGroupSchemes.multiplicative`, rather than define G_m again.

Read the item and every original statement-dependency record, their full Mathlib
declarations and docstrings, the additional multiplicative-group node and module,
and the existing consumer `GmFixedSquareZeroLifting.lean`. Read Stacks
`groupoids.tex`, example-Gm-on-affine (0EKJ), lines 2303–2337, and
lemma-complete-reducibility-Gm (0EKK), lines 2339–2370. Also read the latest
blueprint's `det-thm-sf-ctf-stability-direct-images` statement and proof, the
ancestor recorded in the item's supporting-input chain.

Hypotheses and objects:

- Arbitrary commutative R and commutative R-algebra C are `(R C : Type u)` with
  `[CommRing R] [CommRing C] [Algebra R C]`. There is no `Nontrivial`, finiteness,
  field, flatness, smoothness, reducedness or Noetherian assumption. The universe
  is explicitly bound, and all rings and test algebras share an arbitrary ambient
  universe, as in the recorded consumer of this item.
- `Spec C` over `Spec R` is `(algSpec (.of R)).obj (op (CommAlgCat.of R C))`.
  The definition `algSpec` uses `Spec` and the actual algebra structure map.
- G is `(RingGroupSchemes.multiplicative R).X`, namely
  `(Spec (.of (LaurentPolynomial R))).asOver (Spec (.of R))`. Its canonical
  Laurent Hopf group law has z mapping to z tensor z, counit z mapping to 1,
  and inverse z mapping to z^-1. Mathlib `LaurentPolynomial` is the finite
  integer-indexed monoid algebra, so the node's unique finite formal coefficients
  and multiplication of monomials are its actual ring operations.
- The specified R-morphism with action identities is the instance
  `[ModObj G X]`. Its data is `smul : G ⊗ X ⟶ X`; the tensor in the cartesian
  category `Over (Spec R)` is the fibre product over R. Its fields `one_smul`
  and `mul_smul` are the two action identities. These imply the stated point
  identities on every test algebra. Conversely, the node's point identities
  imply these diagrams by testing universal points on the affine source
  products, so the bundled formulation adds no hypothesis.

Conclusions:

- `∃ W : ℤ → Submodule R C` supplies precisely the integer-indexed R-submodules.
- For every c, `∃! d : ℤ →₀ C, (∀ n, d n ∈ W n) ∧ d.sum (fun _ v ↦ v) = c`
  means a unique finitely supported family of homogeneous elements adding to c.
  This includes zeros off the support and is exactly a unique finite
  decomposition, without the irrelevant choice of a finite set containing its
  support. No internal grading is assumed in the hypotheses.
- `(1 : C) ∈ W 0` and `∀ r : R, algebraMap R C r ∈ W 0` render both degree-zero
  clauses separately.
- The quantified implication for m, n, c, d renders `C_m C_n ⊆ C_(m+n)`.
  Closure under sums is already part of each `Submodule`.
- For every commutative R-algebra B and x:C →ₐ[R] B, the map
  `(algSpec (.of R)).map (CommAlgCat.ofHom x).op` is the corresponding B-point
  of X. The fully faithful affine-spectrum functor identifies every R-scheme
  point of X in this way.
- The variable t ranges over every B-point of G. Such a point is exactly a
  unit of B: pull back z for the unit, and conversely evaluate Laurent
  polynomials at that unit using `LaurentPolynomial.eval₂ (algebraMap R B)`.
  Thus quantifying over these t is precisely the node's quantification over Bˣ,
  not just its ordinary R-points or points of fields.
- `t • ...` is the induced point action, defined in
  `CategoryTheory.Hom.instSMul` by pairing the two points and composing with
  the internal action morphism. `Spec.preimage ... .left` recovers its coordinate
  ring map. Its value at c is therefore the node's `a_B(t,x)(c)`.
- `(Spec.preimage t.left).hom (LaurentPolynomial.T n) * x c` is exactly
  `t(z)^n * x(c)`. Indeed `T n` is the nth integer power of the universal unit,
  and ring maps preserve this identity, including inverse powers. This avoids
  introducing a duplicate unit-to-point construction. The concrete ring type
  annotations in the formula only resolve the bundled `algSpec` carrier.
- The formula is required for every n and every c in W n. There are no other
  conclusions or assumptions.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`;
  `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`: `Spec.preimage`,
  `Spec.homEquiv`, used for the actual affine point correspondence.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, `pullback.lift`;
  supplied transitively by the affine group-scheme and cartesian-over imports.
  The product over the base in `ModObj` is this fibre-product construction.
- `Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing`:
  `AlgebraicGeometry.RingGroupSchemes.multiplicative`, with its inherited Hopf
  group-object structure.
- `Mathlib.AlgebraicGeometry.Group.Affine`: `AlgebraicGeometry.algSpec`,
  its object and map formulas, fullness and faithfulness.
- `Mathlib.CategoryTheory.Monoidal.Cartesian.Mod`: the induced action on Hom;
  `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.ModObj` and its fields.
- `Mathlib.Algebra.Polynomial.Laurent`: `LaurentPolynomial`, `C`, `T`, `eval₂`,
  `eval₂_T`; the Laurent Hopf structure comes from
  `Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra` through the group module.
- `Mathlib.LinearAlgebra.Finsupp.Defs`: finite-support function and sum API.

There are no further proof-only module imports: both recorded proof dependencies
are the original statement dependencies and are already available publicly.

Edge cases checked before writing: R=0 forces any R-algebra C=0, and its empty
spectrum and unique zero decomposition are allowed. C=0 over nonzero R is also
allowed. Under the trivial action W_0=C and W_n=0 for n≠0 satisfy the conclusion.
For C=R[x] with x of weight 1 or -1, the formula has respectively positive or
negative powers and the sign agrees with Stacks 0EKJ. For nilpotent base R=Z/4,
finite coefficient comparison remains valid. B=0 is allowed; all values are zero.
The decomposition of zero is the zero finitely supported function. No finite
support is imposed uniformly on all of C; only individual decompositions are
finite, as required for polynomial examples of unbounded weight.

Searches for an existing statement (2026-10-24):

- `msearch.py leanfinder`: "An action of the multiplicative group scheme on an
  affine scheme gives an integer grading of the coordinate algebra" returned
  Proj/projective-spectrum and graded-monoid results, no affine-action grading.
- `msearch.py loogle`: `"LaurentPolynomial", "GradedAlgebra"` returned zero hits.
- `msearch.py grep`: `Gm.*grad|grad.*Gm|coaction` in AlgebraicGeometry returned
  zero hits.
- `msearch.py leansearch`: "An action of the multiplicative group on an affine
  scheme over a ring induces an integer graded algebra" returned `GradedAlgebra`
  and graded action structures; these assume the grading rather than construct
  it from a group-scheme action.
- Direct `rg` on Mathlib AlgebraicGeometry with
  `Gm.*grad|grad.*Gm|multiplicative.*group.*grad|coaction` found no theorem.
  Read `RingTheory/GradedAlgebra/Basic.lean`: `GradedAlgebra` is grading data,
  not the missing existence result. Using finite-support functions in the
  proposition states the node's decomposition directly without defining a
  competing notion of graded algebra.
- Direct `rg` on both `lean/WeilConjectures` and `lean/Sheaf` for
  `Gm.*grad|grad.*Gm|gm_affine|gm.*grading`, and on the upstream name index,
  found no duplicate. Searching the item's id found only the downstream
  fixed-square-zero lifting proof plan. Read the existing field-only
  `GmRepresentationWeightBasis` theorem: it treats finite-dimensional vector
  spaces, so does not give this arbitrary-ring coordinate-algebra statement.
- The DAG's `lem-sfb-group-algebra-coaction-grading` is a general coaction result,
  not this scheme-action statement or an existing Lean attachment of it.

Validation: the prescribed `scompile.py` compiled the sandbox probe and the named
library module cleanly (1.4 seconds each), with no warnings. The first compile
exposed bundled-carrier inference in the final multiplication; explicit
`CommRingCat.of C/B` annotations repaired it without a mathematical change.
No statement dispute, statement correction, missing notion, or dependency repair
was necessary.

## Second reading by Q25

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
