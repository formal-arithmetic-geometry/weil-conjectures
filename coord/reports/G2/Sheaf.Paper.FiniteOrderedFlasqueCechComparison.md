## What changed

Proved the finite ordered flasque Čech comparison without changing its statement.
The explicit coefficient map is constructed by its resolution-degree-zero total
inclusions. Its cochain equation, coefficient-map naturality, degree-zero
compatibility, and single-coefficient isomorphism are proved componentwise.

The global-section comparison uses flasque ordered row exactness and finite-strip
row augmentation. Flasque row exactness reuses the source library's
`TopCat.Sheaf.exactAt_cechComplex_of_isFlasque` and the existing ordered/usual
Čech restriction homotopy equivalence. The coefficient comparison uses finite
products of section quasi-isomorphisms, restriction of scalars, and the existing
finite-column comparison theorem. The naturality clause uses the canonical
single-complex/pushforward isomorphism and the existing augmentation naturality.

Five new modules contain these constructions and proved helper results:
`FlasqueAlternatingCechRowAugmentation`,
`FiniteOrderedFlasqueCechComparisonAlpha`, `FiniteOrderedCechCoefficientMap`,
`FiniteOrderedCechTotalMap`, and `FiniteOrderedFlasqueCechComparisonBeta`, all
under `Sheaf.Paper`. Their DAG nodes record the actual proof dependencies.
No existing definition or statement is changed, and no consumer adaptation is needed.

Repair of return f4bbf2051: removed all four flagged duplicate theorems from
`FiniteOrderedCechTotalMap`. Its proof-only `import all` of
`Sheaf.AlgebraicGeometry.QCohAlternatingCechResolutionQuasiIso` supplies the
existing column projection, its isomorphism theorem, and both finite-support
lemmas. Removed the duplicate projection definitions too. The remaining column
comparison has explicitly stated sectionwise hypotheses and is more general
than the quasi-coherent resolution comparison in that existing module.

Also removed the duplicate column-vanishing theorem from
`FiniteOrderedFlasqueCechComparisonAlpha`. A proof-only `import all` of
`Sheaf.AlgebraicGeometry.InjectiveTermsAlternatingCechAugmentation` supplies
its existing helper. Neither imported module's main comparison theorem is used.
The new-node proof descriptions name the reused helpers; their mathematical
proof dependencies remain unchanged.

The full-delivery duplicate scan found five further copied helper statements
in `FlasqueAlternatingCechRowAugmentation`: `alternatingRow_d_apply`,
`singletonIntersection`, `alternatingRow_zero_d`, `alternatingRow_glue`, and
`alternatingRow_mono`. These and their copied auxiliary definitions are removed.
A proof-only `import all` of
`Sheaf.AlgebraicGeometry.InjectiveAlternatingCechRowAugmentation` reuses the
existing proofs. The new flasque positive-degree exactness proof remains,
under the descriptive private name `flasqueAlternatingRow_positive`.

## Proved and sorry left

Closed: `AlgebraicGeometry.finiteOrderedFlasqueCechComparison` (one original hole).
Added holes: none. Remaining holes in the delivery: none.
The five new helper modules also contain no `sorry`.
The new proved public theorems are
`AlgebraicGeometry.flasque_alternatingCech_row_augmentation`,
`AlgebraicGeometry.finiteOrderedFlasqueCechComparison_alpha`,
`AlgebraicGeometry.coefficient_comm`,
`AlgebraicGeometry.orderedCechCoefficientMap_naturality`,
`AlgebraicGeometry.orderedCechCoefficientMap_zero`,
`AlgebraicGeometry.orderedCechCoefficientMap_single_isIso`,
`AlgebraicGeometry.orderedCechTotalMap_quasiIso`, and
`AlgebraicGeometry.orderedCechCoefficientMap_quasiIso`.
The definition `AlgebraicGeometry.orderedCechCoefficientMap` contains explicit data.
This is a proof, not a decomposition into unproved helper claims.
All six sandbox modules compile through `lcompile.py --all`. The existing
comparison theorem signature is textually unchanged, and every Lean line
respects the 100-character limit.

## No longer needed

Removed the proof import `Sheaf.Algebra.Homology.FirstQuadrantTotalComparison`
from the item module. Its node
`lem-sc-first-quadrant-total-column-comparison` is no longer a proof dependency
or an approved tool use of this comparison. Finiteness in the Čech direction
allows the already proved finite-strip row and integer finite-column comparison
lemmas instead; no signed transposition of totals is needed.

The proposed fresh finite-cover induction for ordered flasque exactness is
unnecessary: the library already proves full flasque Čech exactness and the
ordered/usual homotopy equivalence. No new node or unproved induction lemma is
introduced for that route. The existing statement dependencies and public
imports of the item are preserved.

The copied private proofs `alternatingCechColumnProjection_isIso`,
`alternatingCechDouble_isZero_column`, `alternatingCechDouble_strictlyGE` and
`alternatingCechDouble_strictlyLE` are no longer needed in the total-map module.
Its copied `alternatingCechTermsProjection` and
`alternatingCechColumnProjection` definitions are also removed. The copied
`alternatingCechDouble_isZero_column` in alpha is removed as well. Their existing
library implementations are imported and used. No existing library module is
withdrawn or made unreachable by this repair.

The copied row helpers `alternatingRow_d_apply`, `singletonIntersection`,
`alternatingRow_zero_d`, `alternatingRow_glue`, and `alternatingRow_mono`,
and their auxiliary definitions `intersectionCech` and `singletonTuple`,
are also removed from the new flasque row module in favor of their existing
library implementations. Only the flasque positive-degree argument is new.

## Where the brief, the DAG or earlier work was wrong

The returned delivery copied private helper lemmas already proved in the
library. This was unnecessary duplication; the repair imports and uses those
existing declarations. No false statement or unusable dependency was found.
The DAG's proof route was longer than needed because it did not use the source library's flasque Čech
exactness theorem and the finite support of the ordered Čech direction.
The alpha helper needs only nonnegativity, flasqueness and the cover condition;
the beta helper needs only sectionwise quasi-isomorphisms. The item's full
original hypotheses and all of its naturality clauses remain unchanged.

## New nodes

`lem-weil-pbc-flasque-alternating-cech-row-augmentation`: flasque ordered row
augmentation, obtained from full Čech exactness, ordered restriction homotopy,
and degree-zero sheaf gluing. Empty covers and empty intersections are handled
by the sheaf condition and zero objects.

`lem-weil-pbc-finite-ordered-flasque-cech-comparison-alpha`: finite-strip row
comparison. Negative coefficient rows are zero, while nonnegative rows use
the flasque augmentation lemma.

`lem-weil-pbc-ordered-cech-coefficient-map`: the explicit coefficient map and
its cochain identity, naturality, degree-zero agreement, and the single-sheaf
isomorphism. All off-axis summands in the single-sheaf case are zero.

`lem-weil-pbc-ordered-cech-total-map`: maps of ordered Čech totals are
quasi-isomorphisms under sectionwise hypotheses. Columns are finite products
of section complexes, and only finitely many columns can be nonzero.

`lem-weil-pbc-finite-ordered-flasque-cech-comparison-beta`: combine the total
map comparison with the isomorphism from the coefficient Čech complex to the
total of its single complex, identified with beta by naturality.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
