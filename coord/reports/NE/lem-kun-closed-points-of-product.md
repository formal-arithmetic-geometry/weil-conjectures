## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedPointsProduct` states
`AlgebraicGeometry.closedPoint_iff_of_finiteType_product`.  It introduces a
field `K`, schemes `X` and `Y` of the same universe, their structure
morphisms `f : X ⟶ Spec K` and `g : Y ⟶ Spec K`, finite-type hypotheses on
both morphisms, and a point `z` of their categorical fibre product.  Its
conclusion is the equivalence between `z ∈ closedPoints (↑(pullback f g))`
and the conjunction that the first and second projection images of `z` lie
in `closedPoints X` and `closedPoints Y`, respectively.  The proof is
postponed with `sorry` as required for stage 2.

The Lean rendering of each hypothesis and clause is as follows.

1. “A field `K`” is `{K : Type u} [Field K]`.
2. “Schemes `X` and `Y`” is `{X Y : Scheme.{u}}`.
3. “Finite type over `K` for `X`” is
   `(f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [QuasiCompact f]`.
4. “Finite type over `K` for `Y`” is
   `(g : Y ⟶ Spec (.of K)) [LocallyOfFiniteType g] [QuasiCompact g]`.
   This is Mathlib's finite-type convention: locally of finite type together
   with quasi-compactness of the structure morphism.
5. “A point `z ∈ X ×_K Y`” is `(z : ↑(pullback f g))`.
6. “`z` is closed in the product” is
   `z ∈ closedPoints (↑(pullback f g))`.
7. “The image `x` in `X` is closed” is
   `pullback.fst f g z ∈ closedPoints X`.
8. “The image `y` in `Y` is closed” is
   `pullback.snd f g z ∈ closedPoints Y`.
9. “If and only if both images are closed” is the displayed equivalence with
   the conjunction of clauses 7 and 8.

Statement dependencies used by the module are the Mathlib declarations
`AlgebraicGeometry.LocallyOfFiniteType` and
`AlgebraicGeometry.QuasiCompact` from
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
`Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`,
`CategoryTheory.Limits.pullback` and its `fst`/`snd` projections from
`Mathlib.AlgebraicGeometry.Pullbacks`, and `closedPoints` from
`Mathlib.Topology.JacobsonSpace`.  The stated proof dependencies are imported
from `Sheaf.AlgebraicGeometry.ClosedPointField`, declaration
`AlgebraicGeometry.closedPoint_iff_residueField_trdeg_zero_and_finite`, and
`Sheaf.AlgebraicGeometry.FibreProductPointResidueField`, declaration
`AlgebraicGeometry.Scheme.Pullback.exists_residueField_equiv_ofPointTensor`.
The latter two imports are needed by the node's recorded proof route even
though they do not occur in the theorem's type.

The module docstring records the source proof in its six logical parts: the
finite-type affine-cover construction for the product; the forward implication
using injective residue-field maps; finite-dimensional spanning of the tensor
product in the converse; the prime tensor quotient and its residue-field
identification; the multiplication-by-a-nonzero-element argument showing the
finite-dimensional domain is a field; and the final closed-point criterion on
the product.

Edge cases checked were arbitrary fields (including positive characteristic),
empty schemes, zero-dimensional schemes, points whose projections are not
closed, and points over closed projections with nontrivial finite residue-field
extensions.  The statement has no algebraic-closure, separability,
nonemptiness, reducedness, or geometric-integrality assumption, and no
restriction on the characteristic.  The empty product and the cases where one
factor is empty are represented by the same categorical pullback and require
no special clause.

Searches made:

- `msearch.py ... leanfinder` with “A point of a fiber product of finite type
  schemes over a field is closed if and only if its two projections are
  closed” returned eight universally-closed and closed-immersion declarations;
  none states the equivalence.
- `msearch.py ... loogle` with “closedPoints, pullback, LocallyOfFiniteType,
  QuasiCompact” reported an unknown `pullback` identifier and no exact hit.
- `msearch.py ... grep` with
  `closed.*point.*pullback|pullback.*closedPoints|closedPoints.*pullback`
  returned no exact hit.
- `rg` over `WeilConjectures` and `lean/Sheaf` for closed-point/product and
  closedPoints/pullback patterns found no duplicate declaration.  The only
  nearby hits concern generic universally-closed maps or unrelated closed-point
  constructions.
- `grep -rn` for `lem-kun-closed-points-of-product` in the upstream source
  found no Lean declaration.

No statement correction, new definition node, dependency module, or
`STATEMENT-DISPUTED` note is needed.

## Second reading by NE

I independently opened the sandbox node and module, the four statement-dependency
nodes and their recorded Mathlib declarations, and the two imported project proof
dependencies. I read the exact blueprint source at
`/home/ubuntu/weil-launcher-nt/literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-closed-points-of-product.md`.
Its statement is verbatim the DAG statement: arbitrary field, finite-type factors,
and closedness of a point equivalent to closedness of both projection images.
I also read Stacks `schemes.tex`, Tags 01JR and 01JT, including the residue-field
assertion and proof, in the read-only `/home/ubuntu/c1-stacks-review` copy; and the
surrounding argument in `etale-cohomology.tex` at `lemma-kunneth-localize-on-X`.
The latter assumes only a field and finite-type schemes for this geometric fact.
It does not require the field to be separably closed, even though the later
Kunneth unit has that assumption. No source-wide hypothesis is missing here.

The complete object/hypothesis/conclusion checklist, in node order, is:

1. Field K: `{K : Type u} [Field K]`. Exact; no closure, cardinality,
   perfectness, or characteristic condition.
2. Schemes X and Y over K: `{X Y : Scheme.{u}}`,
   `(f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))`. Exact structure
   morphisms. The node `def-weil-scheme-over-base` records `Scheme.Over`,
   which is precisely the data of such a morphism. The explicit-morphism
   form is authorized for a fibre product and does not introduce a different
   notion or an extra commutativity hypothesis.
3. X finite type over K: `[LocallyOfFiniteType f] [QuasiCompact f]`.
   Exact conjunction from `def-weil-finite-type-morphism`.
4. Y finite type over K: `[LocallyOfFiniteType g] [QuasiCompact g]`.
   Exact, independently of X's hypotheses. I read the class bodies in
   Mathlib `Morphisms/FiniteType.lean` and `Morphisms/QuasiCompact.lean`:
   these are the affine finite-type and topological quasi-compactness
   conditions, not finite morphisms or finite presentation.
5. Product and its point: `(z : ↑(pullback f g))`. Exact chosen categorical
   fibre product over Spec K, using `def-pc-fibre-product`'s recorded
   `CategoryTheory.Limits.pullback`; Mathlib `Pullbacks.lean` supplies
   `HasPullbacks Scheme`. There is no user-supplied existence assumption.
6. Images x and y: `pullback.fst f g z` and `pullback.snd f g z`.
   Exact projections from that same chosen pullback, as read in
   `Limits/Shapes/Pullback/HasPullback.lean`. Substituting these expressions
   for the named images avoids redundant point binders and preserves
   the quantifiers: every K, X, Y, structure pair, and point z.
7. Closedness of z in the product:
   `z ∈ closedPoints (↑(pullback f g))`. Exact ambient closedness.
8. Both images closed:
   `pullback.fst f g z ∈ closedPoints X ∧
   pullback.snd f g z ∈ closedPoints Y`. Both clauses are present with
   their respective ambient schemes. I read `closedPoints` and
   `mem_closedPoints_iff` in Mathlib `Topology/JacobsonSpace.lean`:
   membership is exactly closedness of the singleton, as required by
   `def-weil-closed-points`, with no residue-field or rationality substitute.
9. Logical relation: the displayed `↔` connects clause 7 to the conjunction
   in clause 8. It includes both implications and neither strengthens nor
   weakens either conclusion. There is no added Noetherian, separated,
   proper, nonempty, reduced, integral, or algebraically closed instance.

Dependency and proof-plan check: I read the full signature of
`closedPoint_iff_residueField_trdeg_zero_and_finite` in
`Sheaf.AlgebraicGeometry.ClosedPointField`. Its second conjunct is exactly
the closed-point/finite-extension criterion under the same field and
finite-type assumptions, with the K-algebra induced by the structure
morphism; its separably closed clause is unused. I read
`Scheme.Pullback.exists_residueField_equiv_ofPointTensor` in
`Sheaf.AlgebraicGeometry.FibreProductPointResidueField`. It applies to
arbitrary schemes and the actual canonical tensor map, takes its prime
kernel, and identifies the kernel's residue field with that of z,
compatibly with both factor maps. It also gives the quotient-field
version when the quotient is a field. It is not an arbitrary field
isomorphism. Thus neither import hides a stronger assumption needed by
the documented proof. The open-product and affine-spectrum product
nodes are Mathlib leaves provided by `Pullbacks` and `PullbackCarrier`
(the latter is imported by the residue-field module). I checked their
recorded signatures against their node statements. There are no new
definition nodes or dependency modules in this delivery and no
`statement_change`, so no correction/citer audit is needed.

Edge cases: an empty factor gives an empty fibre product and hence no z;
no nonemptiness instance prevents this case. X=Y=Spec K gives its unique
closed point. Positive-dimensional factors can have nonclosed projection
images, and the equivalence then asserts that z is nonclosed. Finite
inseparable residue extensions are allowed: their tensor can be
nonreduced, but the proof uses a prime quotient, not the tensor itself as
a field. Finite separable extensions with a tensor that splits into
several factors are likewise covered. Nonreduced schemes and all
characteristics are admitted. The parameter `u` is arbitrary and shared
by the schemes and base field, as in the recorded scheme and fibre-product
interfaces; no fixed universe or independent smaller test universe is
introduced. There is no index set, integer n, or coefficient object in
this binary-product statement, so empty-index, n=0, and zero-module
cases introduce no additional hypothesis. In particular, this is not a
claim about nullary products or a spectrum of the zero ring as a field.

Independent H4 searches, all actually run with `msearch.py` and logged
in `searches.jsonl`:

- LeanFinder: "Closedness of a point in a scheme fibre product over a
  field is equivalent to closedness of both images, assuming the factors
  are finite type". Eight hits concern universally closed maps and
  closed immersions; none is this equivalence.
- LeanSearch: "A point of the fibre product of finite type schemes over
  a field is closed iff its projections are closed". Service unavailable
  (Internal Server Error); no mathematical verdict is inferred.
- Loogle: `closedPoints, AlgebraicGeometry.LocallyOfFiniteType`. Five
  hits: preservation of closed points and algebraically closed-field
  rational-point correspondences. I opened
  `Scheme.Hom.closePoints_subset_preimage_closedPoints` in Mathlib
  `Morphisms/Finite.lean`; it proves only preservation along one map to
  a Jacobson scheme, not the converse product assertion. The rational-point
  results require an algebraically closed base and do not match.
- Grep search: `closedPoints.*(fst|snd)|isClosed_singleton.*(pullback|tensor)|closedPoint.*(fiber|fibre|prod)`:
  no hit. Independently searched Mathlib, upstream `WeilConjectures`, and
  this project's `lean/Sheaf` with closedPoints/product/pullback and
  singleton/tensor terminology, and checked the exact declaration and
  blueprint id against the upstream name inventory. No duplicate found.
  I opened upstream `Topology/SpectralSpace/WLocal/Pullback.lean`:
  `closedPoints_prod` and `isClosed_singleton_prod_iff` concern the
  topological Cartesian product with a T1 first factor, not scheme fibre
  products. Upstream `ClosedPoints.lean:finitePoints_eq_closedPoints`
  concerns residue fields finite as sets over the integers, also different.

H5/H6/H8/H9: the delivered file defines no new data and states one named
theorem with exactly `by sorry`; nothing is proved. Its module source
and theorem docstring identify the blueprint node, and the theorem
docstring gives all six DAG proof steps: finite type of the product,
forward residue-field injection argument, finite-dimensional tensor,
prime quotient/residue-field identification, finite-dimensional domain
is a field, and the final closed-point criterion. All variables and
the universe are bound, there is no file-local notation/private helper,
and every Lean line is at most 100 characters. The node's `lean.statement`
was mechanically compared with the source signature and is verbatim equal.

Mismatches and changes: no mathematical or Lean mismatch was found, so
the correct module and node were retained. Two phrases in the worker
report need clarification: the proof is in the theorem docstring, not
the module docstring; and "empty product" means the binary fibre product
with an empty factor, not an empty-index product. This second reading
and the independent search log are the only additions.

Validation: `scompile.py NE lem-kun-closed-points-of-product
lean/Sheaf/AlgebraicGeometry/ClosedPointsProduct.lean` succeeded for the
sandbox and library forms in 3.3 and 3.4 seconds, with no errors or
warnings. No global build was run.
