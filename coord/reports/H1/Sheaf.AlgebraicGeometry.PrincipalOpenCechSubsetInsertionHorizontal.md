## What changed

Replaced the sorry in `AlgebraicGeometry.principalSubsetInsertion_horizontal` with a reduction to
one supported-tuple ordered-face calculation. The original theorem signature is unchanged.
The main module now has proved private helpers for evaluating sums of additive-group morphisms
and for the horizontal differential of one source summand. The latter proves the total-degree
arithmetic, applies `ι_D₁` and `d₁_eq`, removes the horizontal sign, identifies the extended
column differential using `extend_d_eq` and `CochainComplex.of_d`, and cancels the extension
isomorphisms. The theorem constructs the subset boundary as an additive homomorphism, expands
the finite insertion sum, and reassembles supported coordinates by additivity.

Added the proof-only import `Sheaf.AlgebraicGeometry.PrincipalOpenCechSubsetHorizontalFaces`.
That new module states the remaining face calculation for one fixed source subset and one
section, without the total differential D₁ or arbitrary coordinate functions. Updated the
original DAG proof and dependencies to match this argument. No existing definitions,
public imports, or signatures changed; no forced consumer adaptations are needed.

## Proved and sorry left

Closed: `AlgebraicGeometry.principalSubsetInsertion_horizontal`
(node `lem-sc-principal-open-cech-subset-insertion-horizontal`), 1 of 1 original holes.
This is a decomposition, not a sorry-free proof: its remaining dependency is stated below.
The private helpers `sum_apply` and `principalSubsetInsertOne_horizontal` are fully proved.

Added and left: `AlgebraicGeometry.principalSubsetHorizontalFaces`
(node `lem-sc-principal-open-cech-subset-horizontal-faces`), exactly one public named theorem
with whole proof `:= by sorry` in its own module. It handles only the ordered-face calculation
for one supported source tuple. Total-differential identification and finite linear assembly
are proved in the assigned module. Net holes closed minus added: zero. No other sorry remains
in the delivered files.

## No longer needed

No existing import, DAG node, or library module was pruned. Both original definition
nodes remain needed; the insertion module is needed by the statements, and the new face
module is needed only by the proof. Removed the earlier sandbox's rejected whole-statement
`principalSubsetInsertion_horizontal_core` and its uncommitted
`lem-sc-principal-open-cech-subset-insertion-horizontal-single` node. Removed its unrelated
copies of `PrincipalOpenCechSubsetInsertion` and `PrincipalOpenCechSubsetInsertionVertical`;
neither is part of this delivery. These discarded attempt files are not library pruning.

## Where the brief, the DAG or earlier work was wrong

The earlier core theorem was identical to the assigned theorem and did not reduce the proof.
The new statement instead fixes one source subset, calculates its explicit ordered tuple
differential, and leaves total D₁ bookkeeping and arbitrary-coordinate assembly to proved code.
The original DAG's single prose step did not expose the ordered-face calculation as a separate
Lean statement. Its two dependencies are definitions, so neither supplied that identity.

Read Stacks Tags [01FG](https://stacks.math.columbia.edu/tag/01FG),
[08C1](https://stacks.math.columbia.edu/tag/08C1), and
[08C0](https://stacks.math.columbia.edu/tag/08C0). The formula immediately preceding
Definition 20.23.2 in 01FG is the source of the new lemma. Checked its edge cases: r=0 admits
no nonempty source; singleton targets have empty deletions and zero coefficient; a source
of maximal cardinality has no nonzero target face; negative coefficient degrees remain allowed.
No mathematical statement was corrected. The unit record `sk-thm-picard-duality` was read and
its statement and route are unchanged.

## New nodes

`lem-sc-principal-open-cech-subset-horizontal-faces`, in chapter `sec-picard-framework`, unit
`sk-thm-picard-duality`: the fixed-source ordered face calculation. Its statement uses the
existing insertion and total-complex definitions. Its complete proof in words explains
support, increasing enumeration, deletion signs, section transport, degree transport, and
boundary cases. Mathlib searches were run through msearch (LeanFinder, Loogle, grep;
LeanSearch returned unavailable), and blueprint searches for horizontal differential,
finite subset, and ordered Cech found no matching imported blueprint statement. The
machine's ancestor query returns no blueprint ancestor for this existing generated node;
the new node records its immediate source proof step explicitly. No change record is needed.

## Second reading by H1

1. Compared both delivered Lean modules with the repository versions. Existing declaration
signatures and definitions are unchanged byte for byte; the only interface addition is the
new proof-only face module and its split theorem.

2. Compiled `PrincipalOpenCechSubsetHorizontalFaces.lean` and
`PrincipalOpenCechSubsetInsertionHorizontal.lean` with `lcompile.py`; both compile cleanly.
There are no `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations, and the
only remaining `sorry` is the named `principalSubsetHorizontalFaces` theorem.

3. Checked the split statement against the ordered Cech differential and its boundary cases.
It is a strict one-source reduction of the target, with the source, node, docstring, and DAG
record present; no duplicate library declaration was found.

4. The proof follows the unit route through total-complex inclusion, horizontal differential,
and ordered Cech faces. The import used only for the proof is plain `import`; no removable
existing import or proof dependency was found, and no pruning is claimed.

5. The item and split-node DAG records match the declarations, proof dependencies, proof steps,
and realized unit route. No statement or definition change, forced adaptation, or change record
is needed.

Changed: added this second-reading record only; no Lean proof or statement was altered.
