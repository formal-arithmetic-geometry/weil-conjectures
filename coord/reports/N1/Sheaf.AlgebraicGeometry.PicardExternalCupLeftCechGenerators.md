## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.PicardExternalCupLeftCechGenerators`
with a complete Lean proof from two strictly separate geometric steps and the existing
`HomologicalComplex.tensor_kunneth_nat`. The existing theorem signature and its public
imports are unchanged. Added proof-only imports of `PicardLeftCechCupHomology` and
`TensorKunnethNat`.

Added `PicardLeftCechCupConstruction`: its explicit Prop definition
`IsPicardLeftCechCup` fixes theta on every nonnegative bidegree pure cochain tensor by
the front/back section formula, using the existing `picardCechPullSection`,
`picardProductCechFace`, `cupFront`, and `cupBack`. Its existence theorem is purely
cochain-level, natural in every left module, and assumes neither quasi-coherence nor
affine diagonals. No data are chosen from this new theorem to define any object.

Added `PicardLeftCechCupHomology`: for a transformation satisfying those cochain
coordinates, affine comparisons give scalar-total and product homology isomorphisms
and the existing cycle-normalization predicate `IsPicardExternalCupHomology`.
It does not produce theta or the desired direct-sum equivalence. The main proof
constructs that equivalence by composing tensor Kunneth with the inverse scalar-total
comparison. It lifts arbitrary factor homology elements through the epic homology
projections, obtains their total cycle from Kunneth's cycle formula, rewrites by that
formula, and applies the normalization on cycles. These are actual Lean proof steps,
not a direct application of a renamed statement.

Updated the original node's proof, proof_deps and proof_origin to match the Lean.
The unit remains `sk-prop-av-cube`; its statement and route are untouched.
All three delivered modules compiled cleanly through `lcompile.py --all`.
`deliver3.py N1 Sheaf.AlgebraicGeometry.PicardExternalCupLeftCechGenerators --no-push`
printed OK: compiles and passes the preflight except for the second reading, which
the second reader writes. Nothing was pushed.

## Proved and sorry left

Closed the original named hole:
`AlgebraicGeometry.Scheme.Modules.picardExternalCup_left_cech_generators`
(node `lem-sc-picard-external-cup-left-cech-generators`). The item has no sorry left.

Added exactly two named holes, one per new module:

- `AlgebraicGeometry.Scheme.Modules.picardLeftCechCup_exists`
  (node `lem-sc-picard-left-cech-cup-construction`).
- `AlgebraicGeometry.Scheme.Modules.picardLeftCechCup_homology`
  (node `lem-sc-picard-left-cech-cup-homology`).

This is a decomposition: one upper hole closed and two lower holes added, not a
claim of an axiom-free geometric proof. The arithmetic net for these delivered
holes is -1; no closure ledger measurement is claimed. Existing dependencies may
still depend on sorryAx, as intended by the stage-3 brief. Every newly remaining
sorry is exactly a public theorem with its source, complete proof in words, and node.
There is no sorry in a definition or private declaration, and no added axiom.

## No longer needed

None. No original import was removed, and no existing node or module is claimed
pruned. The original cochain construction dependencies are retained under
`lem-sc-picard-left-cech-cup-construction`; the original affine-comparison and
cup-compatibility dependencies are retained under
`lem-sc-picard-left-cech-cup-homology`. Moving those dependencies below the two
intermediate steps is not pruning them. The shared right-cup construction module
is imported for its already existing section and face constructions; its right
existence theorem is not applied in this proof.

The following old direct `proof_deps` are no longer applied by the item itself;
they remain in the plans of the two new lemmas and are not closure-pruning claims:

- `def-sc-cech-cup-product`.
- `def-sc-cech-refinement-cochain-map`.
- `def-sc-field-linear-module-cohomology-operations`.
- `lem-pc-module-pullback-adjunction`.
- `lem-sc-cech-comparison-map-iso-affine`.
- `lem-sc-cech-comparison-map-naturality`.
- `lem-sc-picard-affine-diagonal-intersections`.
- `lem-sc-picard-cech-cup-pullback-compat`.
- `lem-weil-pbc-module-pullback-quasi-coherent`.
- `lem-weil-pbc-quasi-coherent-tensor-product-affine-sections`.

Removed the stale unlanded `PicardExternalCupLeftCechGeneratorFormula__probe.lean`
from the earlier attempt. It is not a library dependency or a pruning claim.

## Where the brief, the DAG or earlier work was wrong

The previous proposed formula for arbitrary theta was false. In degree zero on
Spec k with structure-sheaf coefficients, theta=0 kills every source class while
the external cup of units is nonzero. Mere existence of a transformation cannot
fix this. The replacement explicitly constrains theta on cochains by front/back
pullback and tensor sections before asserting any homology comparison. For theta=0
that predicate requires those section tensors to vanish, so the earlier
counterexample does not meet its hypothesis.

Edge cases checked at the statement level: a zero coefficient makes the section
pairing zero; empty schemes have zero sections on the empty opens and zero
cohomology; degree zero has the ordinary pullback section tensor on the (0,0)
summand. Negative bidegrees have a zero extended factor and require no additional
coordinate assertion. In all cases the tensor-total differential is the standard
signed differential. No invertibility of external cup is assumed or used.

The library's right cup construction fixes F and is natural in G; it cannot be
applied as a natural transformation in F. Its source also extends the natural
indexed total, whereas the fixed left functor totals the extended factors.
The new predicate is written directly for the latter source, using its integer
bidegree inclusions and the canonical extension term isomorphisms. Thus no
unsupported equality of those two differently indexed totals is asserted.

The cited Stacks TeX sources are not installed in this clone. Read the official
source pages at https://stacks.math.columbia.edu/tag/0BED,
https://stacks.math.columbia.edu/tag/01FD,
https://stacks.math.columbia.edu/tag/07MB, and
https://stacks.math.columbia.edu/tag/0FKV. The cochain construction, coefficient
naturality and affine comparison are the original plan, not a new geometric route.
Mathlib searches were run with msearch.py and recorded in searches.jsonl;
LeanSearch returned Internal Server Error, and no absence claim is inferred from it.

## New nodes

`lem-sc-picard-left-cech-cup-construction`, at
`dag/nodes/sec-abelian-varieties/lem-sc-picard-left-cech-cup-construction.json`,
states the first original proof step: a left-natural transformation with explicit
cochain coordinates. It includes the predicate definition and the one existence
theorem in `lean/Sheaf/AlgebraicGeometry/PicardLeftCechCupConstruction.lean`.

`lem-sc-picard-left-cech-cup-homology`, at
`dag/nodes/sec-abelian-varieties/lem-sc-picard-left-cech-cup-homology.json`,
states the affine-comparison and cycle-normalization steps for a transformation
already constrained by that predicate, in
`lean/Sheaf/AlgebraicGeometry/PicardLeftCechCupHomology.lean`.

No existing statement or definition changed, no forced adaptation, and no change
record is needed.

## Second reading by N1

1. Compared the delivered item to the repository with diff and checked its theorem
   signature byte for byte. Only two plain proof imports and the proof body changed;
   the existing statement, definitions, visibility and public imports are unchanged.
   The other two modules are new. No change record or forced adaptation is needed.
   Verdict: pass.
2. Independently compiled all three modules through lcompile.py --all: no errors
   or warnings. The sole original sorry is closed; exactly the two reported public
   theorem sorries remain. Read every definition and proof: no hollow data, private
   sorry, axiom, unsafe, opaque, extern, implemented_by or kernel bypass. The new
   existential witnesses are eliminated only inside a theorem proving a proposition;
   no definition chooses data from them. Verdict: pass, as a decomposition with two
   geometric obligations still open, not an axiom-free proof.
   A scratch copy with #print axioms checked all four delivered declarations:
   IsPicardLeftCechCup uses only propext, Classical.choice and Quot.sound; the
   three theorems additionally use only sorryAx, from the documented open proofs.
   The scratch copy was removed before delivery.
3. Read both new statements, their predicates, full docstring arguments, and nodes.
   Checked the front/back indices, extension isomorphism directions, tensor summand
   inclusions, signed Leibniz convention, and the unit-normalized pullback sections.
   On Spec k in degree zero the formula is the tensor of sections and excludes the
   zero-transformation counterexample with nonzero unit classes. Zero coefficients,
   empty factors and negative extended degrees give zero terms. In positive degrees
   the shared-vertex cancellation gives the usual (-1)^p differential sign. The
   homology comparison uses factor comparisons and field tensor Kunneth, without
   assuming external cup invertible. The construction fixes cochain coordinates;
   the comparison assumes those coordinates and transports cycles. Neither merely
   renames the original existential generator theorem.
   Independently searched with leanfinder (Alexander Whitney pairing of Cech cochains
   natural in coefficient sheaves on product schemes), loogle
   (HomologicalComplex.extendMap), msearch grep, and rg throughout the project.
   Read CechCupProduct, CechCupPullbackCompat, TensorPullbackAdjunction,
   PicardRightCechCupConstruction, PicardRightCechCupHomology and
   PicardExternalCupHomologyUnique. Existing results provide components, not the
   needed left-natural integer-total construction or its comparison. The right
   construction fixes F and is natural in G, and extends the natural-index tensor
   total: applying it directly would not establish the left predicate. Closing either
   geometric obligation requires substantial constructions, not a short proof.
   Read official Stacks Tags 0BED, 01FD, 07MB and 0FKV to verify the route.
   Verdict: pass; two strictly separate original geometric steps remain open.
4. Read the proof from its target down. The tensor Kunneth theorem and surjective
   homology projections supply the actual algebraic reduction. The plain imports
   are needed for the two new lemmas and tensor_kunneth_nat. Public imports in the
   new modules supply constants used by their signatures or predicate definition.
   Enumerated every old direct proof dependency moved below the new steps under
   No longer needed; none is claimed globally pruned. Read sk-prop-av-cube.json:
   its realized arrays and route are untouched; this is below its unit level.
   Verdict: pass.
5. Checked the original node changes only proof, proof_deps and proof_origin.
   For all three nodes, proof_deps is exactly the union of step uses, every dependency
   exists, and lean.statement is a verbatim signature in the matching file. The new
   nodes record source, argument, searches, creation, blueprint provenance, chapter,
   unit and Lean declarations. The main node records construction, comparison,
   Kunneth, cycle lifts and normalization in the order used by the Lean proof.
   Verdict: pass.

Changed only report.md: made the list of moved old direct proof dependencies
explicit and added this independent second reading. No Lean proof or new statement
needed repair. Holes closed: picardExternalCup_left_cech_generators (one of one
original holes). Holes added: picardLeftCechCup_exists and
picardLeftCechCup_homology (two). Net delivered holes: -1; pruned modules: none.
