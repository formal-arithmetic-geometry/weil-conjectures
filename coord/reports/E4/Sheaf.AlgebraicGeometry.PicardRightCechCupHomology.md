## What changed

Replaced `picardRightCechCup_homology`'s sorry with a compiling Lean reduction to
`picardRightCechCup_generators` and the existing `tensor_kunneth_nat` theorem.
The existing theorem signature, definitions, public imports, and section commands
are unchanged.
Added proof-only imports of `Sheaf.AlgebraicGeometry.PicardRightCechCupGenerators`
and `Sheaf.Algebra.Homology.TensorKunnethNat`.

The new module states the geometric comparison only on pure factor-homology tensors
in direct-sum coordinates. It chooses the Cech equivalence and product comparison
jointly with their generator formula. The item's proof chooses tensor Kunneth
coordinates for the scalar models and composes their equivalence with the inverse
Cech equivalence to construct a. For each specified total cycle, injectivity of the
cycle inclusion identifies it with the cycle produced by Kunneth. The inverse
linear equivalence calculation then reduces the required normalization equation
to the geometric generator formula. This scalar-total cycle argument is fully
proved in Lean, with no local sorry. Updated the item node's proof fields and
added the generator node with the full geometric proof plan.

The geometric source was read at the official Stacks pages:
[0BED](https://stacks.math.columbia.edu/tag/0BED),
[01FD](https://stacks.math.columbia.edu/tag/01FD),
[07MB](https://stacks.math.columbia.edu/tag/07MB), and
[0FKV](https://stacks.math.columbia.edu/tag/0FKV).
The source library, the recorded dependency signatures, and the reviewed analogous
left generator/comparison route were checked. LeanFinder and Loogle returned generic
or unrelated tools; grep found no matching geometric statement. LeanSearch returned
Internal Server Error, recorded as unavailable, not as an absence result.

## Proved and sorry left

Upper hole closed: `AlgebraicGeometry.Scheme.Modules.picardRightCechCup_homology`
(node `lem-sc-picard-right-cech-cup-homology`), 1 of 1 original sorries.
No sorry remains in the item's module.

Lower hole added: `AlgebraicGeometry.Scheme.Modules.picardRightCechCup_generators`
(node `lem-sc-picard-right-cech-cup-generators`), in the new module
`Sheaf.AlgebraicGeometry.PicardRightCechCupGenerators`.
Its proof is exactly `by sorry`; its docstring and node give the geometric proof.
This is a decomposition, not an axiom-clean proof or a net decrease in holes.
The existing tensor Kunneth and its dependencies are used without reproving them.

The new statement has no scalar-total homology object, comparison to that total,
or normalization on its cycles. It isolates the geometric Cech generator part;
the original module proves the passage to scalar-total cycle normalization using
Kunneth's cycle formula and injectivity of iCycles. It is the right-cover analogue
of the library's reviewed left-coefficient generator decomposition.

## No longer needed

No original import or geometric proof dependency is globally pruned.
The following old direct proof dependencies are transferred to the generator
node rather than used directly by the homology proof:
`lem-sc-cech-comparison-map-iso-affine`,
`lem-sc-cech-comparison-map-naturality`, `lem-sc-cech-comparison-natural`,
`lem-sc-picard-affine-diagonal-intersections`,
`lem-sc-picard-cech-cup-pullback-compat`,
`lem-sc-picard-right-cech-cup-construction`,
`lem-weil-pbc-fibre-product-affine-spectra`,
`lem-weil-pbc-module-pullback-quasi-coherent`, and
`lem-weil-pbc-quasi-coherent-tensor-product-affine-sections`.
The original geometric dependencies now belong to the new generator node's proof
plan; the item's direct proof dependencies are the generator node, scalar-model
support, and natural-index tensor Kunneth. The unit's realized statement and steps
are unchanged. The homology-map uniqueness theorem is not used by the new proof;
its public module still supplies the normalization predicate in the signature.

## Where the brief, the DAG or earlier work was wrong

The rejected arbitrary-isomorphism normalization lemma was false under independent
scalar rescaling of the product comparison. This delivery does not use it. The new
lemma chooses e and b together with their generator equation: multiplication by 2
on b alone is no longer a permissible change of witnesses. In degree zero with
singleton covers of Spec Q, the witnesses may be the canonical factor and product
comparisons and the equation is the usual section tensor pairing. Zero coefficients
and empty covering schemes give zero homology; no nonempty index or positive-degree
hypothesis is added. These are mathematical edge-case checks, not claimed Lean
encodings of those geometric examples.

The original two-step plan bundles the scalar restriction, natural/integer total
comparison, and generator cup compatibility without a declaration exposing the
result in the required scalar coordinates. The new node records that geometric
part explicitly; existing affine Cech and cup compatibility lemmas remain its proof
dependencies. The abstract Kunneth cycle argument is now implemented rather than
left in this bundled step.

The prior report's second-reading section belonged to the rejected attempt. It is
replaced here; this report does not claim a second reading of the new delivery.
The first dry run flagged an added scoped-notation command as an interface change.
Removed that command and used explicit TensorProduct.tmul in the proof. The item
then compiled again. No statement, definition, or interface change, forced
adaptation, or change record is needed.

## New nodes

`lem-sc-picard-right-cech-cup-generators`, in
`dag/nodes/sec-abelian-varieties/lem-sc-picard-right-cech-cup-generators.json`, states
the specified right-cover cup formula on pure factor homology tensors with compatible
Cech coordinates. Its module is
`lean/Sheaf/AlgebraicGeometry/PicardRightCechCupGenerators.lean`.
It carries its source, proof steps, actual search records, and verbatim Lean signature.
No change records.

## Second reading by E4

1. Compared the delivered homology module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; the only interface addition is the new proof-only module and its plain imports. Verdict: pass.

2. Compiled both delivered modules individually and with the sandbox import order using `lcompile.py --all`; compilation succeeds. The homology module has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow definition. The generator theorem is the single explicitly split-off `sorry`, named in its docstring and DAG node. Verdict: pass; scratch `#print axioms` checks for both delivered theorems show exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`, as expected for the open geometric generator theorem and existing open dependencies.

3. Reviewed the split-off generator statement against the Lean declaration and DAG node. It is strictly below the original target: it exposes only pure direct-sum generators and jointly chooses the comparison coordinates and formula, with no scalar-total cycles. Its source, proof plan, searches, docstring, and node are present; no duplicate library theorem was found. Independently searched using LeanFinder (cohomology comparison affine covering external multiplication tensor generators), Loogle (`"homologyMap"`), launcher grep (`external.*cup|cup.*comparison|Cech.*tensor`), and `rg` across Picard modules. Results are generic tools and the analogous left generator split, not this specified-right-cover result. Spot-checked Stacks 0BED and 0FKV: finite affine covers supply quasi-compactness and the cup comparison is the front/back construction. Edge cases (empty covers, zero coefficients, degree zero) are addressed in the proof documentation. Verdict: pass.

4. Checked the proof route from the target downward. The target uses the generator theorem and the existing tensor Kunneth cycle theorem; the cycle inclusion injectivity and inverse-equivalence calculation close the remaining normalization step. The imports are minimal for this proof and no old proof dependency is incorrectly removed; the unit `sk-prop-av-cube` remains realized. Verdict: pass.

5. Checked the DAG `proof`, `proof_deps`, and `proof_origin` against the Lean proof and verified the new node's `lean` record and statement text. The new node is recorded as a decomposition and the report lists the one hole closed and one hole added. Verdict: pass.

Changed during second reading: no mathematical or interface changes; made the transferred old direct proof dependencies explicit in No longer needed, corrected the description of the unchanged unit record, and appended this review record.
