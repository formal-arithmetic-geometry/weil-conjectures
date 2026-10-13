## What changed

Completed `AlgebraicGeometry.exists_homComplex_overEquiv_projections` in
`Sheaf.AlgebraicGeometry.HomComplexOverEquivProjections` without changing its signature or
existing docstring. The proof works from the specified product projections: product preservation
constructs the degree isomorphisms; the signed differential formula proves compatibility;
product extensionality proves naturality. The already proved generic calculation in
`HomComplexRestrictSchemeNaturalComponents` provided the local proof pattern, extended here to
retain the prescribed projection equations. Its private helpers are proved, and the private
specification definition is a genuine conjunction of properties, with no omitted data.

Added two proof-only imports: `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products` supplies
`isLimitFanMkObjOfIsLimit`, and `Mathlib.CategoryTheory.Linear.LinearFunctor` supplies the
integer-unit scalar compatibility used for the signed differential. The existing public import
of `OrdinaryEvaluationData` is retained. Scoped the larger heartbeat limits to the generic
calculation and its specialization, with explanatory comments; use transparent-definitional
checking settings matching the generic proof pattern.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.exists_homComplex_overEquiv_projections`.
Holes closed: 1. Holes added: 0. No `sorry` remains in the delivered module and no other
module is delivered. Both proposed split-off holes,
`AlgebraicGeometry.homComplex_overEquiv_projection_iso` and
`AlgebraicGeometry.homComplex_overEquiv_naturality`, were removed before delivery, together
with their unlanded node files. This is a complete proof, not a decomposition.

A scratch-copy `#print axioms AlgebraicGeometry.exists_homComplex_overEquiv_projections`
reports exactly `[propext, Classical.choice, Quot.sound]`. The scratch copy compiles without
warnings in 54.3 seconds. No forbidden declarations or omitted proofs occur.

## No longer needed

No repository import, old proof dependency, or library module is pruned. The sole original
proof dependency `lem-sc-hom-complex-projections` remains used directly. The proposed unlanded
nodes `lem-pc-hom-complex-over-equiv-projections-components` and
`lem-pc-hom-complex-over-equiv-projections-naturality` are no longer needed and are not delivered.
The initial unused private fan and differential helpers were replaced by the used, complete
generic construction. No dependency on the restriction-comparison module is introduced.

## Where the brief, the DAG or earlier work was wrong

The first worker's naturality theorem had a `True` premise instead of the required projection
compatibility premise. Arbitrary comparison isomorphisms need not be natural (even scalar
rescalings chosen independently at different complexes can destroy naturality). The first
worker's docstrings also lacked complete proofs and its new node records did not contain
verbatim Lean signatures or three independent searches. Rather than retain that defective
split, the second reading completed both obligations and removed the new declarations and nodes.
The first assembly closed one hole while adding two; that was decomposition, not net progress.
The original parent DAG proof plan was adequate after all and remains the actual proof route.

## Second reading by A4

1. Interface: compared the final module with the repository version and checked the existing
   target declaration's signature byte for byte with a script assertion. It is unchanged;
   no definitions used in its statement change. No other repository module is delivered.
   The existing target docstring is restored at the target declaration. Verdict: pass.

2. Proof: compiled the final proof in a scratch copy through `lcompile.py` and inspected
   `#print axioms`; only `propext`, `Classical.choice`, and `Quot.sound` occur. There are zero
   `sorry`s, no hollow definitions, and no forbidden declarations. Products are constructed
   by universal lifts, and any choice of the degree isomorphism is determined by its
   projection equations, so this does not choose arbitrary data from unproved existence.
   Verdict: pass.

3. Split statements: rejected the original unconditional naturality assertion and removed
   both split-off statements and their nodes after completing their arguments. No new public
   statements or new nodes remain. Fresh searches using `msearch.py` (LeanFinder, Loogle,
   and grep; recorded in `searches.jsonl`) and repository/upstream searches found the proved
   local generic construction in `HomComplexRestrictSchemeNaturalComponents`, which was reused
   as a proof pattern. Mathlib's product extensionality and component-isomorphism constructors
   are used. The zero-complex, empty-open, negative-degree, and unbounded cases require no
   extra hypothesis: the argument uses integer-indexed product universal properties and the
   sign unit, with no finiteness or nonzero assumption. Verdict: pass.

4. Route and pruning: opened `HomComplexProjections` and checked its three clauses (product
   limit, differential, and bifunctor maps) against the proof. Read the Hom-product and signed
   differential formulas at https://stacks.math.columbia.edu/tag/0A8X (section-hom-complexes).
   The construction keeps the actual chosen projections as explicit parameters; it does not
   replace them by unrelated projection choices. All added imports are proof-only and used.
   The old proof dependency remains necessary. The unit `sk-thm-picard-duality` has no realized
   node for this auxiliary comparison, and its unit record and route are unchanged.
   Verdict: pass.

5. DAG: the existing node's proof and `proof_deps` again describe the product, differential,
   and naturality argument actually implemented. Its `proof_origin` records the completed
   A4 second reading. The original statement, statement dependencies, Lean signature, unit,
   and chapter remain unchanged. The unlanded split-node files are absent. Verdict: pass.

Changed during second reading: rejected the faulty `True` premise; completed the product,
chain-map, and naturality arguments; removed both split-off holes and node files; restored
and synchronized the original proof route; replaced the warning-producing global heartbeat
option with scoped options; and rewrote the report to describe the verified final proof.
