## What changed

Completed the proof of `AlgebraicGeometry.singleComplexBaseChangeCriterion` using the inherited
single-complex stalk condition, quasi-coherent closure of derived tensor and pullback, and the
qcqs induction theorem. The proof also uses the canonical tensor-comparison realization bridge.
The realization bridge could not be compiled from its lengthy transport proof within this item, so
it is retained as a named public theorem with a documented proof plan and a matching DAG node.

Added the proof-only imports needed for complex quasi-coherence, derived tensor QCoh closure,
derived pullback tensor QCoh closure, and the canonical realization bridge.

## Proved and sorry left

Closed one local hole: `AlgebraicGeometry.singleComplexBaseChangeCriterion` in the item module.
Added one lower hole, so this is a decomposition with net zero holes closed, not an axiom-free proof.
The added theorem `AlgebraicGeometry.canonicalPullbackTensor_monoidal_realization` remains `sorry`
as a strictly lower intermediate result, with node `lem-pc-canonical-pullback-tensor-monoidal-realization`.
The existing imported declarations `singleComplexInheritedTensorCondition` and
`singleComplexBaseChangeQcqsInduction` remain their upstream named holes.

## No longer needed

No imports or DAG nodes from the prior proof plan were removed. The canonical realization theorem
is the only additional bridge required by the written proof; unrelated modules are not imported.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt included a full transport proof for the canonical realization bridge, but that
proof currently fails in its own module at a type mismatch between `Scheme.Modules.tensorPullback`
and the sheaf-module functor after rewriting the transported counit. This delivery isolates that
failure as a lower theorem rather than leaving a partial proof. The target statement and all existing
signatures are unchanged.

## New nodes

`lem-pc-canonical-pullback-tensor-monoidal-realization` records the lower theorem, its Stacks
source, proof plan, searches, and Lean declaration. Its change is included in the sandbox DAG copy.

The dry run accepts the first-reader handoff without a second-reading section.
Both modules compile; the second reader owns the independent review and delivery.

## Second reading by H1

1. **Signatures and accidental changes: PASS.** Compared the delivered criterion module with the repository version. The target theorem signature and all existing declarations are byte for byte unchanged. The only added declaration is the separately documented lower theorem and its matching node.

2. **Compilation and axioms: PASS.** Compiled both sandbox modules with `lcompile.py --all`; both compile without errors. The criterion proof contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The isolated lower theorem is the sole intentional `sorry` and is named in the report and node.

3. **Statements and lower split: PASS.** The lower theorem is a genuine realization result needed to turn the canonical comparison into a monoidal structure, strictly smaller than the criterion. Its statement is unchanged from the delivered node, has a source and complete proof plan, and is not duplicated elsewhere. Its existential data is used only through the displayed tensorator equalities.

4. **Route and pruning: PASS.** The proof follows the inherited tensor condition and qcqs induction route, establishes quasi-coherence from the actual complex and pullback, and uses the canonical realization bridge. All added imports are proof-only imports; no unused public import was introduced. The unit route and its realized nodes are unchanged.

5. **DAG agreement: PASS.** The criterion node's proof and dependencies match the calls in the Lean proof. The new realization node has matching Lean and JSON statements, source, proof dependencies, proof origin, creation metadata, chapter, and unit. No statement change or forced adaptation is present.

Second-reading changes: appended this review only. No theorem signatures, definitions, or DAG statements were changed.
