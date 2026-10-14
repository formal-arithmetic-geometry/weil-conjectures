## What changed

Preserved the exact signature of `AlgebraicGeometry.schemeOrdinaryEvaluation_chain_action`.
Its complete proof compares two canonical formulas on each triple tensor summand,
then uses chain-map and total-tensor coproduct extensionality. A proved private
helper establishes this extensionality over abstract complexes and rewrites triple
inclusions as successive inclusions using category associativity.

Added two component normalization modules, imported only for the proof:
`SchemeOrdinaryEvaluationTripleComponent` and `SchemeCanonicalTensorUnitComponent`.
The first uncurries the ordinary component equation and moves the augmentation last.
The second combines coefficient cancellation with the generic tensor-unit component
calculation. Each is a genuine part of the argument, has a complete proof in words,
and has its own DAG node. The parent's node records the route actually used.
No existing statement, definition, visibility, or target changes.

## Proved and sorry left

Closed `AlgebraicGeometry.schemeOrdinaryEvaluation_chain_action`, one of one original
holes. Its module has no remaining `sorry`; the private helper is also fully proved.

Two new holes remain, each with proof exactly `:= by sorry`:

- `AlgebraicGeometry.schemeOrdinaryEvaluation_triple_component`, node
  `lem-pc-scheme-ordinary-evaluation-triple-component`.
- `AlgebraicGeometry.schemeCanonicalTensorUnit_component`, node
  `lem-pc-scheme-canonical-tensor-unit-component`.

This is a decomposition: one original hole closed and two strictly smaller holes
added. The ordinary component lemma has no factor map `e` or coefficient
factorization hypothesis. The tensor-unit lemma has no ordinary map `f` or ordinary
component predicate. Each gives only one summand's normalization formula; the main
module supplies the actual combination and global extensionality argument.

## No longer needed

No original dependency module becomes unreachable, and no original public import
is removed. The projection, tensor-Hom, ordinary-component, uncurrying and tensor
unit APIs are still required by the two new steps. The parent's old direct proof dependencies no longer used directly are
`def-pc-scheme-ordinary-evaluation-formula`, `def-pc-scheme-tensor-unit-action`,
`lem-pc-tensor-hom-uncurry-differential`, and `lem-sc-hom-complex-projections`.
All four remain dependencies of the new component lemmas; their modules remain
reachable, and the first three parent imports are required by its signature. No blueprint unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement was found false and no existing interface was changed. The two prose
steps need explicit component normalization interfaces; these new statements
supply them without adding boundedness, flatness, or existence assumptions.
Edge cases checked in the statements and proof plans include arbitrary and negative
integer degrees, zero complexes, zero maps, and the empty scheme.

The local literature checkout named in the source records was unavailable. The
cited Stacks Project tags 08DJ, 08DM and 08DQ were read on the Stacks Project website.
Large coproduct elaborations are confined to a private helper over abstract
complexes; the proof uses component APIs rather than unfolding evaluation data.

## New nodes

`lem-pc-scheme-ordinary-evaluation-triple-component` records source and coefficient
naturality, inverse tensor-Hom and symmetry laws, and the two degree-sum cases for
ordinary evaluation. It contains no coefficient factorization assumption or `e`.

`lem-pc-scheme-canonical-tensor-unit-component` records degreewise augmentation
cancellation, coefficient identification, total associator and tensor-map
naturality, and the single-unit right unitor calculation. It contains no ordinary
map `f` or predicate `hf`. These are combined as one step to avoid duplicating
coefficient calculations across independent component interfaces.

Both nodes belong to `sec-picard-framework`, unit `sk-thm-picard-duality`.
There are no change records or forced adaptations.


## Second reading by T3

1. Compared every delivered module with the repository. Only the parent module
   previously exists. Its existing theorem signature and docstring are byte for
   byte unchanged; the diff adds two plain proof imports, a private proved
   extensionality helper, and replaces the original sorry. No definitions or
   public visibility changed, and no change record is required. Verdict: pass.
2. All three modules compile locally in dependency order without warnings or
   errors (13.8, 13.5 and 23.4 seconds). Scanned every delivered file: precisely
   the two reported named theorem sorries remain; there are no forbidden trust
   declarations and no new definitions. The scratch axiom check and delivery
   probe check the three public theorems and private helper; sorryAx is expected
   from the two open components and existing dependencies. Verdict: pass.
3. Read each component formula against IsSchemeOrdinaryEvaluation,
   schemeTensorHomUncurry_component, projection naturality, tensorHomEquiv,
   and the explicit schemeTensorUnitAction. In the zero degree-sum branch,
   p+q=n and n+r=k imply p=k; in the other branch the single coefficient is zero.
   Zero complexes/maps, negative degrees, and the empty scheme introduce no
   exceptions. The coefficient cancellation uses the degreewise monomorphic
   K-injective augmentation. Each lemma isolates one side of the argument and
   omits the other side's map/hypothesis; neither restates the parent. Both have
   source, full prose proof, and matching nodes. Independent LeanFinder, Loogle,
   Mathlib grep and repository searches found component naturality and standard
   associator/unitor APIs, but no duplicate of either formula. The existing
   component-naturality theorem concerns maps between resolved targets and does
   not directly give augmentation from an unresolved coefficient. Neither open
   formula has a short one-lemma proof. Verdict: pass as a decomposition.
4. Read the proof from the parent down. The helper uses Mathlib triple tensor
   coproduct extensionality and inclusion reindexing, followed by chain-map
   extensionality. The parent genuinely combines two component equalities.
   All public imports supply its signature; new imports are plain proof imports.
   No old dependency module becomes unreachable. The unit record
   sk-thm-picard-duality has empty realized statement and step lists, and this
   delivery changes neither it nor any unit route. Verdict: pass.
5. Compared the parent node with its old version: only proof, proof_deps and
   proof_origin change. Checked proof_deps equals the union of step uses and
   each new node's full Lean statement matches its declaration. Source, searches,
   creation, blueprint, chapter, unit and Lean records are present. Verdict: pass.

Second reading changed only this report: completed the explicit list of old
parent proof dependencies no longer used directly and recorded the independent
review. Lean statements and proofs were retained.
