## What changed

Replaced the rejected earlier attempt with a genuine reduction. The item's sole
original hole, `ModuleCat.localizedTensorComparisonProperty_shift_component`, now
constructs the inverse-shift representative isomorphism, proves K-flatness of that
representative using Mathlib, applies the original hypothesis in degree `i+n`, and
uses an explicit conjugacy equality to conclude invertibility. Existing signatures
and public imports are unchanged. The new proof-only import is
`Sheaf.Algebra.Homology.LocalizedTensorComparisonShiftSquare`.

The new module states one transport theorem about the actual comparison arrows.
It assumes neither the property at X nor invertibility of any comparison. It gives
a model of the explicit inverse-shift complex, source and target isomorphisms,
and an equality of morphisms. The source complex is fixed, not an existentially
selected representative. The existential model is used only inside a proposition
proof; no definition selects data from an unproved existence statement.

The component node's proof and dependencies now follow the written Lean argument.
The top theorem and its node remain unchanged. No other library module is adapted.

## Proved and sorry left

Original hole closed: `ModuleCat.localizedTensorComparisonProperty_shift_component`
(node `lem-pc-localized-tensor-comparison-shift-component`). Its entire combining
proof compiles with no remaining hole. The already proved
`ModuleCat.localizedTensorComparisonProperty_shift` remains proved unchanged.

Hole added: `ModuleCat.exists_localizedTensorComparison_shift_square`
(node `lem-pc-localized-tensor-comparison-shift-square`), the sole `sorry` in this
sandbox's Lean modules. Its proof is exactly `by sorry`, with the model transport
construction and comparison-square proof detailed in its docstring and node.

This delivery closes one original hole and adds one strictly lower transport
obligation: it is a decomposition, with zero net holes removed, not a complete
proof of the mathematical shift stability result. In particular, the derived
counit shift comparison and its compatibility with the recorded E-module action
remain to be formalized in the new item. The representative and K-flat transport
are already proved directly in this delivery and are not left to that new item.

## No longer needed

No original library import, node or module is pruned. The original property
import remains necessary to state the component and apply hX. Its model import
remains necessary to state and transport the comparison arrows.

The earlier sandbox-only `LocalizedTensorComparisonShiftAllModels` module and
`lem-pc-localized-tensor-comparison-shift-all-models` node were removed; they were
never library dependencies and are not counted as library pruning. The discarded
all-model statement was merely a restatement of the component obligation.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt incorrectly characterized an all-model restatement as a
reduction. The replacement separates a comparison-square identity from the
application of hX and the proofs of the representative/K-flat hypotheses.

The original component node described tensor/model transport but exposed no
usable transport lemma. Searches of Sheaf, WeilConjectures and Mathlib found
first-variable tensor shift, second-variable tensor shift and cohomology shift
isomorphisms, but no theorem giving the square for the specialized recorded
base-derived tensor model. LeanFinder returned derived adjunction and exact
functor results; Loogle returned the tensor shift ingredients; LeanSearch was
unavailable (Internal Server Error), which is not evidence of absence.

The degree is checked explicitly: H^(i+n)(U[-n]) is H^i(U). For n=0 the new
square uses the canonical zero-shift identifications. Zero complexes and t=0
give the same conjugacy equation; no invertibility is asserted in the transport
lemma. Positive and negative shifts are included. Neither K-flatness of Q,
flatness of C, nor boundedness is silently added.

The unit `sk-thm-picard-semicon` has empty realized statement/step lists; no unit
route is bypassed. The existing signatures, including universe binders, stay
identical.

The source files are not installed on this machine. The existing cited sources
were read at https://stacks.math.columbia.edu/tag/0DJA and
https://stacks.math.columbia.edu/tag/0BYJ. The detailed transport proof is marked
as agent-written, since those tags do not themselves state this Lean model's
shift square. WANTED: the repository's literature/stacks-project/perfect.tex
(Tag 0DJA) and more-algebra.tex (Tag 0BYJ), for the new transport node.

## New nodes

`lem-pc-localized-tensor-comparison-shift-square` in
`dag/nodes/sec-picard-framework/` records
`ModuleCat.exists_localizedTensorComparison_shift_square` in the new module
`Sheaf.Algebra.Homology.LocalizedTensorComparisonShiftSquare`. It isolates model
and arrow transport without a property-at-X or invertibility hypothesis. Its
proof describes reindexing the cohomology action, retaining the universal derived
functor, constructing the comparison via its counit, localizing via adjunction,
and using naturality to obtain the displayed conjugacy. The three kinds of
Mathlib search are recorded, including the unavailable LeanSearch service.
No definition/interface change record is necessary.

## Second reading by S3

1. I compared `LocalizedTensorComparisonShift.lean` with the repository version. Existing
   declaration signatures are unchanged byte for byte; the added import is proof-only and the
   new square theorem is recorded as a separate node.
2. Both sandbox modules compile with `lcompile.py --all`. The only remaining `sorry` is the
   named theorem `ModuleCat.exists_localizedTensorComparison_shift_square`; there are no
   definitions containing `sorry`, axioms, unsafe declarations, or forbidden implementation
   directives. The component proof is closed and uses only the permitted library axioms apart
   from the explicitly open square theorem.
3. The split-off square statement is a genuine transport obligation: it has no property or
   invertibility hypothesis, fixes the shifted model's source, and states the precise conjugacy
   equality required by the component proof. Its edge cases (zero shift, zero complexes, and
   zero map) are covered by the stated naturality argument. Searches recorded in the node and
   `searches.jsonl` found no existing declaration duplicating it.
4. The component proof follows the shortest available route: inverse-shift the representative,
   transport K-flatness with Mathlib shift isomorphisms, apply the original property in degree
   `i+n`, and rewrite by the square. The proof-only import is used; no unused import or old
   proof dependency was removed. The unit route and existing realized nodes remain intact.
5. DAG proof steps and dependencies match the Lean proof, and the new square node contains the
   required source, statement, proof plan, searches, and Lean record. I changed only the report
   by adding this review section; no Lean statement or definition was changed during review.
