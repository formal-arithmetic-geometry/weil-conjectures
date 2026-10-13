## What changed

The original signature of `AlgebraicGeometry.relativeMVInverseOpenIso_mate` is
unchanged. Its proof now combines the open coefficient transport on X',
coefficient naturality of base change, naturality of the direct-image composition
comparison, and horizontal pasting. All three added imports are proof-only.
Both original public imports are needed by the signature and remain public.

The second reader removed the earlier `relativeMVInverseOpenIso_mate_transpose`
restatement and its undelivered node. There are two new modules:
`Sheaf.AlgebraicGeometry.RelativeMVOpenCoefficientTransport` proves
`AlgebraicGeometry.relativeMV_open_coefficient_transport` by open-unit
compatibility and cancellation, and
`Sheaf.AlgebraicGeometry.DerivedBaseChangeHorizontal` states the remaining
horizontal pasting obligation. No existing definitions or statements changed.
Unchanged dependency copies used to populate the sandbox compilation overlay
were moved to scratchpad and are not delivered.

## Proved and sorry left

Closed the original local hole in
`AlgebraicGeometry.relativeMVInverseOpenIso_mate`.
Added one local hole:
`AlgebraicGeometry.schemeDerivedBaseChange_horizontal`, node
`lem-pc-derived-base-change-horizontal`.
The new `AlgebraicGeometry.relativeMV_open_coefficient_transport`, node
`lem-pc-relative-mv-open-coefficient-transport`, is proved without a local sorry.
The assigned module has no sorry. The horizontal theorem has the delivery's only
sorry, as the entire proof of a named public theorem with a source, proof
in words, and matching node.

This is a decomposition: one existing hole closed and one new hole added,
net zero holes closed. The original theorem still depends on `sorryAx` through
the horizontal pasting theorem. It is not claimed
as an axiom-free completed target. The new coefficient theorem contributes an axiom-checked proof of the
exact-to-pinned open comparison step: its `#print axioms` lists only
`propext`, `Classical.choice` and `Quot.sound`, with no `sorryAx`.

## No longer needed

No original import or module was pruned. Of the original node's `proof_deps`,
`lem-pc-ringed-spaces-derived-pullback-composition` and
`lem-weil-pbc-open-preimage-fibre-product` are no longer direct dependencies of
the upper proof. They remain dependencies of the horizontal or coefficient
steps, respectively. All five other original direct proof dependencies remain.
The undelivered transpose node and theorem are removed entirely; their merely
equivalent restatement is not part of the reduction.

## Where the brief, the DAG or earlier work was wrong

The earlier split applied an invertible Hom equivalence to both sides of the
whole target and then left the resulting equality sorry. This does not separate
any mathematical step and is refused as a restatement, regardless of whether
the tool's syntactic restatement heuristic detects it.

The earlier coefficient draft also missed the shorter route available from
`mvOpenBaseChange_unit` and `schemeDerivedOpen_unit_isIso`: invert the pulled-back
exact-open unit after restriction, compare precompositions into Rp, and cancel.
That route proves the coefficient statement instead of adding a second hole.

The repository's source for a dependency can precede its published compiled
artifact. Unchanged copies were compiled into the sandbox overlay through
lcompile.py, with no change delivered to those modules.

## New nodes

`lem-pc-derived-base-change-horizontal` records horizontal pasting for two
arbitrary commutative squares. It has no exact restriction, inverse-open
transport, coefficient map, or cartesian assumption. This is strictly the
pasting step of the original mate argument, and remains open. Its complete
counit/triangle/coherence proof is in its docstring and node.

`lem-pc-relative-mv-open-coefficient-transport` records the now-proved comparison
on X', before applying any further direct image to a base. Its statement has no
f, f', or second base-change g. Its proof uses existing open-unit theorems,
adjunction uniqueness and cancellation. Neither new node changes a unit's route.
No change record is needed: existing signatures, definitions, and visibility
are unchanged.

## Second reading by T4

1. **Interfaces: pass after repair.** Compared every existing sandbox module
   with the repository by diff. The only delivered existing module changes
   proof text and adds three plain imports. Independently checked that the
   original theorem signature is byte-for-byte identical. There is no added
   hypothesis, changed conclusion, changed definition, or public-import change.
   The unchanged inverse-open module and other compile-only dependency copies
   were excluded from the delivery.

2. **Proof and trust: pass as a decomposition.** Compiled the delivered modules
   individually through lcompile.py, in dependency order. Checked the source for
   forbidden declarations and for hidden proof holes. The only remaining local
   sorry is the entire named horizontal pasting theorem. Checked `#print axioms`
   for both new public theorems and the original theorem, and the delivery tool's
   full declaration probe: the coefficient theorem uses only `propext`, `Classical.choice` and
   `Quot.sound`; the horizontal theorem and original theorem additionally use
   `sorryAx` from the recorded horizontal obligation. There are no new definitions or arbitrary witnesses.

3. **Intermediate statements: pass after removing the restatement.** The
   previous transpose statement was equivalent to the entire target and was
   removed. Horizontal pasting is the two-square counit calculation, with
   canonical adjunction and composition comparisons; the coefficient transport
   is only the open comparison on X'. Empty and full opens, zero complexes and
   zero coefficient maps require no new hypotheses; horizontal pasting also
   works for identity arrows and noncartesian squares. Its proof consists of
   naturality, triangles and the pinned associativity laws. Read Stacks
   [08HY](https://stacks.math.columbia.edu/tag/08HY),
   [0D5S](https://stacks.math.columbia.edu/tag/0D5S), and
   [08HZ](https://stacks.math.columbia.edu/tag/08HZ).
   Ran independent leanfinder, loogle and grep searches, logged by msearch.py.
   Mathlib's `mateEquiv_hcomp` supplies generic pasting, but does not identify
   these pinned scheme composition comparisons in one application. Repository
   searches also found `schemeDerivedBaseChange_pasting`, whose statement adds
   an upper-left morphism to one square, not the two-square law needed here.
   No existing exact horizontal or coefficient theorem was found.

4. **Route and pruning: pass after a shorter coefficient proof.** Replaced the
   draft's long coherence calculation by proved open-unit compatibility and
   injective precomposition, and wrote the real upper reduction. Every import
   is used; new proof-only imports are plain imports. The two old direct DAG
   dependencies replaced by lower steps are listed above; no modules are
   claimed pruned. The unit `sk-thm-picard-semicon` has empty realized entries
   and this item is a below-unit comparison step; its unit and chapter route
   are unchanged.

5. **Nodes: pass after repair.** Rewrote the original node's proof, proof_deps
   and proof_origin to follow the coefficient/naturality/pasting reduction.
   Both new nodes carry their exact Lean signatures, source and complete
   natural-language argument, union of proof-step uses, all required search kinds, with LeanSearch recorded as unavailable,
   creation and blueprint provenance, chapter and unit. The discarded transpose
   node is absent. The new coefficient node records a proved theorem; the
   horizontal node records the sole remaining named obligation.

The first dry run caught missing LeanSearch metadata: leanfinder and Loogle
count as one search kind. Ran LeanSearch for both new nodes and recorded the
service failure as unavailable; the successful searches remain recorded.

Second reading changed the equivalent transpose split into an actual reduction,
proved the open coefficient comparison, made all new proof imports private to
proofs, updated the DAG and hole accounting, and excluded unchanged dependency
sources from delivery.
