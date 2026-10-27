## What changed

Reduced `WeilConjectures.PurStrictScalar.scalar_clopen_projection` to the normalized
open-adjunction unit equation `WeilConjectures.PurStrictScalar.strictScalarOpenUnit`
in the new proof-only import `Sheaf.Paper.StrictScalarOpenUnit`.

The parent contains a complete categorical proof: naturality of the pullback/tensor
comparison, the two `pi_components` equations, the scalar/open unit equation, and
naturality of the target open unit identify the pullbacks. The clopen `openToR`
isomorphism and the geometric adjunction Hom bijection then recover equality of the
original maps. This is a real reduction from the clopen projection to its open-unit
normalization; it does not test equality after finite evaluation. The lower lemma imports only `ConstantScalarTowerMates` and the strict geometric
arrows. Its pullback comparison is displayed as the existing `leftAdjointUniq`
defining term of `strictScalarPull`, so its statement is definitionally the same
open-unit identity. All existing public statements, definitions, visibility, and
public imports are preserved. The main
refinement and coherence proofs are retained verbatim.

## Proved and sorry left

Original module: three holes. One is closed by a decomposition, and two remain.
Closed: `WeilConjectures.PurStrictScalar.scalar_clopen_projection`.

Remaining original holes, both attached to
`lem-pur-compact-support-strict-scalar-refinement`:

- `WeilConjectures.PurStrictScalar.scalar_properOpen_alpha`.
- `WeilConjectures.PurStrictScalar.scalar_compactification_composition`.

Added one lower hole:
`WeilConjectures.PurStrictScalar.strictScalarOpenUnit`, attached to
`lem-pur-strict-scalar-open-unit`. This statement only concerns the open unit;
it contains neither a clopen projector nor a compactification. The argument
recovering the projector from it is proved in the parent. Net holes closed: zero;
this delivery is a decomposition, not an unconditional proof of the scalar square.
No definition contains a hole and no axiom is introduced.

Profiling confirmed that the new unit statement elaborates in under a second;
the parent cumulative declaration work is well within the single-file limit.
All development profiling options have been removed. Final compilation and
preflight are run by the required delivery tool.

## No longer needed

No original import, node, module, or unit-route step is withdrawn. The new lower
module does not need the broad `CompactSupportStrictScalarMate` import: the
underlying `ConstantScalarTowerMates` definitions suffice. Its node therefore
cites those definitions rather than the broad scalar-mate theorem, which also
bundles native compact-support dependencies. The
existing restriction-square dependency remains necessary for the main refinement
proof, and the original proper/open alpha and composition assertions remain present.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The first preflight rejected the new node's broad
scalar-mate dependency because that node reaches this refinement node through
native compact-support model dependencies. The open-unit calculation uses none
of those models. Its source now displays the scalar pullback comparison's defining
adjunction-uniqueness term and imports the underlying constant-tower definitions;
the node records exactly those dependencies, with no return path to the parent. The assigned module currently exists in `lean/`
and its original source compiled successfully in 26.5 seconds, despite the older
rework row referring to a quarantined dependency chain. The archive and Lean
attachments were preserved.

The new proof separates the open-unit normalization from the clopen projection
calculation. The precise remaining work is to identify the published geometric
`strictScalarPull`, which uses the whole-complex normalized proper restriction
comparison, with the sectionwise coefficient pullback comparison. Merely invoking
finite evaluation or saying that scalar extension preserves sections would not
justify this normalization. The new theorem's docstring and node retain that work.

## New nodes

`lem-pur-strict-scalar-open-unit` records the scalar/open unit equation from
auxiliary refinement Steps 3--4, supported by Stacks 0E8I and 07A6. It applies to
arbitrary open immersions and strict derived towers. Empty and identity opens,
the zero object, and identity coefficient extension all give the corresponding
unit identity; no closedness, Tor, constructibility or uniform-bound hypothesis
is introduced. LeanSearch, Loogle, LeanFinder and Mathlib/repository searches found generic
mate and scalar counit lemmas, but no theorem identifying these published strict
tower comparisons. The parent node now cites the new node in its clopen step.
There is no shared definition change and no change record is required.

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
