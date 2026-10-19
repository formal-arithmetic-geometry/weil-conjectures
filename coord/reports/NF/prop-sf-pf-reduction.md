## Worker report

The module `Sheaf.Paper.ProjectionFiniteReduction` states the finite-coefficient
projection-formula reduction proposition. It uses the positive-level convention
`A_{E,r+1}`: `m ≤ n` is rendered by `Nat.succ_le_succ h`, and the quotient map is
`PurCompactSupport.finiteQuotientChange` from level `n+1` to `m+1`.

The theorem binds a finite-field datum `D`, coefficient datum `C`, field `E` with its
Padic algebra and finite-dimensionality, levels `m,n` and `h : m ≤ n`, a six-functor
datum at level `n+1`, finite-type objects `X,Y` in `SixFunctorSpace D`, separatedness
instances, a morphism `f`, a compactification `c`, finite-derived objects `K,L`, and
finite-Tor hypotheses `_hK` and `_hL`. The first conjunct is the commuting square:
its upper arrow is `finiteReductionProjection` followed by coefficient extension on
`Y` and `finiteProjectionReductionTarget`; its left arrow is
`finiteProjectionReductionSource`; its lower arrow is `finiteReductionProjection`
at level `m` on the coefficient-extended `K,L`. The second conjunct is the exact
`IsIso` equivalence for these two projection arrows.

The helper definitions are real canonical constructions. `finiteReductionProjection`
uses `PurCompactSupport.projectionMap` and the normalized finite tensor models.
`finiteProjectionReductionSource` uses `PurCompactSupport.scalarTensor` and the
compact-support coefficient comparison. `finiteProjectionReductionTarget` uses the
same comparison, the compact-support image map, scalar tensor, and
`PurCompactSupport.scalarPull`. No comparison map is chosen by `sorry`.

Dependency declarations used include:

- `Sheaf.Paper.SixFunctorDatum`, `WeilConjectures.SixFunctorDatum`;
- `Sheaf.Paper.SixFunctorDualNotation`, `WeilConjectures.SixFunctorDatum.finiteCoefficientDual`;
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`,
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`;
- `Sheaf.Paper.BasicOperationsCoefficientReduction`,
  `WeilConjectures.basicOperationsCoefficientReduction`;
- `Sheaf.Paper.EtaleCompactSupportCoefficientChange`,
  `AlgebraicGeometry.Etale.compactSupportCoefficientComparisonPlus`;
- `Sheaf.Paper.IntegralCompactSupportCoefficientData`,
  `WeilConjectures.PurCompactSupport.finite`, `finiteQuotientChange`, `comparison`,
  `scalarTensor`, `scalarPull`, `image`, and `projectionMap`;
- `Sheaf.Paper.FinitePullbackTensorComparison`,
  `WeilConjectures.pullbackTensorFiniteModel`;
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison`,
  `proEtaleConstantRingCompositeCoefficients_eq`.

The proof dependencies named by the node are imported as stated modules, including the
constructible-origin, Tor-amplitude, flat-model, Nagata, open-extension, ringed exchange,
and finite projection-formula interfaces. The only postponed proof is the named
`projectionFiniteReduction` theorem, whose proof is `sorry` as required for stage 2.

Edge cases checked before writing include `m = n` (identity quotient), zero objects
`K = 0` or `L = 0`, an empty scheme, and the permitted nonflat quotient. The
construction keeps the source's separated finite-type setting and does not impose
flatness of the reduction map.

Searches made: `msearch.py ... leanfinder` for projection formula and finite reduction
found no matching theorem; `msearch.py ... loogle "projectionFormula, IsIso"` found no
hits (the identifier was unknown); `rg` over `lean/WeilConjectures` and `lean/Sheaf`
found the related upstream reduction square and the canonical finite reduction and
projection declarations, which are used above. The DAG search found no existing
`prop-sf-pf-reduction` Lean declaration. The module was compiled with
`scompile.py NF prop-sf-pf-reduction` successfully, with no warnings.

## Second reading by NF

No independent second worker was used: the dispatched brief prohibits starting other
agents and assigns independent review to the maintainer. The author reread the node
and file, matching the datum, finite-type spaces, separated morphism, positive levels,
finite-Tor inputs, specified reduction square, and original-map IsIso equivalence.

## Delivery preflight failure

The server dry run compiled the module successfully and pushed nothing, but rejected
the unchanged base DAG with:

`(b) incremental DAG validation: cycles: prop-sf-pf-reduction -> det-sp-reduction-direct-image reaches prop-sf-pf-reduction`

The complete existing cycle is `prop-sf-pf-reduction` →
`det-sp-reduction-direct-image` → `det-sp-tower-bound-uniform` →
`det-sp-tower-shriek-levels` → `sk-thm-sf-pf-proetale` → `thm-sf-pf-adic` →
`prop-sf-pf-reduction`. Every edge is present in the read-only base. The sandbox
item is identical to the base outside `lean`. Repairing a dependency's `lean`
record cannot remove these edges. The stage-2 scope permits neither changing the
other nodes' proof dependencies nor deleting the item's existing proof dependency
without a source-based statement correction; the proposition's statement needs no
such correction. The delivery wrapper expressly rejects removal of base
`proof_deps`. No launcher or preflight tool was modified or bypassed.

## Resumed delivery audit, 2026-10-20

The required initial resumed dry run of `deliver2.py NF prop-sf-pf-reduction
--no-push` compiled the saved module and failed with exactly the inherited-cycle
diagnostic above. Nothing was pushed. The saved Lean and node record were retained.

I checked all six cycle nodes in the read-only published DAG. Each displayed edge
is an existing statement or proof dependency; none is introduced by this packet.
The dependency `det-sp-reduction-direct-image` already has its canonical comparison
and isomorphism recorded in `Sheaf.SecSmoothPurity.ReductionDirectImage`. Replacing
that Lean interface under section 1(B) cannot remove its graph edges: dependency
packets change only `lean`, preserving their statement and proof dependencies.

The gate's implementation confirms the obstruction: `tools/nt_incremental2.py`
rejects every existing cycle through a delivered node, and
`tools/test_nt_preflight2_graph.py` explicitly tests both
`test_inherited_cycle_through_touched_node_still_blocks` and
`test_lean_only_dependency_repair_preserves_current_edges`. No gate or test was run
or modified on this machine; these files were read for diagnosis only.

The prescribed delivery wrapper refuses dropping existing item `proof_deps`
without a statement correction. Moreover `tools/node_fields.py` rejects a changed
proof or proof-dependency list when the mathematical statement is unchanged.
The source proposition needs no source-based correction that would force removal
of this edge. A cosmetic statement change solely to unlock a proof rewrite would
not satisfy section 1(C). New definitions or dependency Lean repairs also cannot
break existing graph paths. Thus the unchanged graph requires an upstream proof
DAG repair, beyond the permitted stage-2 packet fields. The exact tool failure is
the prescribed preflight refusing this compiling, Lean-only packet because of the
existing cycle; the sandbox and all launcher tools remain intact.

## Latest resumed dry run, 2026-10-20

The prescribed `deliver2.py NF prop-sf-pf-reduction --no-push` completed normally
and again returned `PREFLIGHT FAILED, nothing pushed`, with its sole reason:
`(b) incremental DAG validation: cycles: prop-sf-pf-reduction -> det-sp-reduction-direct-image reaches prop-sf-pf-reduction`.
No interrupted delivery remains pending. A fresh JSON comparison confirms that the
saved item differs from the current read-only base only in `lean`. All six edges
of the cycle reported above are still present in the current base. Section 1(B)
and section 5 of the standing stage-2 brief permit dependency repairs only in
`lean`; section 1(C) permits proof-edge changes only as forced by a source-based
statement correction. Neither authorizes deleting this pre-existing cycle from
this unchanged-statement delivery. The packet is retained; no push was attempted
after the failed dry run, and no tool was modified or bypassed.

## Dispatcher retry verification, 2026-10-20

Started this retry with the retained packet and the prescribed dry run, rather than
rewriting it. `deliver2.py NF prop-sf-pf-reduction --no-push` compiled the sandbox
and library module successfully, then exited 1 with exactly one preflight reason:
`(b) incremental DAG validation: cycles: prop-sf-pf-reduction -> det-sp-reduction-direct-image reaches prop-sf-pf-reduction`.
The tool reported `PREFLIGHT FAILED, nothing pushed`.

A fresh comparison with the current read-only node again found only `lean` changed.
A fresh audit of the six cycle edges confirmed that each remains in the base DAG,
including the statement dependency from `det-sp-tower-bound-uniform` to
`det-sp-tower-shriek-levels`; no edge is introduced by this packet. The resolved
stage-1 repair note explicitly requires keeping this item's statement unchanged.
No source-based statement defect was found that would authorize a section 1(C)
proof-edge change. Section 1(B) dependency repairs preserve graph fields, so cannot
repair this inherited cycle. The packet is retained. No forbidden graph edit,
launcher-tool modification, preflight bypass, or push was attempted.
