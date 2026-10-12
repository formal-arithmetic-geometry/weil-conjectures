## What changed

Proved `AlgebraicGeometry.Scheme.FiniteEtale.exists_neighbourhood_comparison_of_stalk`
in `Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleStalkComparisonDescent`, with its
signature and public imports unchanged. All new helpers are private and proved.
The proof constructs the cofiltered affine neighbourhood system inside W, proves
its stalk-overlap cone limiting by initial restriction and cartesian cone squares,
proves affine transitions and qcqs stages, applies the existing proved
`AlgebraicGeometry.exists_iso_of_isPullback`, and transports its isomorphism to
finite etale covers and the exact iterated pullback in the conclusion.

The argument follows [Stacks Tag 0BQ5](https://stacks.math.columbia.edu/tag/0BQ5)
and [Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM), parts (2) and (3).
Updated the existing node's proof, proof_deps and proof_origin to describe this
implementation. No statements, definitions used by targets, or interfaces changed;
no forced adaptations or change records are needed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.FiniteEtale.exists_neighbourhood_comparison_of_stalk`
(blueprint: `lem-sbc-finite-etale-stalk-comparison-descent`).
No holes remain in this module and no holes were added or split off.
The proof is complete, not a decomposition into new deferred lemmas.

The single-file compile passes without warnings (about four seconds).
`#print axioms` for the theorem reports exactly `propext`, `Classical.choice`,
and `Quot.sound`; it has no reachable `sorryAx`.
The empty-overlap case is included: the system of neighbourhoods is nonempty,
while its overlap schemes and covers may be empty. Neither the cartesian-limit
proof nor the descent theorem requires those schemes to be nonempty.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.FibreProductLimit`.
Its node `lem-kun-fibre-product-limits` is no longer a proof dependency of this item:
the explicit cartesian-cone proof uses Mathlib's
`CategoryTheory.Limits.isLimitOfIsPullbackOfIsConnected` directly.
No other original imports or proof-dependency nodes were removed.
The retained dependencies are `lem-weil-pbc-local-ring-spec-limit-affine-neighbourhoods`,
`lem-weil-pbc-open-fibre-product` (Mathlib open-intersection cartesian squares), and
`thm-pd-spreading-out` (the proved finite-presentation comparison-descent corollary).
This reports pruning from this item's proof, not a claim that no other target branch
uses FibreProductLimit. The unit `sk-prop-input-spreading` and its route are retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The planned separate descent of maps and
inverse equations is already proved by `AlgebraicGeometry.exists_iso_of_isPullback`
in the planned finite-presentation-descent module. It can be used directly.
The generic Sheaf fibre-product-limit comparison module was unnecessary: an explicit
cartesian-cone limit proof suffices and identifies the projections required here.

## Second reading by H2

1. Compared the delivered Lean module with the repository using diff and checked
   the existing theorem signature byte for byte by extraction through `:= by`.
   Verdict: unchanged hypotheses, conclusion and visibility. No existing definition
   changes, new public declarations, or change records. The added helpers are private.
2. Independently compiled the module with lcompile.py: exit 0, no warnings.
   Compiled a scratch copy with `#print axioms` for
   `AlgebraicGeometry.Scheme.FiniteEtale.exists_neighbourhood_comparison_of_stalk`:
   exactly `propext`, `Classical.choice`, `Quot.sound`, no `sorryAx`.
   Read all helper bodies: no sorry, forbidden declaration, or hollow definition.
   The only chosen data in a definition is the unique factorization supplied by the
   proved stalk-limit theorem, so it satisfies the construction rule.
3. No statements were split off and no holes were added. Reviewed the private
   finiteEtale_stageIso reduction against exists_iso_of_isPullback, including the
   structure-map equations used to lift the scheme isomorphism. Empty U, empty C,
   empty local overlaps, and s in U are allowed: neighbourhood nonemptiness comes
   only from hsW and the affine basis; overlap nonemptiness is never assumed.
   Verdict: genuine proof of the original statement, no restatement hole.
4. Searched again with leanfinder for isomorphism descent for finite-presentation
   schemes over cofiltered limits, and searched lean/ with limit, iso, comparison,
   and stalk terminology. No shorter ready theorem for this entire local-overlap
   statement was found. The proof already uses the proved upstream isomorphism
   descent theorem rather than redoing map and inverse-equation descent.
   All retained public imports supply notions in the signature; the two retained
   plain imports supply proof results. No unnecessary proof import remains.
   The original proof_deps lose exactly lem-kun-fibre-product-limits, reported above.
   Read sk-prop-input-spreading and its realized record (currently empty lists):
   unchanged; this proof still implements its local spreading step and bypasses no unit.
5. Compared the node files: only proof, proof_deps and proof_origin changed.
   Checked that proof_deps is exactly the union of the steps' uses and that the
   steps follow the Lean construction, cartesian limit proof, descent application,
   and final pullback-associativity transport. Read Stacks Tags 0BQ5 and 01ZM:
   the source attribution matches this route. Verdict: node and Lean agree.

Second reading changed only this report by adding the independent checks above.
No proof, import, signature, definition, or node repair was needed.
