## What changed

Reduced `closed_test_chain_mate_restriction` to the independent derived-exchange and
localized-derived-unit normalization calculations. The new modules
`Sheaf.Paper.ClosedTestChainExchangeNormalization` and
`Sheaf.Paper.ClosedTestChainUnitNormalization` state these strict subclaims with
complete proof plans. They use the existing constructions through the new acyclic interface module
`Sheaf.Paper.ClosedTestChainMateData`. This moves construction declarations verbatim;
the parent publicly imports them under their unchanged names.
The parent imports both privately and assembles the conjunction without a proof hole.

Proved the middle chain equality from `closed_test_mate_sections`: cancel the literal
pushEvaluation isomorphism, apply the equality of natural transformations termwise,
and compose with the same supplied resolution map. Existing public signatures,
definition and instance signatures and bodies are unchanged. The parent adds the public
interface import; the interface retains the parent’s original public dependency imports.

## Proved and sorry left

One of the original two holes is reduced: `closed_test_chain_mate_restriction` has a
complete proof from the two new normalization statements and the proved chain equality.
This is a decomposition, not a net proof gain: one hole closed and two holes added.

Three holes remain in this packet, all in namespace
`AlgebraicGeometry.ProEtale.ClosedTestChainMateRestriction`:

- `closed_test_mate_sections`, unchanged; node
  `lem-sfb-closed-test-chain-mate-restriction`.
- `closed_test_chain_exchange_normalization`; new node
  `lem-sfb-closed-test-chain-exchange-normalization` (original proof step 3).
- `closed_test_chain_unit_normalization`; new node
  `lem-sfb-closed-test-chain-unit-normalization` (original proof steps 5–6).

The previously proved `closed_test_localized_adjunctions` and its helpers are preserved.
The new statements were checked on zero complexes, identity resolutions, the zero and
unit ideals, and empty tests: they assert compatibility of the actual maps and never
assert that restriction or exchange is invertible. The quasi-isomorphism j is the only
resolution arrow inverted, through the original pullRepresentative construction.

## No longer needed

No imports or modules are withdrawn. The parent now delegates its original step-3 and
steps-5–6 dependencies to the two new nodes; those dependencies remain needed below
these nodes. The middle chain equality does not separately need the K-injective section
model theorem: it follows directly from the ordinary section equality by functoriality.
No blueprint unit is bypassed. No source-library declaration is removed or changed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. A direct proof using the general
iterated-mate unit identity was explored; its concrete module-adjunction specialization
exceeded the compile limit because of definition unfolding. It is not part of this
packet. The delivered reduction instead follows the existing numbered plan. Expanded split
statements also caused excessive kernel unfolding, so the existing construction
constants were extracted for acyclic imports; no slow proof or mathematical argument
was divided to evade a limit.

## New nodes

`lem-sfb-closed-test-chain-exchange-normalization` isolates the derived mate
representative calculation, original step 3. `lem-sfb-closed-test-chain-unit-normalization`
isolates the localization and derived global-section composition calculation, original
steps 5–6. Each has its own module, named public theorem, source, proof in words and
matching node. Both are strict parts of the original three-conjunct theorem.
The construction extraction is recorded in
`coord/changes/closed-test-chain-mate-data.md`. Downstream checks find zero consumer
modules; no forced adaptations are needed. The interface has node
`def-sfb-closed-test-chain-mate-data`, attaching every moved declaration.

The node and consumer checks confirm the three new import directions are acyclic,
and every new Lean signature agrees with its node attachment.

The four-module lcompile check passed. Its two parent style warnings were removed
before delivery; deliver3.py performs the final compile and packet checks.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
