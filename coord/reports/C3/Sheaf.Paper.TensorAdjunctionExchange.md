## What changed

`tensor_adjunction` now constructs CorePackage and Package from two distinct
obligations: `normalized_models` constructs the normalized adjunction/projection
inputs; `coherent_conclusions` proves exchange and its coherence on those supplied
inputs. The assembly preserves every realization, projection and admissibility
clause. Choices occur only inside its theorem proof.

Moved the real definition interface verbatim to TensorExchangePresentation so the
proof modules can import it without a cycle. The parent publicly reexports it and
retains its five original public imports. The shared source synced S1's reviewed
coefficient-shift repair during this session; this delivery uses that latest
interface verbatim, rather than changing it again.

Change record: coord/changes/C3-tensor-exchange-presentation-assembly.md.

## Proved and sorry left

Original item holes: 1. Closed upper hole:
`WeilConjectures.TensorAdjunctionExchange.tensor_adjunction`
(node fix-lem-tensor-adjunction), with a complete record/conjunction assembly.

Added holes, both named public theorem bodies exactly `by sorry`:

- `WeilConjectures.TensorAdjunctionExchange.normalized_models`
  (lem-sf-tensor-exchange-normalized-models): normalized adjunction ingredients,
  without exchange or shift/coefficient conclusions.
- `WeilConjectures.TensorAdjunctionExchange.coherent_conclusions`
  (lem-sf-tensor-exchange-coherent-conclusions): coherent exchange on supplied
  normalized inputs, without existence of the inputs.

This is a decomposition: 1 upper hole closed, 2 lower holes added, net -1.
No holes remain in the item module or its definition owner. No definition contains
sorry or chooses data from an unproved existence theorem.

## No longer needed

No old mathematical dependency or module is pruned. The twelve original proof
obligations remain needed by the two split steps. None of the five original public
imports is removed. The final assembly uses only its two private proof imports;
the old proof obligations now belong below those two steps.

The absent signed-transposition module is not fabricated or duplicated; its node
remains a proof dependency of coherent_conclusions. The existing coefficient
transposition module uses PodHomChain records and does not directly construct the
old TensorAdjunctionExchange.Model interface.

## Where the brief, the DAG or earlier work was wrong

At session start the ledger/node reported S1's witness-specific shift repair landed,
but the shared source still had the disproved universal coefficientShifts field.
The source synced during this session, and this delivery uses the synced version.
No additional statement weakening or correction is made here.

The DAG's signed-transposition declaration points to a module absent from both lean
and quarantine at session start. Other stated dependencies use different normalized
presentations, so merely importing them does not construct these fields. The split
steps isolate that construction and the exchange/coherence argument.

The latest blueprint uses finite stalk tests, integral derived Nakayama, rational
integral-model generation and common finite-field descent. Those arguments remain
in coherent_conclusions' docstring and node. The normalized-input step retains the
finite/uniform integral domain obligations already stated by the DAG. The five
adjunction arrows, actual projection, canonical inverse, signed shifts and specified
coefficient comparisons remain. No unit route is bypassed.

Searches via msearch.py used LeanSearch, LeanFinder, Loogle and grep. They found
generic adjunction/closed-category tools but no exact normalized geometric package.
The upstream etale TensorHom.lean constructs an exchange via parametrized adjunctions;
it does not supply these pro-etale/completed/localized/common-stage realization
and coefficient records. Source and DAG duplicate searches found no existing
normalized-input/conclusion separation with these precise records.

## New nodes

`def-sf-tensor-exchange-presentation` owns the moved real definition interface plus
Presentation and NormalizedDatum, without any existence assertion. It prevents the
cycle from proof-step modules importing the parent theorem.

`lem-sf-tensor-exchange-normalized-models` is the input construction, strictly
excluding exchange conclusions. Its proof in words covers domains, completion,
projection normalization and coefficient-stage construction.

`lem-sf-tensor-exchange-coherent-conclusions` is the five-arrow/Yoneda, coefficient
and shift argument on normalized supplied inputs. It does not construct them.
The final theorem combines the two parts with an explicit CorePackage record
construction and the unchanged realization witness.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
