# Mismatch-to-definition attribution: PR1624

Lean 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`); historical probe snapshot `1ef1fddac73`. Fresh MDA trace of `probes/mprwe/OriginalDependentEndpoint.lean` (SHA-256 `791a5361be2821263e5cb5fa4cdfeb00085f5c2bda209e8c1aaf95b86897110f`) selected root 22078 in the pinned import tree. `mda/selected-root.jsonl.gz` stores exact left/right Exprs, universes and implicit arguments for every selected call below.

## A. Root and M0

The checked final argument of a seven-argument `Iso.trans` is an `isoWhiskerLeft` term. Its inferred type and the instantiated seventh binder domain are both `Iso` applications with structurally identical carrier and category arguments. Source and target endpoint arguments are concrete `Functor.comp` pairs. The earlier exact S5 probe found arguments 2/3/6/7 unequal under the common `Functor.comp` head; historical S2 and pre-finalization Exprs remain unavailable. `Functor.comp` has hint `regular:1`, with a one-step `Functor.mk` body. The root returns equal after 6,598,545 calls, 64,749.140 ms comparison-exclusive and 46,810.905 ms reduction time. M1 is 5,215,138 calls / 64,098.198 ms; M2 287 / 157.750 ms; Matched 1,383,111 / 92.308 ms; Unclassified 8 / 372.530 ms. M1 maximum depth is 88, mean fan-out 1.265 and maximum 21.

## B. Gateway-to-cost (§4.1)

Selected subtree times include all labels. Arguments 2 and 3 are disjoint siblings; rows below each endpoint are nested and must not be added to it. The MDA extension records M1 call counts per selected subtree but only total-label subtree exclusive time. Exact M1-only time for each selected subtree is unavailable; complete M1-only direct groups appear in the next table.

| Gateway ID | Parent M0 path | Kernel branch | Exact child pair | Source/API candidate | M1 calls | M1 exclusive time | Total subtree exclusive time | Evidence |
| --- | --- | --- | --- | --- | ---: | --- | ---: | --- |
| 22078:14 | root 22078:1 | application / argument 2 | `Functor.comp` / `Functor.comp` | source endpoint composition | 2,608,356 | unavailable by subtree | 35,285.633 ms | S: exact first expensive child |
| 22078:3299856 | root 22078:1 | application / argument 3 | `Functor.comp` / `Functor.comp` | target endpoint composition | 2,606,776 | unavailable by subtree | 29,434.581 ms | S: disjoint sibling |
| 22078:1601762 | argument 2 | application / argument 7 | `Functor.comp._proof_4` / same | source `map_comp` law | 1,341,527 | unavailable by subtree | 16,789.394 ms | S: nested proof path |
| 22078:1601763 | argument 2 / argument 7 | proof irrelevance / proposition type | exact dependent pair in JSONL | generated law proposition | 1,341,526 | unavailable by subtree | 16,484.081 ms | S: nested in prior row |
| 22078:4900253 | argument 3 | application / argument 7 | `Functor.comp._proof_4` / same | target `map_comp` law | 1,341,531 | unavailable by subtree | 12,357.981 ms | S: nested proof path |
| 22078:3583908 | argument 3 / argument 5 | dependent body / binder 3 | `Functor.map` / `Functor.map` | target map component | 670,686 | unavailable by subtree | 9,351.258 ms | S: nested map path; child Unclassified |

The first selected expensive branch is 22078:14, before any `Functor.mk` field path. The two `Functor.comp._proof_4` branches show that proof proposition types, rather than only object values, amplify both endpoints. The target map descendant at 3583908 is Unclassified at entry and contains M1; its lineage cannot be relabeled wholesale as M1.

## C. Definition/API path (§4.2)

| Candidate definition/API | Role | First seen | Kernel path | M1 calls | M1 exclusive time | Intervention | Evidence |
| --- | --- | --- | --- | ---: | ---: | --- | --- |
| Concrete whiskered `Iso.trans` endpoints | producer | S0 source; exact S5 pair | root arguments 2/3 | 5,215,132 in two disjoint selected endpoint subtrees | unavailable by subtree | abstract helper | S: producer/boundary confounded |
| `Functor.comp`, `regular:1` | expansion gateway | 22078:14 and 3299856 | application argument 2/3, then `Functor.mk` | 2,608,356 / 2,606,776 | unavailable by subtree | no local typed alignment | S for traversal; P for local cause |
| `Functor.comp._proof_4` | downstream law component | 1601762 and 4900253 | application argument 7 | 1,341,527 / 1,341,531 | unavailable by subtree | helper removes concrete check | S for traversal |
| `Functor.map` | downstream map component | 3583908 | dependent body then lazy delta | 670,686 | unavailable by subtree | no map-only control | S for traversal |
| Projection component 0, unknown source | direct M1 amplifier group | aggregate | projection | 904,705 | 18,225.644 ms | none | S for partition, U for source owner |
| `comparisonUpperStar._proof_1` / projection 0 | direct M1 source-context group | aggregate | projection | 391,545 | 8,092.882 ms | none | S for partition, P for ownership |
| `comparisonUpperStar._proof_1` / WHNF exposure | direct M1 source-context group | aggregate | `second_whnf` | 159,390 | 2,432.279 ms | none | S for partition, P for ownership |

The final three rows are disjoint direct-cost groups over the root. Their nearest-head source keys are observational; `comparisonUpperStar._proof_1` may be a downstream context rather than the initial gateway. No time is assigned twice to it and the selected inclusive subtrees. The field map resolves `Functor.obj`, `map`, `map_id`, and `map_comp` indices 0-3; the selected proof-4 head is a generated law path, not proof that the field itself was constructed at this Kernel transition.

## D. Root-to-source chain (§4.3)

Concrete derived-functor composition under two whiskerings (S0, S) -> two differently represented `Functor.comp` endpoints in an `Iso.trans` domain (S5, S) -> M0 `Iso` pair 22078:1 -> application argument 2/3 gateways 22078:14/3299856 (S) -> nested `Functor.comp._proof_4` proposition comparisons and `Functor.map` dependent bodies (S) -> projection and WHNF descendants with 64,098.198 ms root M1 direct-exclusive time (D measurement) -> `homologyIntegersTowerIsoAux` over abstract functor variables avoids the old concrete endpoint check (S API-level counterfactual).

The same-statement `Before.lean`/`After.lean` source control changes concrete assembly to the abstract helper, reducing target Kernel checking from 102 s to 3.18 s. Earlier broad endpoint alignment reduced 6,598,545 calls to 456,393 but changed the dependent telescope and M0, so it is not a one-factor cut of either endpoint. Restoring the concrete assembly restores the slow target. No valid endpoint-only intervention preserving the original dependent root is established. The helper's own Kernel hint was not measured; its status as a stable head boundary is P. Reassociating concrete compositions at the use site punctures the effective boundary.

## E. Summary (§4.4)

| Case | Mismatch producer | Expansion gateway | Cost amplifier | Best valid control and effect | Overall evidence |
| --- | --- | --- | --- | --- | --- |
| PR1624 | concrete derived-functor composition under whiskerings (S) | `Iso` application arguments 2/3 into `Functor.comp` (S) | `Functor.comp._proof_4` proposition types, `Functor.map`, projection paths (S traversal, P causal ownership) | abstract helper, same statement but API-level: target 102 -> 3.18 s | S; no M0-preserving local cut |

The boundary is fragile but effective. A direct per-endpoint M1-exclusive number needs per-label subtree accumulation in MDA, while an exact source declaration owner needs a Kernel call-context tag or a structural join to a matched S2 Expr. A type-correct single-endpoint alignment under the original `Iso.trans` telescope would be the smallest causal control. Historical S2/finalization causality remains U.

Artifacts: `mda/selected-root.jsonl.gz`, `mda/analysis.txt`, `mda/fields.map`. Label calls, transition edges and direct groups reconcile exactly.

## Audit note

The concrete endpoint and `Functor.comp` gateway are **S** with historical S2 unavailable. The abstract helper is an API-level counterfactual, not an M0-preserving endpoint cut. Law and map paths are **S** traversal with **P** individual ownership.
