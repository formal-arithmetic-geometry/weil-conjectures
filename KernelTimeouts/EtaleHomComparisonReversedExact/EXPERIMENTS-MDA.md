# MDA attribution: EtaleHom

## Scope and evidence

The source declaration is `etaleHomComparison_reversedExact_commShift_component` at source revision `8ca2e912b93800690f06ca80b1e4b0b122335580`. The measured import tree is `105ac3f5b23c1e6eefcf6fd1fd3f8ce745df071d` with Lean 4.35.0. The checked conversion is argument 26 (`hv`) of `derivedTensorHomShiftComparison_component`, using `probes/mprwe/Original.lean`. The exact kernel Exprs, including universes and implicit arguments, are in `mda/selected.jsonl.gz`, root 2632. The local context and S2 pair are in `moe/P4Frozen-results.md` and `EXPERIMENTS-MOE.md`. This case reuses the completed Batch 0 field-aware trace; no new control was run.

The source supplies `hv : IsEtaleHomTranspose X φ M v`; the helper expects an instantiated `forall K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat A)), ...`. The S2 outer Exprs are application/forall. `IsEtaleHomTranspose` has hint `regular:34`; `DerivedCategoryModule` is an `abbrev`. The original root succeeds with 3,180,470 calls, 2,390,795 M1 calls, 22 M2 calls, 789,652 Matched calls, and 30,519.102 ms comparison-exclusive in the MDA trace. Instrumentation changes wall time, so compare counts and within-trace exclusive partitions rather than cross-run trace timings.

## 4.1 Gateway-to-cost

Rows below are nested inclusive subtrees; only the first selected gateway owns the cost. The exact Expr pair for every ID is in the reduced JSONL.

| Gateway ID | Parent M0 path | Kernel branch | Exact child pair | Source/API candidate | Subtree calls / M1 calls | Subtree comparison-exclusive | Evidence |
| --- | --- | --- | --- | --- | ---: | ---: | --- |
| 2632:3 (parent 1) | `root/binder_body[1]` | `quick` dependent body | `Eq` / `Eq`, instantiated body after `IsEtaleHomTranspose` exposure | argument-26 dependent proposition | 3,180,468 / 2,390,794 | 30,438.540 ms | S: exact trace and S2 join; no local cut |
| 2632:709 (parent 3) | `root/binder_body[1]/argument[2]` | application argument 2 | `DFunLike.coe` / `DFunLike.coe` | equality's coerced equivalence component | 3,179,762 / 2,390,536 | 30,278.941 ms | S: exact trace, nested in 3 |
| 2632:710 (parent 709) | same path, then WHNF | `second_whnf` | `EquivLike.coe` / `EquivLike.coe` | downstream equivalence exposure | 3,179,761 / 2,390,535 | 30,242.470 ms | S: path node, not separate owner |
| 2632:713 (parent 712) | six WHNF exposures | `second_whnf` | `CategoryStruct.comp` / `CategoryStruct.comp` | dependent category composition | 3,179,758 / 2,390,532 | 30,174.445 ms | S: path node, not separate owner |
| 2632:1335 (parent 1334) | `.../argument[0]/argument[7]` | `lazy_delta` argument 7 | `DFunLike.coe` / `DFunLike.coe` | deeper equivalence/coercion component | 3,179,090 / 2,390,295 | 29,199.059 ms | S: nested path node |

The first expensive child is the dependent **body** (call 3); the initial domain comparison is outside that dominant child. This corrects the broad domain-level description in the earlier aggregate report. The equivalence projections and `CategoryStruct.comp` occur after call 709 and are amplifiers, not the source-authored producer. `mda_top` records a selected nested chain, not a complete field-by-field ordering.

## 4.2 Definition/API path

These direct `mda_group` rows partition time by Kernel branch/component. Their `source` label remains the nearest user head, `IsEtaleHomTranspose`; it does not prove every internal call unfolded that definition. Rows are disjoint, unlike 4.1.

| Candidate definition/API | Role | First seen | Kernel path | M1 calls | M1 exclusive | Intervention | Evidence |
| --- | --- | --- | --- | ---: | ---: | --- | --- |
| `IsEtaleHomTranspose` vs helper `forall` | producer | S0/S2 | root application/forall | 2,390,795 total | root M1 total within 30,519.102 ms | whole-proposition transport | D |
| instantiated `Eq` body | gateway | call 3 | `quick/dependent-body[1]` | 2,390,794 inclusive | 30,438.540 ms inclusive | transport changes M0 | S |
| `DFunLike.coe` equivalence argument | amplifier entry | call 709 | `application/argument[2]` | 2,390,536 inclusive | 30,278.941 ms inclusive | no local control | S |
| projection field 0 (structure unresolved) | amplifier component | aggregate | projection | 626,927 direct | 9,744.225 ms direct | no local control | P |
| WHNF/Iota exposure through `EquivLike.coe`, `Equiv.toFun`, `Equiv.invFun` | amplifier path | calls 710-715 | `second_whnf` | 255,583 direct | 6,564.525 ms direct | no local control | S for path, P for exact field allocation |
| application argument 1 | amplifier component | aggregate | application | 211,855 direct | 2,952.623 ms direct | no local control | P |
| application function head | amplifier component | aggregate | application | 449,473 direct | 1,750.894 ms direct | no local control | P |
| proposition-type comparison | dependent amplifier | aggregate | proof irrelevance | 60,717 direct | 937.566 ms direct | no local control | P |

`NatTrans.app`, `tensorLeft`, derived-category instances, and Hom additive structures occur in earlier S6/path records. The selected MDA nodes do not individually identify their non-overlapping exclusive shares; attributing the entire 30 s to each would double-count. A larger selected-node budget or call-stack source inheritance through non-user namespaces, plus field maps for `DFunLike`/equivalence/category structures, is needed to split those shares.

## 4.3 Root-to-source chain

Source `hv : IsEtaleHomTranspose X φ M v` handed directly to the helper -> S2 named predicate application versus instantiated raw `forall K` domain (M0 at argument 26) -> regular `IsEtaleHomTranspose` exposure and dependent `Eq` body at call 3 -> coerced equivalence argument at call 709 -> `EquivLike.coe`, `Equiv.toFun`, `Equiv.invFun`, `CategoryStruct.comp`, later `DFunLike.coe` -> 2,390,794 M1 calls / 30,438.540 ms inclusive at call 3. The source-to-S2 link is D; the call-3 and call-709 path is S; finer field ownership is P. The control supplies `(fun K => by transport_exact hv K)` at argument 26, retains the preceding 25 arguments, and changes the outer type to matching `forall`/`forall`.

## 4.4 Summary

| Case | Producer | Expansion gateway | Cost amplifier | Best intervention | Evidence |
| --- | --- | --- | --- | --- | --- |
| EtaleHom | named `IsEtaleHomTranspose` versus helper's raw dependent proposition (D) | exposed dependent `Eq` body, call 3; `DFunLike.coe` argument, call 709 (S) | equivalence/coercion projections, composition, dependent proposition comparisons (S path; P field shares) | whole-proposition transport, 3,180,470 -> 7,039 calls; direct/expanded restoration -> 3,180,470/3,179,834 | D for API boundary; not M0-preserving |

The theorem/helper obligation and first 25 arguments are preserved, but transport changes the argument-26 proposition and M0. The named predicate boundary is fragile: direct `hv` or an explicitly expanded predicate punctures it and restores the expensive conversion. No causal Elaborator transparency/provider result was demonstrated. Remaining uncertainty is the exact per-field cost inside the dominant coerced equivalence; the current selected-node trace identifies its entry and downstream heads but not a complete field ordering.

## Audit note

The producer is **D** because the S2 pair and type-correct transport are
preserved. The call-3/call-709 gateway is **S**: it is an exact selected path,
but the transport changes M0. Amplifier field shares remain **P**, since the
selected inclusive nodes overlap and no field-local intervention was run.
