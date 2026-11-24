# MDA: Derived-Completion Cone

## Scope and evidence

Historical source `9ba4d01f55cd864882a84a5f566d52ef44c2d389`, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, Lean 4.33.1
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. The root is the final
inferred-type versus declared-type check of `HistoricalR2.inlineCone` in the
existing `probes/anatomy/inline.lean`; probe SHA-256 is
`c0fff6972e903452268c45aa8f7f591140cc96c7801b6b61f6ab1563f556483e`.
It has the eight-binder context and the declared result
`Cone (DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K)`. The full root Expr
pair and universe arguments are in `mda/pair-1.json.gz`; the 36 proof-position
proposition Exprs are in `mda/proof-position-exprs.txt` (structural `repr`,
including hidden arguments, local free variables and universe levels).

Two fresh MDA traces of the same original root had exactly 12,220,822 calls,
9,356,262 M1 calls, 9,087 M2 calls, 2,855,469 Matched calls and three
Unclassified calls. The first trace measured 123.761 s comparison-exclusive,
of which M1 owned 123.321 s (99.645%); reduction time is separate. The
root-filtered replay measured 136.204 s comparison-exclusive. Timing varies
with tracing overhead; the tables below use the first run only. The full
direct-cost, label and edge partitions reconcile in `mda/validation.md`.
`mda/root-filtered-events.jsonl.gz` supplies the first raw root calls, which
the first run's global raw-event cap missed.

The root-filtered call 1 reports the first structural divergence at
`root/body/body/body/body/body/body/body/domain/fn/arg/arg/fn/fn/fn/fn/fn/fn`.
The corresponding minimal differing proof position in the fresh structural
audit is `HistoricalR2.inlineCone._proof_1` against
`GrothendieckTopology.hasSheafify_of_essentiallySmall`, of proposition type
`HasSheafify J (ModuleCat R)` on both sides. The `HasSheafify` pair itself
checks immediately. The first divergence's *source before finalization* is
unknown: no matched pre-`abstractNestedProofs` Expr was retained.

## 4.1 Gateway-to-cost

These selected subtree times are **inclusive and nested**. They identify the
path, not additive cost shares. Exact left/right pairs for the selected calls
are the numbered compressed JSON files in `mda/`; `mda/root-summary.json`
has every selected call's parent, label, path and component.

| Gateway ID | Parent M0 path / call | Kernel branch | Exact child pair | Source/API candidate | M1 calls in subtree | Subtree exclusive s | Evidence |
| --- | --- | --- | --- | --- | ---: | ---: | --- |
| 1849:34 | first proof divergence; 24 | application, argument 4 | `Functor.comp` / `Functor.comp`; `pair-34.json.gz` | inline diagram composition | 9,356,253 | 123.756 | S: original path and named counterfactual |
| 1849:35 | 34 | lazy-delta, argument 7 | `MonoidalCategory.tensorLeft` / same; `pair-35.json.gz` | derived monoidal instance argument | 9,356,252 | 123.756 | S: exact pair; upstream nested cost |
| 1849:44 | 42 | quick dependent-body 1 | `MonoidalCategoryStruct.tensorObj` / same; `pair-44.json.gz` | first costly monoidal field, index 0 | 9,356,244 | 123.751 | S: direct field path; inclusive nested cost |
| 1849:45 | 44 | second WHNF exposure | `Functor.obj` / same; `pair-45.json.gz` | object component of tensor functor | 9,356,243 | 123.728 | S: exact child and exposure |
| 1849:47 | 46 | application function-head | `Functor.obj` projection / same; `pair-47.json.gz` | `Functor` field 0 | 9,356,241 | 123.626 | S: projection metadata and field map |
| 1849:589679 | 589656 | quick dependent-body 3 | `CategoryStruct.comp` / same; `pair-589679.json.gz` | category composition field 2 | 8,905,314 | 116.894 | S: exact child; downstream of 47 |

Call 34 is the first costly M1 child after the eighth-binder cone body (call
24). Call 35 exposes `Functor.mk`; call 44 is the first costly monoidal field.
Call 47's projection is explicitly `Functor.obj:0`. The nested category path
then enters `CategoryStruct.comp`, `DFunLike.coe`, `EquivLike.coe` and
`Equiv.toFun`; these are measured path nodes, not separate owners of the same
inclusive time. The first run's source-prefix field is `unknown` on this path:
the Kernel Expr heads are generic imported declarations, so the source link
to the inline cone is supplied by the exact root pair and source declaration.

## 4.2 Definition/API path and non-overlapping direct cost

The direct group rows below partition M1 comparison-exclusive time; they
classify *mechanisms*, not separate source declarations. The remaining
groups are in `mda/root-summary.json`.

| Candidate definition/API | Role | First seen | Kernel path / component | M1 calls | Direct M1 exclusive s | Intervention | Evidence |
| --- | --- | --- | --- | ---: | ---: | --- | --- |
| Inline `Functor.comp` in cone type | producer/API | source and 1849:34 | application argument 4 | 126,501 across root | 3.346 | named diagram: 22 calls | S |
| `MonoidalCategoryStruct.tensorObj` | gateway/field | 1849:44 | quick dependent-body 1 | 59,206 across root | 1.200 | named diagram bypasses root | S |
| `Functor.obj` and nested projections | amplifier | 1849:45/47 | projection field 0 | 2,951,252 | 45.242 | named diagram bypasses root | S |
| WHNF through derived functor/category data | amplifier | 1849:45 onward | second WHNF exposure | 1,053,679 | 25.099 | named diagram bypasses root | S |
| Application arguments 0, 1, 2 | amplifier | below 1849:47 | application argument | 1,844,827 | 18.876 | named diagram bypasses root | S |
| Generated proof proposition types | downstream amplifier | below 1849:47 | proof-irrelevance proposition-type | 187,303 | 4.112 | named diagram bypasses root | S for path, P for individual proof owner |
| `CategoryStruct.comp` | nested amplifier | 1849:589679 | dependent body 3 | 14,552 | 3.646 | named diagram bypasses root | S for path, aggregate is branch-wide |

The row labelled `CategoryStruct.comp` uses the **branch-wide**
dependent-body-3 direct group, so 3.646 s is an upper bound for that specific
field, not a field-exclusive total. Likewise the `Functor.obj` row is a
branch-wide projection-0 group. The exact field path is established by the
selected call pairs and `mda/field-map.txt`; attributing every call in a
group to that one field would overclaim. No inclusive subtree time is summed.

The two exact call-34 arguments each contain
`DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory`. Their
`GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall` subterms
have different structural occurrences (one versus four in these serialized
expressions). This is an observed concrete representation divergence, not
evidence that that declaration alone caused the cost. The path continues
through `Functor.totalLeftDerived` and `DerivedMonoidal` in the retained
exact pairs.

## Proof-position audit

The fresh audit found the same 36 minimal proof-term differences, with their
individual paths and both structural proposition types saved in
`mda/proof-position-exprs.txt`. All 36 isolated proposition-type conversions
returned `equal` in under the one-millisecond timer resolution. Most are
repeated `HasSheafify` and `IsGrothendieckAbelian` occurrences; the remaining
families include `MonoidalPreadditive` and
`Functor.HasDerivedMonoidalCategory`. In the original root, the corresponding
top-level `inlineCone._proof_*` comparison groups are individual cheap
events, while 187,571 generated `Eq` proposition comparisons occur deep in
the category/functor chain. They are different proof positions.

Thus no one of the 36 has a demonstrated non-overlapping share of the 123 s
M1 workload. The root-filtered M0 path points to the first `HasSheafify`
position; the expensive call-34 chain descends through the cone body. Its M1
label records persistence of that original divergence, not ownership by that
proof term. Whether several of the 36 positions converge on one concrete
instance comparison is **U**: the shared tool records global top subtrees and
aggregate paths, but not a position ID propagated through WHNF/Delta and
proof-irrelevance descendants. A position-tagged call-tree trace with
subtree-close records and exact proposition pairs, or an equivalent
non-overlapping call-ID partition, is needed. The 20 global top entries are
almost all ancestors on one chain and cannot answer that question.

## 4.3 Root-to-source chain and interventions

`inlineCone` writes the inline `quotPowFunctor J I ⋙ tensorLeft K` in its
declared cone type (source/API choice, **S**) -> inferred and declared
types differ first at the `HasSheafify` proof representation in the seventh
binder domain (M0, **S**; first stage between elaboration and finalization
**U**) -> the eighth-binder body compares `Functor.comp` arguments, call 34
(gateway, **S**) -> `tensorLeft` WHNF, `MonoidalCategoryStruct.tensorObj`,
`Functor.obj` field 0, then `CategoryStruct.comp` field 2 (exact pairs and
fields, **S**) -> 9,356,262 M1 calls and 123.321 s direct M1 time in the
first trace -> the named `derivedCompletionDiagram` API changes the cone's
outer diagram head and avoids this conversion (counterfactual, **D**).

The **one factor** in the named control is the diagram expression in the
declared type. It is type-correct and retains the mathematical cone over the
same diagram construction, but changes the root Expr and M0: it is an
API-level counterfactual, not an M0-preserving local cut. A fresh MDA run of
the named control has a largest relevant root of 22 calls, 0.598 ms
comparison-exclusive, with no `tensorObj`/`Functor.obj` chain; its declaration
checks. The explicit shared-instance control has 344 calls and 22.377 ms in
the fresh trace, but adds a binder and changes the dependent telescope, so it
is **not** the one-factor original-M0 intervention. The original inline
spelling restores 12,220,822 calls in the fresh root-filtered replay.
The named boundary is fragile but effective: unfolding/inlining it at use
sites exposes the concrete monoidal data again. Its outer head is a regular
definition (`regular:33` in the saved MOE snapshot), so maintenance that
replaces it with an abbrev or an inline composition can puncture the boundary.

## 4.4 Per-case summary

| Case | Mismatch producer | Expansion gateway | Cost amplifier | Best intervention | Evidence |
| --- | --- | --- | --- | --- | --- |
| Derived-Completion Cone | Inline composition with separately represented proof/instance arguments; first `HasSheafify` proof mismatch at M0 | call 34 application argument into `Functor.comp`, then call 44 `tensorObj` field 0 | `Functor.obj` projection and `CategoryStruct.comp` field 2, with nested generated equality propositions | named regular `derivedCompletionDiagram`: 12,220,822 calls to 22; 123.761 s to 0.598 ms comparison-exclusive in separate trace runs | producer **S**; gateway **S**; amplifier **S**; API counterfactual **D**; per-position ownership **U**; finalization origin **U** |

The root Expr pair is saved in `mda/pair-1.json.gz`; the exact local-context
declarations are available in the earlier `moe/compare-context.txt` snapshot,
but the MDA JSONL does not serialize the local-context object. Individual
proposition pairs are in the audit file.
The original root times out at the deterministic Kernel limit; controls
complete. The small controls do not emit complete MDA JSONL group rows because
the shared writer has a hard 1,000-call threshold. Their fresh root counters
and raw events were used for the effect comparison. A control-level complete
gateway table would require removing that writer threshold in a scratch
instrumentation build. No pre-finalization Expr, type-correct M0-preserving
field intervention, or position-tagged descendant trace was available.

## Audit note

The named diagram control is **D** only as an API-level counterfactual: the
root and M0 change, and inline restoration returns 12,220,822 calls. The
`Functor.comp`/`tensorObj`/`Functor.obj` path is **S** from exact selected
children. The 36 isolated proof types are cheap, so their causal ownership
of the 123.321 s M1 workload remains **U**. Branch-wide direct groups do
not establish exclusive time for each named field.
