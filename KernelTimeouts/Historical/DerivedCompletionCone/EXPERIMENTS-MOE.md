# Mismatch-Origin Experiment: Derived-Completion Cone

## Provenance and scope

The case is the historical `Derived-Completion Cone` at source revision
`9ba4d01f55c`, Lean `4.33.1` (`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`),
and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Fresh S0-S5
snapshots use the rebuilt `Complete.Defs` import closure and the Batch 0
`MOEStage` commands. The complete S6 aggregate is the validated READY4.1
historical replay already recorded for this exact root; the accepted READY3.2
replay differs by one call at the deterministic timeout boundary. No timing
claim is made from a different consumer or a changed theorem telescope.

## Stage snapshots

The raw records are in `moe/`. `context_inline.snapshot` and
`context_named.snapshot` were produced by `#moe_elab` in one shared variable
context, avoiding cross-file hygiene differences. `diagram-decl.snapshot`
is `#moe_decl DerivedCategory.derivedCompletionDiagram`; its imported
declaration is marked finalization-observable-only by the contract.

| Stage | Evidence | Result |
| --- | --- | --- |
| S0 | `context_inline.snapshot`, `context_named.snapshot` | Inline spelling is `Cone (quotPowFunctor J I ⋙ tensorLeft K)`; named spelling is `Cone (derivedCompletionDiagram J I K)`. |
| S1 | same snapshots | Inline expands to `Cone Functor.comp quotPowFunctor ... tensorLeft K`; named expands to the single `derivedCompletionDiagram` constant application. |
| S2 | `compare-context.txt` | The **cross-variant** inline/named difference is `root/arg/arg`: inline `kind=app` (`Functor.comp`), named `kind=fvar` (bound diagram). This is not a structural diff of the original inline M0 pair. |
| S3/S4 | `diagram-decl.snapshot`, `variants-constants.txt`, historical `REPORT.md` B1.2 | `derivedCompletionDiagram` is stored `regular:33`. Local controls distinguish `abbrev` from `regular:31`. The original inferred-value/declared-type diff has 36 proof positions, including generated `_proof_*` constants versus ambient proofs after `abstractNestedProofs`; no saved pre-finalization value isolates their first appearance. |
| S5 | `root-diagram.snapshot` | Frozen replay of the stored diagram type against its checked value type returns `MOE_KERNEL stage=S5 result=true`. |
| S6 | prior complete READY4.1 aggregate and M1 path record | The original inline root is M0 at the final inferred-type/declared-type conversion; its first corresponding application argument continues as M1. |

The cross-variant S2 difference is an expression change, not a hash-only claim. The
inline node at `root/arg/arg` is an application whose descendant head is
`CategoryTheory.Functor.comp`; the named node is a bound variable applied by
the surrounding `Cone` type. The named declaration therefore supplies a
stable constant head at the exact position where the inline source exposes
the composition.

The wrapper API M/L controls are the independently named diagram wrappers
used by the historical `Functor.obj` and `Functor.map` diagnostics. Fresh
`wrapper-obj.snapshot` and `wrapper-map.snapshot` records show S0/S1 source
and macro expansion for, respectively,
`(derivedCompletionDiagram J I K).obj (op 0)` and
`(derivedCompletionDiagram J I K).map (𝟙 (op 0))`. Both keep the named
diagram constant head at S2. The prior instrumented M/L controls are real
non-identity conversions in this wrapper family and remain below the timer
resolution; they are diagnostic controls, not the original inline Cone root.

## First divergence and kernel provenance

The original M0 pair is the inferred type of the inline cone value versus its
declared type `Cone (DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K)`.
The saved `root/arg/arg` S2 comparison is **between inline and named controls**;
it locates the naming boundary, not the first unequal node of that original
M0 pair. For the original root, the historical `REPORT.md` B1.2 structural
diff identifies 36 differing proof positions in the inferred/value versus
declared/type sides, including generated `derivedCompletionDiagram._proof_*`
versus ambient proof constants. Their exact pre-finalization S2 forms were not
captured. The inline-versus-named source choice exists already at S0/S1.

The complete READY4.1 replay has 12,220,822 recursive calls. Its exclusive
provenance totals are:

| Label | Calls | Exclusive time | Share |
| --- | ---: | ---: | ---: |
| M0 | 1 | 0.067 ms | 0.000% |
| M1 | 9,356,262 | 86,644.293 ms | 99.694% |
| M2 | 9,087 | 55.712 ms | 0.064% |
| Matched | 2,855,469 | 210.463 ms | 0.242% |
| Unclassified | 3 | 0.121 ms | 0.000% |

The first useful kernel descent is `is_def_eq_app`: after the surrounding
function-head check, the corresponding argument inherits the original root
divergence and is labelled M1. The cross-variant S2 comparison does not
identify that child's first unequal proof field. The recorded M1 path is
`root/binder_body[8]/argument[4]/argument[7]/argument[4]/binder_body[1]`.
Subsequent projection, application-argument, dependent-body and WHNF
continuations inherit that same mismatch. The largest complete transitions
are projection-to-projection (2,951,994 calls, 38,999.493 ms) and
application-to-argument (4,542,956 calls, 21,805.155 ms). These are
propagation costs, not new independent origin mismatches.

## Elaborator decision evidence

The inline trace (`remote_elab_inline.out`) records synthesis of
`MonoidalCategory (DerivedCategory (Sheaf J (ModuleCat R))` through
`DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory`, with
metavariable assignment to that constructor and nested selection of
`GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall`.
The named trace (`remote_elab_named.out`) still selects the surrounding
`HasDerivedCategory` route, but the use-site term stops at the stored
`DerivedCategory.derivedCompletionDiagram` constant and does not repeat the
derived monoidal-category synthesis.

This records instance synthesis in the elaborated inline Expr: instance
search selects a proof-carrying concrete monoidal structure, while the named
source moves that construction behind a declaration boundary. It does not
demonstrate a causal Elaborator contribution under MOE section 11: S0/S1
already differ, and no targeted perturbation changed a metavariable
assignment and final Expr with a frozen F0/F1 cost replay.
It does not demonstrate that elaborator execution is the timeout bottleneck;
the existing phase split puts the deterministic cost in the final kernel
conversion. The traces contain `Meta.isDefEq.assign` records for ordinary
metavariable assignments, but no assignment is claimed as a separate kernel
optimization or causal speedup.

## Cheap-but-fragile boundary inventory (E2)

| E2 boundary | Exact Expr/metadata change | Cheap evidence | Fragility and causal status |
| --- | --- | --- | --- |
| Named diagram head | `Functor.comp (quotPowFunctor J I) (tensorLeft K)` becomes `derivedCompletionDiagram J I K` at S2 `root/arg/arg`; stored hint is `regular:33`. | Named control completes in the existing matched family; S5 frozen replay is `true`. | Expanding the named body at the use site restores the inline shape and the timeout-scale root. Cheapness is a diagnostic boundary, not a strict same-root causal cut. |
| Explicit monoidal sharing | The source lambda gains `[MC : MonoidalCategory (DerivedCategory (Sheaf J (ModuleCat R)))]`; S2 uses bound-variable occurrences instead of freshly synthesized concrete instance data. | `remote_elab_explicit.out` records the added binder and bvars; the historical explicit-instance control is a fast, nontrivial conversion. | It changes the dependent telescope and therefore does not preserve the original M0. It demonstrates a representation boundary, not an M0-preserving intervention. |
| Vocabulary consistency | Downstream type uses the named `derivedCompletionDiagram` vocabulary rather than spelling the composition again. `abbrevDiagram` is `abbrev`; ordinary and `[reducible]` local controls are both `regular:31` in S4. | `variants-constants.txt` records the metadata distinction and the named controls remain cheap. | Reducibility metadata alone is insufficient: the exact constant head and its use-site vocabulary are the boundary. Re-expansion is fragile. |
| Proof abstraction boundary | The historical structural audit finds 36 proof positions, including `derivedCompletionDiagram._proof_*` versus ambient sheaf/derived proof constants, inside the concrete monoidal instance. | Isolated proof-position checks are below timer resolution; the full inline root is not. | The proof bodies are not independently expensive; their proposition types carry the instance expressions. Exact descendant replacement is ill-typed when the field depends on the original provider. |

## C controls, perturbation, and replay

The explicit-sharing lambda is a valid local S0-S2 perturbation and is kept in
`remote_elab_explicit.out`; it is intentionally reported as a changed-
telescope control. The existing named/explicit matrix gives the same reading:
the named diagram, explicit local instance, and combined control are all fast,
but none compares the original fixed inline provider pair.

The attempted descendant-only alignment is retained in the case history as
`InvalidDescendantAlignment.lean`. Replacing the selected proof/provider field
changes its dependent field type, so no type-correct O-cut preserves the
original cone consumer, eight-binder telescope, and M0. The original O/R
replays therefore establish reversibility of the historical root, not a causal
speedup from a selective descendant replacement.

## Remaining uncertainty

The S2 path locates the source-authored *naming-control* divergence, while the
bounded raw S6 capture cannot assign every one of the millions of M1 calls to
one concrete field path or local-context fingerprint. The named and explicit
controls change the root representation or telescope, so they cannot separate
naming from sharing with a strict same-root matched control. The available
kernel records do not measure Expr allocation or GC, and elaborator trace
volume is not a kernel-time share. The historical READY4.1/READY3.2 boundary
drift is one deterministic timeout-boundary call; no stronger precision is
claimed.

## Audit note and Batch 2 boundary test

The previous "Elaborator contribution demonstrated" label inferred causality
from monoidal-instance synthesis on only the inline source branch. The
inline/named source and S1 syntax already differ, while explicit sharing adds
a binder and changes the telescope. No section-11 perturbation isolates an
Elaborator-induced divergence. The named diagram's imported S3 record is
finalization-observable-only; its actual pre-finalization S2 value was not
captured. The original root's 36 proof-position differences include generated
constants after `abstractNestedProofs`, so declaration processing materially
affects its value-side representation; its exact first S2-to-S4 change is not
isolated. The earlier report also conflated the cross-variant `root/arg/arg`
path with the original inline M0 pair. E3 puncture: inline the type-correct
named diagram body at its use
site. The saved historical inline control restores the 12,220,822-call root;
the named control stays in the cheap family. This is a boundary diagnostic,
not an M0-preserving descendant cut. The wrapper `Functor.obj`/`Functor.map`
M/L controls remain separate, cheap, non-identity negative controls; no
raw-wrapper puncture with the original cone root was measured.
