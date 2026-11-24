# MDA Batch 0 instrumentation contract

MDA extends `../moe/MOE-CONTRACT.md` at S5/S6. MOE owns S0-S4 source,
elaboration, finalized Expr paths, and reducibility hints. MDA owns the
Kernel call tree and cost attribution. The same structural Expr pair and
environment must be used when joining MOE and MDA records.

## Revision pins

Lean 4.35.0 is `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` and its
Mathlib is `56a005855ea17e0b0958f73ec801ae140b0a1679`. Current probe
imports are pinned at `105ac3f5b23c1e6eefcf6fd1fd3f8ce745df071d`.
Lean 4.33.1 is `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` and its
Mathlib is `0df444a360eaa60ab8c11dca51a86af692955474`.
Historical source snapshots below are originals, not fast controls.

| Case | Lean / Mathlib | Original source snapshot | Measurement import tree | Evidence |
| --- | --- | --- | --- | --- |
| Slow Derived Tensor | 4.33.1 / historical | `bdab171985a5e6c6e44fc3920386b89fc5627ca3` | historical source, control `428569e1ce147b18f348606682d934b302c056a9` | MOE, CCMOA |
| Derived-Completion Cone | 4.33.1 / historical | `9ba4d01f55cd864882a84a5f566d52ef44c2d389` | historical source | MOE, CCMOA |
| EtaleHom | 4.35.0 / current | `8ca2e912b93800690f06ca80b1e4b0b122335580` | current pin | MOE, M1P, MDA |
| FiniteBaseChange | 4.35.0 / current | `0676f555de6410290e94024fe84ba51c2f73fde7` | current pin | MOE, CCMOA |
| F66Adj | 4.35.0 / current | `f66ad18a9ed8931b2d386105528c40a56fae8e0c` | current pin | MOE, CCMOA |
| OrderedSpectral | 4.35.0 / current | `f4946fdb6b68a7010f913438a6d4e3c22ee59025` | current pin | MOE, CCMOA |
| RealPushforward | 4.35.0 / current | `a2ec460045b512b71b195595d35270512bd4c025` (IM snapshot) | current pin | IM, CCMOA, M1P |
| RealPurity | 4.35.0 / current | `a2ec460045b512b71b195595d35270512bd4c025` (IM snapshot) | current pin | IM, M1P |
| ImageHomCounit | 4.35.0 / current | `a2ec460045b512b71b195595d35270512bd4c025` (IM snapshot) | current pin | IM, CCMOA, M1P |
| IntegralComparison | 4.35.0 / current | `a2ec460045b512b71b195595d35270512bd4c025` (IM snapshot) | current pin | IM, M1P |
| NativePullTensor | 4.35.0 / current | `1ef1fddac73ed8d77efa0edd9db659d19ef99cb3` (case probe snapshot) | current pin | MPRWE, M1P |
| PR1556, PR1625, PR1563, PR1624, PR1627, PR2122 | 4.35.0 / current | `1ef1fddac73ed8d77efa0edd9db659d19ef99cb3` (case probe snapshot) | current pin | MPRWE, MOE for PR1627 |

The IM reports give the short `a2ec460045b`; the full object hash above is
the matching repository commit. Workers must still pin the exact probe file
and record its hash before a case-specific replay. Historical
PR1556/PR1625/PR1563/PR1624/PR1627/PR2122 S2 source may be unavailable;
the current import pin is a measurement environment, not a claim that it is
the original PR source.

## Call identity and accounting

`(root, call)` is the only call key. Root is the process-wide relaxed-atomic
serial inherited from READY4.2; call is preorder within that root; `parent`
is the immediate recursive caller, with zero for M0. IDs never cross runs.
Labels are exactly READY4.2 `M0`, `M1`, `M2`, `Matched`, `Unclassified`.
`Unclassified` remains explicit. Initiating branches are the READY4.2
`quick`, `reflection`, `quick_reduced`, `proof_irrelevance`, `lazy_delta`,
`same_constant`, `same_fvar`, `projection`, `second_whnf`, `application`,
`eta`, `eta_structure`, `string_expansion`, `unit_like`, and `unattributed`.
`failure` and `exception` are outcomes, never gateway branches.

`exclusive_ns` is elapsed comparison time minus immediate child comparison
spans and WHNF/reduction spans. Reduction time is separate. The complete
`mda_group` rows partition comparison-exclusive time over all calls, even
when raw enter/exit capture stops. Their call sum equals root calls. A
`mda_top` row contains direct exclusive time and inclusive comparison
subtree time (`subtree_exclusive_ns`), calls, and M1 calls. Parent and child
subtree totals overlap; rank by subtree time but assign cost only once to a
chosen non-overlapping gateway partition.

## Attribution fields

Each selected `mda_top` has the original left/right head, exact kernel Expr
strings (universes, implicit args and generated names included), root/path,
branch, child kind/index, delta-exposed head, and projection structure plus
index/name. The field name is resolved from a generated structure map; an
unknown entry is `field:<index>`, not an invented name. `source` is the
nearest parent-call head with the worker-supplied source namespace prefix;
`unknown` is retained otherwise. This is an Expr-path attribution, not a
proof that the source declaration caused the conversion. API `component`
is the READY4.2 child kind and binder/argument/field index. The full name
of an application head is kept separately from that component.

`mda_group` keys are `(gateway, source, component)`. They contain all-label
direct calls and exclusive nanoseconds plus separate `m1_calls` and
`m1_exclusive_ns`. The `source` can remain the root user
head over a long internal chain; downstream Mathlib constants in selected
pairs are path nodes and do not receive duplicate cost ownership. A source
path not recoverable from the kernel alone must be joined to MOE S0-S4 with
the same exact Expr pair. Delta exposure is observational; a changed head
is not automatically the unfolded definition.

## Bounds and validation

`LEAN_DEFEQ_MDA_TOP` bounds selected costly nodes to at most 100 (default
20). `LEAN_DEFEQ_MPRWE_MAX_EVENTS` independently bounds raw READY4.2
enter/exit/reduction events. Aggregate rows and selected top pairs are
emitted after the root, including when raw capture is exhausted. The
EtaleHom selection uses 12 top nodes and 200 raw events; the compressed
selected-root JSONL is under 5 MB.

The EtaleHom original root is 2632 and has 3,180,470 calls: M0 1, M1
2,390,795, M2 22, Matched 789,652. Label calls, child edges and group
direct time reconcile exactly. The process wall baseline is 28.32 s;
field-aware trace is 103.57 s (3.66x, 75.25 s overhead). A bounded
counters-mode comparison is 29.82 s (1.05x, 1.50 s overhead). These are
single sequential process measurements, not normalized root-exclusive
controls; the trace includes exact Expr serialization and JSONL output.
