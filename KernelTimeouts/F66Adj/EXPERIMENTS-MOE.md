# MISMATCH ORIGIN AND BOUNDARY STABILITY REPORT

Case: F66Adj
Lean / Mathlib revision: Lean 4.35.0 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
Source snapshot: `f66ad18a9ed`; declaration `imageHomIso_naturality`.
Root conversion: helper `homIso_naturality_of_counit`, proof argument 39 (`hR`).

## 1. STAGE SNAPSHOTS

### S0 source

The slow source supplies
`imageRestriction_counit A _ _ (Over.mk f.left)` as `hR`. The helper's
argument-39 domain is dependent on the preceding 38 arguments and contains a
local scheme variable. The direct control supplies
`restriction_counit A f.left _ _`. The `Over.mk` choice is explicit source
syntax; no source macro is responsible for it.

### S1 macro-expanded

The Batch 0 snapshot records the same application structure after expansion:
the original has `imageRestriction_counit ... Over.mk f.left`, and the control
has `restriction_counit ... f.left`. No macro-generated representation change
was found. See `moe/S2-proof-snapshots.txt`.

### S2 elaborated

The elaborator resolves both terms in the same local context (`A`, `X`, `S`,
`T`, `f`, `K`, `M` and their category/module instances). The proof-term
snapshots are structurally different at `root/arg/arg` (`app` versus `fvar`),
as reported by `moe/S2-compare.txt`. The proposition-type audit of the exact
argument-39 pair gives the first relevant path:

```text
Eq type -> Quiver.Hom argument 1 -> DerivedCategoryModule scheme argument
```

At that leaf the actual proposition contains
`Over.left (Over.mk f.left)` and the expected proposition contains the local
scheme `X`. The difference repeats in both sides of the seven-argument
`CategoryStruct.comp` equality. `Over.left` is an `Expr.app`/abbrev node; the
first path is not an initial projection.

### S3 finalized

For the baseline source compiled in a scratch declaration, the imported
declaration snapshot is necessarily `finalization-observable-only`. The root
type hash is `1338557591`; the root value hash is `2540733603`.
`imageRestriction_counit` and `restriction_counit` are opaque theorem
constants. Their S3 type/value roots are also recorded in
`moe/counit-declarations.snapshot`.

### S4 stored ConstantInfo

The baseline declaration has the same type hash `1338557591` and value hash
`2540733603` at S4. These two imported-environment views do not establish
that no S2-to-S4 finalization change occurred. The fixed
current declaration has the same type hash but value hash `3419966969`; this
is a source-variant value change, not evidence that finalization introduced
the hR mismatch. Both snapshots report theorem kind, `opaque` hints, one
universe parameter, and `hasValue=true`. The auxiliary scan was intentionally
bounded/skipped; no auxiliary-declaration claim is made.

### S5 Kernel root pair

The exact root is conversion of the instantiated proposition for argument 39,
not comparison of the proof bodies. Its first active mismatch is the
`Over.left (Over.mk f.left)` versus `X` scheme leaf above. This is M0.
The source root replay succeeds but is expensive.

### S6 Kernel-exposed descendants

The READY3.2 replay attributes 2,961,163 calls and 30,086.859 ms exclusive
comparison time to M1 (99.791%), 9 calls and 0.065 ms to M2 (0.000%), and
936,732 calls and 63.029 ms to matched descendants. Representative M1 nodes
include `DFunLike.coe`, `CategoryTheory.Functor.proj`, and linear-map/additive
projections. The recorded M2 nodes are the concrete versus site-derived
monoidal proof constants exposed by initial WHNF. The exact reduction order
from `Over.left` to every descendant is not recorded by the available trace.

## 2. FIRST DIVERGENCE

Exact relevant expressions:

```text
actual hR proposition: imageRestriction_counit A _ _ (Over.mk f.left)
expected hR proposition: the helper's hR domain at local scheme X
first material leaf: Over.left (Over.mk f.left)  versus  X
```

Earliest stage: S0/S1 source application, confirmed in the S2 elaborated
proposition. It is active when the helper application checks argument 39;
the preceding 38 arguments remain cheap. Consequence: M0 at argument 39 and
large M1 propagation below dependent derived-category/functor data.

## 3. ORIGIN

- Source-authored: **yes**. `Over.mk f.left` is written in the original hR application.
- Macro-generated: **not observed**.
- Elaborator-selected: **not demonstrated** for the relevant split. The elaborator assigns ordinary implicit instances and preserves the explicit Over term.
- Declaration-finalization-generated: **not established as the origin**. The
  source and S2 proposition already contain the scheme split; an independent
  pre-finalization versus S4 comparison was not captured.
- Environment/import-frozen: **yes** for the imported opaque counit theorem constants and their stored proposition types.
- Kernel-exposed: **only for descendants**. The first mismatch is already present at S2; later `Comma.left`/functor/projection structure is exposed by Kernel reduction.
- Unknown / mixed: exact internal Kernel reduction order and isolated `Over.left` share remain unknown.

Evidence strength: strong for the source/S2 origin and the argument-39 causal
boundary; partial for the internal descendant route.

## 4. ELABORATOR PROVENANCE

The scoped Meta traces in `moe/elaborator-provenance.txt` show the same normal
routes for the original and direct terms: `inst✝` for `CommRing A`,
`Scheme.instCategory`, `instCategoryOver`, `catToReflQuiver`, and derived
category instances. Assignments include `X`, `S.left`, `T.left`, `T`, `S`,
`DerivedCategoryModule A X`, and `DerivedCategoryModule A S.left`; no competing
candidate or changed provider was isolated between the two forms. Transparency
records show the usual local raise from `instances` to `implicit` while
resolving category data. No coercion insertion is the first divergent event.

No concrete unification constraint both controls the original hR proposition
and remains valid under a transparency change. Therefore T1/T2/T3 sweeps and
a strict frozen F1 replay were not valid experiments here; a global
transparency sweep would not identify an elaborator contribution.

## 5. KERNEL INPUT AND COST

The stored root declaration is an opaque theorem with `hasValue=true`; the
observed S3/S4 type root is equal in the imported-environment snapshots.
This does not measure pre-finalization change. The hR proposition is
under `Eq`, `Quiver.Hom`, `DerivedCategoryModule`, and seven-fold composition.
The slow root has 3,897,905 calls in the READY replay, with comparison and
WHNF work both material. The fresh application-only rerun measured:

| variant | wall | user + system | peak RSS | result |
|---|---:|---:|---:|---|
| original hR | 34.42 s | 33.64 + 1.06 s | 5,688,188 KB | succeeds, expensive |
| direct `restriction_counit` hR | 3.30 s | 2.62 + 0.96 s | 2,876,048 KB | succeeds, cheap |
| preceding `τq` edit only | 34.62 s | 33.82 + 1.07 s | 5,685,356 KB | succeeds, still expensive |

The positive and negative controls preserve the helper and theorem obligation;
the positive control changes the proof-producing interface and therefore the
instantiated proposition representation.

## 6. CHEAP-BOUNDARY INVENTORY

### B1: direct restriction-counit proposition

Boundary kind: named proposition/theorem interface. Current fast conversion:
the same argument-39 application with `restriction_counit A f.left _ _`,
3.30 s. Stored outer head: `Eq`, then `Quiver.Hom` and
`CategoryStruct.comp`; the theorem constant is opaque. Hidden implementation:
the concrete over-object scheme and its derived-category/functor instances.
Punctures: replace the direct proof with
`imageRestriction_counit ... (Over.mk f.left)`, unfold `Over.left`, or rebuild
the concrete proof. Result: the 34.42 s root returns. Status: **fragile**.

### B2: abstract helper/functor boundary

Boundary kind: whole-side theorem boundary with abstract `GT`, adjunctions,
and coherence arguments. Current fast control keeps the helper application
abstract while supplying the direct hR proposition. Hidden implementation:
concrete `ExternalRHom.globalHom`/derived-functor paths under `NatTrans.app`.
Punctures: use the original concrete hR and concrete final handoff. Result:
the argument-39 root and the full Before cost return. Status: **fragile**;
future direct concrete functor vocabulary can reopen the path.

### B3: `Over.left` abbrev boundary

Boundary kind: named data accessor/abbrev inside a dependent proposition.
Current first comparison is cheap only while the direct scheme boundary is
preserved. Hidden implementation is `Comma.left` and the enclosing over-object
data. Punctures: `unfold Over.left`, raw `Over` construction, or concrete
proof reconstruction. The diagnostic control changes the major premise and
restores the expensive family; an isolated `Over.left` share was not measured.
Status: **fragile / partially tested**.

## 7. CONTROL RESULTS

- Original: `imageRestriction_counit ... (Over.mk f.left)`; 34.42 s fresh application replay.
- Perturbed local elaboration: direct `restriction_counit A f.left _ _`; S2 proposition changes at the intended scheme leaf and the replay is 3.30 s.
- Negative control: changing only the preceding `τq` argument leaves the original hR pair and costs 34.62 s.
- Frozen replay: no strict same-root F1/F2 pair was constructible without changing the dependent proposition; no Kernel-metadata-only control is claimed.
- Same root obligation: helper, preceding arguments, and final square remain the same; the positive control intentionally changes the proof proposition interface.

## 8. CONCLUSION

Earliest divergence stage: **S0/S1, confirmed at S2**.
Most likely origin: **source-authored explicit over-object specialization**,
then stored in imported opaque theorem/proof data. Elaborator contribution:
**not demonstrated**; traces show standard assignments but no choice that
changes the relevant representation. Declaration finalization: **not the
earliest origin; S2/S4 transformation unmeasured**. Kernel contribution:
**M1 propagation** dominates the measured
root after the M0 dependent proposition mismatch. Current cheap boundaries
are the direct restriction proposition, abstract helper/functor vocabulary,
and the `Over.left` data accessor; all are fragile under concrete proof or raw
over-object expansion.

Remaining uncertainty: the exact reduction predecessor and exclusive cost of
the `Over.left`/`Comma.left` exposure, and a strict transparency perturbation
that preserves the original argument-39 obligation.

## Audit note and Batch 2 boundary test

The prior "no finalization change" inference compared two views of imported
ConstantInfo; the saved S3 field is finalization-observable-only. The exact
`Over.left (Over.mk f.left)` versus `X` split is supported by the source and
S2 proposition audit. E3 puncture: replace the type-correct direct
`restriction_counit A f.left` proof at argument 39 with the original
`imageRestriction_counit ... (Over.mk f.left)`. The saved application replay
changes from 3.30 s to 34.42 s; the `τq`-only negative control remains 34.62 s.
This tests the proposition interface, not an isolated `Over.left` unfold.
