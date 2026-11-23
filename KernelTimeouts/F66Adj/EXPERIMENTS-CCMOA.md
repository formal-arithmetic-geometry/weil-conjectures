# CCMOA report: F66Adj

Revision: Lean 4.35.0 / Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
Declaration: `imageHomIso_naturality`.
Root: helper `homIso_naturality_of_counit`, proof argument 39 (`hR`).
Source snapshot: `f66ad18a9ed`; conversion record: `F66-hR-39-v1`.

This report reuses the completed MOE snapshots and READY4.2 application and
counter runs. Raw snapshots copied for this report are in `ccmoa/`.

## A. S0--S6 stage audit

### S0: source

The original application supplies
`imageRestriction_counit A _ _ (Over.mk f.left)` as `hR`. The helper's
argument-39 proposition depends on the first 38 actual arguments and contains
a local scheme variable. The type-correct control supplies
`restriction_counit A f.left _ _`. The explicit `Over.mk` is source syntax;
no macro is responsible for it.

### S1: macro-expanded syntax

Expansion preserves the two relevant forms: the original has
`imageRestriction_counit ... (Over.mk f.left)` and the control has
`restriction_counit ... f.left`. No macro-generated representation change was
found.

### S2: elaborated expression

The proof-term snapshot reports `first-divergence=path=root/arg/arg`,
`kind=kind`, left `app`, right `fvar`. The exact instantiated proposition
audit localizes the first material type leaf to:

```text
actual:   Over.left (Over.mk f.left)
expected: the local scheme variable X
```

The path is `Eq type -> Quiver.Hom argument 1 -> DerivedCategoryModule scheme
argument`. The leaf repeats on both sides of the seven-argument
`CategoryStruct.comp` equality. The raw S2 actual/expected snapshots and
comparer output are in `ccmoa/`.

### S3: declaration finalization

The source-variant scratch declaration exposes only finalization-observable
data after import. Its root type hash is `1338557591` and baseline value hash
is `2540733603`. The counit theorem constants are opaque. No pre-finalization
term for the imported declaration was captured, and the bounded auxiliary scan
does not support an auxiliary-declaration claim.

### S4: stored environment

The baseline stored declaration retains type hash `1338557591` and value hash
`2540733603`; both counit theorem constants are opaque with `hasValue=true`.
The fixed current declaration has value hash `3419966969`, which is a source
variant and not evidence for a finalization-generated hR mismatch. The S4
metadata snapshots are in `ccmoa/S4-baseline.snapshot` and
`ccmoa/S4-current.snapshot`.

### S5: kernel root pair

The checked root is argument 39 (`hR`) after the first 38 dependent arguments.
The first active mismatch is the scheme leaf
`Over.left (Over.mk f.left)` versus `X` in the `DerivedCategoryModule` type.
This is M0; the proof bodies themselves are not the compared root.

### S6: kernel exposure and cost

The READY4.2 original root has 3,897,905 recursive calls, maximum depth 121,
22.801 s comparison-exclusive time, and 21.373 s WHNF-exclusive time. The
complete aggregate labels are M1: 2,961,163 calls / 99.803% time; M2: 0.000%
time; Matched: 0.197% time. Representative M1 descendants include
`DFunLike.coe`, `CategoryTheory.Functor.proj`, and linear-map/additive
projections. The M2 nodes are concrete versus site-derived monoidal proof
constants exposed by initial WHNF. Exact reduction order from `Over.left` to
each descendant is not recorded.

## B. One-factor controls

### Positive control: direct restriction-counit proposition

Original hR expression:
`imageRestriction_counit A _ _ (Over.mk f.left)`.

Control hR expression:
`restriction_counit A f.left _ _`.

This changes the targeted proof-producing representation at argument 39. The
helper, all 38 preceding actuals, local context, consumer, and final square
remain the same; the instantiated hR proposition changes from the over-object
scheme leaf to the local scheme expected by the helper.

| run | exact Expr change | READY4.2/counter result |
| --- | --- | ---: |
| original | `Over.left (Over.mk f.left)` vs `X` at `DerivedCategoryModule` scheme leaf | 3,897,905 calls; 22.801 s comparison + 21.373 s WHNF |
| direct control | S2 proof child changes `app` -> `fvar`; proposition uses the expected scheme leaf | 2,881 calls in the threshold-zero largest control root; fresh replay 3.30 s |
| restored original | original `imageRestriction_counit ... (Over.mk f.left)` restored | 3,897,905 calls; fresh replay 34.42 s |

The positive and restored runs are type-correct. The direct control changes the
elaborated argument proposition, so it is not a source-spelling-only edit.
The threshold-zero control count and full READY4.2 root use different capture
scopes and are reported with that caveat.

### Negative preceding-argument control

Changing only the preceding tensor-isomorphism (`tauq`) argument leaves the
original hR pair and costs 3,901,014 calls / 34.62 s. It does not cut the
argument-39 mismatch and is a negative control for the targeted boundary.

## C. Elaborator provenance

The scoped Meta traces show the same ordinary assignments and provider routes
for the original and direct terms: `inst` for `CommRing A`,
`Scheme.instCategory`, `instCategoryOver`, `catToReflQuiver`, and derived
category instances. Assignments include `X`, `S.left`, `T.left`, `T`, `S`,
`DerivedCategoryModule A X`, and `DerivedCategoryModule A S.left`; no competing
candidate changes the relevant scheme representation. Transparency rises from
`instances` to `implicit` during ordinary category resolution, but no concrete
constraint both preserves the original hR obligation and changes its provider.

No transparency sweep or strict frozen replay was therefore valid. Evidence
level: **Not observed** for an Elaborator causal contribution.

## D. Declaration finalization

S3/S4 are imported/finalization-observable-only for the relevant declaration;
the stored hashes do not provide a pre-finalization term. No generated proof
field was identified on the first mismatch path. Finalization is not the
earliest origin, but its causal absence is not established. Evidence level:
**Unknown**.

## E. Cheap-but-fragile boundaries

| boundary | current outer head and reason | puncture and result | status |
| --- | --- | --- | --- |
| `B1-direct-counit` | named direct restriction-counit proposition keeps the instantiated scheme aligned; opaque theorem outer head under the same `Eq`/`Quiver.Hom` skeleton | replace it with `imageRestriction_counit ... (Over.mk f.left)`; 34.42 s and the 3,897,905-call root return | fragile but effective |
| `B2-abstract-helper` | abstract helper/functor vocabulary keeps concrete `ExternalRHom` data outside the dependent comparison | use original concrete hR or concrete final handoff; the argument-39 root reopens | fragile but effective |
| `B3-Over.left` | `Over.left`/`Over.mk` is a named data-accessor boundary in the dependent proposition | unfold the accessor, use raw `Over`, or reconstruct the concrete proof; expensive family returns, but its exclusive share is unmeasured | fragile, partially tested |

The effective boundary demonstrated by B is `B1-direct-counit`. The
`Over.left` boundary is a likely amplifier but is not assigned an isolated
kernel time share.

## Synthesis row

| case | earliest divergence | primary origin | Elaborator causal? | Finalization causal? | Kernel-exposed latent difference? | effective boundary | boundary fragility |
| --- | --- | --- | --- | --- | --- | --- | --- |
| F66Adj | S0/S1 (confirmed at S2) | source/API-authored explicit over-object specialization | Not observed | Unknown | Strongly supported: dependent `Over`/functor descendants are exposed at S6 | Demonstrated: direct restriction-counit hR changes the pair and workload | Demonstrated: restoring concrete hR reopens the measured root; fragile but effective |

## Evidence limits

The direct hR control preserves the helper and surrounding dependent telescope
while changing the proof-producing interface. It demonstrates the argument-39
boundary, not an isolated exclusive cost for `Over.left` or its internal
`Comma.left` reduction. A same-root metadata-only replay was not constructed.
