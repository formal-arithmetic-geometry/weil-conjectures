# CCMOA Batch 1: NativePullTensor

Case: `PerfIssues/Current/NativePullTensor`  
Root family: the final inferred/declared conversions for
`nativePullTotalTensor` and its adjacent declarations, with the two
`Exists.choose` application-domain conversions under the original 12-binder
telescope.

The measurements reuse the existing MOE/AD/IM/M1P artifacts and the
read-only current measurement build. No finished experiment was rerun.

## A. S0-S6 stage audit

### S0: source

The source writes the same `Exists.choose`-based construction and the same
`Functor.comp` / `Functor.obj` surface operations on the value and declared
type sides. The relevant functor, category, object, and proof providers are
implicit. The final conversion is checked only after all 12 preceding binders
have been opened.

### S1: macro-expanded syntax

No relevant macro or notation change was recorded. The source-level
application family is the same on both sides; the hidden provider/domain
choice is not visible in source spelling.

### S2: elaborated expressions

The first structural difference at the expensive endpoint is under
`Functor.comp` at the `Functor.obj` application (endpoint argument 6 on the
source endpoint and 7 on the target endpoint). Both outer heads are the same
`Functor.obj`; the first unequal child is provider argument 4 of the
corresponding concrete `Functor.uncurry` major premise. This is the exact
hidden provider/domain difference.

After all preceding arguments are instantiated, the same difference appears
in two `Exists.choose` domain checks:

1. the predicate argument's inferred `Iso ... -> Prop` type versus the
   instantiated `Exists.choose` binder domain;
2. the existential proof argument's `Exists ...` type versus its instantiated
   binder domain.

Each argument's own type checks in at most 6 ms; the domain conversions take
22,998 ms and 23,068 ms. The saved structural walk records the concrete
functor/provider terms and the first positional proof/provider differences,
but those later proof leaves are not independently timed causes.

### S3: declaration finalization

The imported declaration is finalization-observable-only. No generated proof
field is needed to locate the first provider difference, and no pre-finalization
term is available for an imported declaration.

### S4: stored environment

Relevant metadata is:

| Constant | Kind / hint |
| --- | --- |
| `CategoryTheory.Functor.obj` | `def`, `abbrev`; body exposes projection `Functor.0` |
| `Functor.comp` | regular definition |
| `nativePullTotalTensor` and adjacent declarations | imported theorem/definition records; values are stored and replayed |

The `Functor.obj` abbreviation is the boundary that exposes the concrete
major premise. The two endpoint expressions are type-correct and
definitionally equal, but their provider representation is not structurally
shared.

### S5: Kernel root pair

The main READY4.2 root has 2,685,580 calls, depth 81,
22,332.787 ms comparison-exclusive, and 11,745.588 ms reduction-exclusive.
It records 21 Pi-domain comparisons, 32,060 proposition comparisons, and
537,023 proof-irrelevance attempts. The two `Exists.choose` domain checks
reproduce the same 23-second scale.

### S6: Kernel exposure

The provider mismatch is exposed through `Functor.obj` projection reduction,
then `Functor.map`, `NatTrans.app`, category composition, and dependent proof
fields. READY4.2 classifies the root as 98.164% M1, 0.318% M2, and 1.517%
Matched by exclusive time. This is Kernel exposure of an S2 representation
difference; it is not an instance leaf proved to be the only cause.

**First-divergence conclusion:** earliest relevant stage S2; active in the
`Exists.choose` application domains and endpoint `Functor.obj` pair.
Evidence: **Strongly supported**.

## B. One-factor controls

### B1. Major-premise alignment

For each endpoint, the control replaces only `Functor.obj` argument 4 on the
right with the corresponding left major-premise expression. The replacement
is Kernel-checkable and the aligned object type is structurally equal to the
original right object. The outer `Iso`, endpoint, object, consumer, telescope,
and root obligation are retained.

| Pair | Expr change | READY4.2 / measured result |
| --- | --- | --- |
| Original endpoint 2 | Original left provider vs original right provider | 2,685,580 calls; 22,332.787 ms comparison-exclusive; 34.078 s root wall |
| Aligned endpoint 2 | Only provider argument 4 replaced | 0 ms endpoint conversion; no counter record emitted because it is below the 100 ms threshold |
| Original endpoint 3 | Original left provider vs original right provider | Same root family; 23,068 ms `Exists.choose` domain conversion |
| Aligned endpoint 3 | Only provider argument 4 replaced | 0 ms endpoint conversion; below counter reporting threshold |
| Restored right/aligned | Reverse comparison restores the original provider difference | 11,363 ms, equal; confirms reversibility |

This is an isolated one-child diagnostic on the extracted endpoint objects.
It does not replay the original 12-binder dependent root with an elaborated
source variant. The aligned endpoint emitted no READY4.2 counter record, so
the exact aligned call count is unknown, even though its timed conversion was
below the reporting threshold.

### B2. Regular/abbrev representation control

Both sides are wrapped with the same body while changing only the wrapper
representation and its reducibility hint. All four wrappers are Kernel-
checkable. The saved matrix is:

| Pair | Result |
| --- | ---: |
| Original raw `Functor.obj` | 11,388 ms |
| Same-body regular / regular | 0--1 ms |
| Same-body abbrev / abbrev | 11,251--14,134 ms |
| Mixed regular / raw | 11,295--13,637 ms |
| Mixed abbrev / raw | 11,299--15,583 ms |

This control changes metadata and expression heads deliberately; it shows
why the aligned provider boundary is cheap under the installed Kernel policy.
It does not by itself identify which hidden provider was chosen by the
Elaborator.

### B3. `Exists.choose` domain controls

The `ValuePrefixes` control keeps the original 12-binder telescope and adds
the `Exists.choose` arguments one at a time. The type argument costs 3 ms; the
predicate domain costs 22,998 ms; the existential proof domain costs 23,068
ms. The completed prefix is about 47.5 s. These are type-correct controls of
the actual instantiated domains, not comparisons against the generic binder.

**B evidence:** **Strongly supported** for the provider-major-premise boundary
and **Demonstrated as a location observation** for the instantiated
`Exists.choose` domains. No one-factor root-level causal claim is demonstrated.

## C. Targeted elaborator provenance

The targeted source probes observe the implicit functor/category/provider
arguments after the 12 binders are instantiated. The selected `Functor.obj`
constant is the same on both sides; its immediate stored body is the
`Functor.0` projection and its hint is `abbrev`. The source controls do not
produce a genuine alternate implicit assignment with the same final
telescope. No transparency perturbation or coercion insertion changes the
final stored expression while preserving the root obligation.

Thus:

- the hidden provider difference is present in the S2 Expr;
- instance/implicit synthesis supplies concrete terms, but alternate-provider
  causality is not demonstrated;
- the regular/abbrev result is a Kernel metadata/reducibility effect, not an
  Elaborator provenance result;
- no broad transparency sweep is warranted.

**C evidence:** **Plausible** for provider selection as a source of the S2
terms; **Not observed** for a causal transparency, coercion, or alternate
instance assignment.

## D. Declaration finalization

The stored declarations are imported and their pre-finalization terms are not
available. The first mismatch is already present in the replayed stored
value/type pair and in the instantiated `Exists.choose` domains. No generated
field or finalization-only change was isolated.

**D evidence:** **Not observed** as a causal contribution; pre-finalization
identity is **Unknown**.

## E. Cheap-but-fragile boundary inventory

| Boundary | Current cheap behavior | Puncture | Status |
| --- | --- | --- | --- |
| `Functor.obj` abbreviation over a concrete functor | A shared regular major premise makes the endpoint conversion immediate | Use independently elaborated functor providers or expose the projection | **Fragile but effective** |
| `Functor.comp` outer constructor | Same outer head keeps the mismatch below the endpoint arguments | Inline/rebuild the composition with different provider paths | **Untested as an independent cause** |
| `Exists.choose` instantiated domain | Prefix construction is cheap until the predicate/proof domain is compared | Change the preceding provider or telescope representation | **Fragile; expensive when punctured** |
| Generated proof/provider fields | Many later proof leaves are cheap individually but recur in M1 descent | Reconstruct concrete fields or mix wrapper/raw vocabulary | **Untested; not shown primary** |

## Synthesis

| Case | Earliest divergence | Primary origin | Elaborator causal? | Finalization causal? | Kernel-exposed latent difference? | Effective boundary | Boundary fragility |
| --- | --- | --- | --- | --- | --- | --- | --- |
| NativePullTensor | S2 | Hidden provider-major-premise representation under `Functor.obj` / instantiated `Exists.choose` domains (**Strongly supported**) | Plausible | Unknown | Strongly supported | Major-premise alignment plus regular/abbrev boundary (**Strongly supported**) | Strongly supported: restoring the endpoint provider pair restores the 11--23 s path |

The endpoint diagnostic supports a representation and reducibility mechanism
at the Kernel boundary. It does not justify treating one instance leaf as the
sole origin: the expensive pair is embedded in a dependent telescope, and
later proof/provider fields contribute to the broad M1 tree.

## Audit note and Batch 2

The `HintAlignment` control changes only argument 4 of an extracted
`Functor.obj`, and `Kernel.check` confirms its object type. It does not keep
the complete original `Exists.choose` telescope or consumer. The recorded
READY4.2 counters cover the original root, not the aligned endpoint. The
regular/abbrev matrix also changes both expression heads and metadata.
These facts lower the causal and fragility cells to Strongly supported.
The saved reverse comparison (11,363 ms) punctures the endpoint alignment
one boundary at a time. A source-level frozen replay was not available:
there is no second same-telescope elaborated Expr variant. No concrete
transparency constraint selecting a different Expr was found.

