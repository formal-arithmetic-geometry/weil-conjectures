# CCMOA report: FiniteBaseChangeRestrictionMateTransport

Revision: Lean 4.35.0 / Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
Declaration: `finite_base_change_restriction_mate_transport`.
Root: private `transport_from_unit`, proof argument 49 (`hb`).
Source snapshot: `0676f555de6`; conversion record: `FB-hb-49-v1`.

This report reuses the MOE snapshots and the READY4.2 application and
counter runs. Raw snapshots copied for this report are in `ccmoa/`.

## A. S0--S6 stage audit

### S0: source

The theorem application supplies a concrete proof `h` after 48 category,
instance, equivalence, adjunction, functor, isomorphism, and mate arguments.
The helper's argument-49 domain is therefore instantiated by those actuals;
it is not the generic helper binder. The supplied proposition uses
`Scheme.ProEt X`, while the helper domain uses the mode-indexed `Site` form.

### S1: macro-expanded syntax

No relevant macro change was found. The isolated pair remains
`Scheme.ProEt moeX` on the left and `Site .ordinary moeX` on the right.

### S2: elaborated expression

The exact isolated pair has these structural nodes:

| side | root hash | root/fn | root/fn kind |
| --- | ---: | --- | --- |
| actual | `881746797` | `AlgebraicGeometry.Scheme.ProEt` | `const` |
| expected | `259809862` | `Site` applied to `Mode.ordinary` | `app` |

The comparer reports `first-divergence=path=root/fn`, `kind=kind`, with the
same `moeX` argument on both sides. In the actual instantiated `hb` type the
relevant path is `forall` / `Eq` / `Quiver.Hom` / `ProjectionRestriction.Mod`
and then the site argument. No first divergent implicit, coercion, or instance
child was observed.

### S3: declaration finalization

The helper and `Site` declarations are imported. Their S3 records are therefore
`finalization-observable-only`; the pre-finalization term is unavailable. No
generated proof constant was observed on the selected first-mismatch path.

### S4: stored environment

`Site` is a regular definition with hint `regular:20`; `Scheme.ProEt` is a
regular definition with hint `regular:19`. The stored `Site` value contains a
mode matcher whose ordinary branch is `Scheme.ProEt`. Type/value nodes and
hashes are in `ccmoa/S2-S4-site-proet.snapshot`.

### S5: kernel root pair

The checked root is argument 49 (`hb`) after the 48 preceding actuals. Both
sides have a `forall M : FiniteModules A X'` equality-square shape. The first
active mismatch is the `Quiver.Hom` scheme leaf
`Scheme.ProEt X` versus `Site .ordinary X`; the site leaf occurs on both
equality sides.

### S6: kernel exposure and cost

The READY4.2 original root has 239,340,712 recursive calls, maximum depth 87,
150,477,480 failure calls, 813.896 s comparison-exclusive time, and 0.076 s
WHNF-exclusive time. Aggregate labels are M1: 130,197,227 calls / 72.869%
exclusive time; M2: 25.661% time; Matched: 1.419% time. The first latent
exposure is delta reduction of regular `Site`, followed by its ordinary mode
match and the category continuation. The repeated descendant path includes
`CategoryStruct.comp -> LinearMap.comp -> PresheafOfModules.Hom.proj ->
NatTrans.app`.

The mismatch is active at S5; only the `Site` body is latent until S6. The
M0/M1/M2 interpretation is one root entry at `hb`, repeated dependent
comparison propagation, then the reduction cascade. These labels are aggregate
provenance labels, not an exclusive per-site cost attribution.

## B. One-factor controls

### Positive control: whole-proposition transport

Original argument expression: the concrete `h`, whose instantiated premise
contains `Scheme.ProEt X`.

Control expression: `hb := fun M => by transport_exact h M`. This changes only
the proof-argument representation: the helper receives a proof of its exact
instantiated `Site .ordinary` proposition. The helper, all 48 preceding
actuals, consumer, local context, and final obligation remain the same.

| run | exact relevant Expr result | READY4.2/counter result |
| --- | --- | ---: |
| original | `Scheme.ProEt X` vs `Site .ordinary X` at the dependent site leaf | 239,340,712 calls; 813.896 s comparison-exclusive |
| transported | argument proposition is the instantiated expected proposition; no M0 site mismatch | 19,783 calls in the threshold-zero instrumented control; diagnostic 4.40--4.80 s |
| restored original | original concrete proposition reinstated | 239,340,712 calls again |

The control is type-correct and changes the elaborated proof-argument type, not
source spelling alone. The threshold-zero control count is the largest root in
that control file, while the full original count is the authoritative
READY4.2 root; they are reported with that instrumentation caveat.

### Negative elaboration control

An isolated unification hint for `Site .ordinary X` versus `X.ProEt` leaves the
normalized pair digest unchanged (`695947a17c9ebb043bf4449d783c07a1f4c5a89a5a18c39c8b7d317e39ce382a`).
The checked run still has 239,340,712 total calls, 150,477,480 failures, and
19,747,209 lazy-delta calls. This is negative evidence against a hidden
elaborator-selected representation change, not a causal control.

## C. Elaborator provenance

Conditional C was not triggered by the first-divergence rule: the mismatch is
already in S0/S1 and no instance, implicit, or coercion child is first. The
expected domain is created only after the preceding 48 actuals are
instantiated. Available traces show no assignment that changes the site leaf;
the unification-hint replay preserves the S2 pair and kernel counters.
Evidence level: **Not observed** for an Elaborator causal contribution.

## D. Declaration finalization

No true pre-finalization versus stored comparison is possible for the imported
helper or `Site` declaration. The imported S3 record is explicitly
observational-only, and no generated proof field is on the first path.
Finalization is therefore not localized as the first origin, but a causal
absence claim is not made. Evidence level: **Unknown**.

## E. Cheap-but-fragile boundaries

| boundary | current outer head and reason | puncture and result | status |
| --- | --- | --- | --- |
| `B-SITE` | regular `Site mode X` (`regular:20`) reduces its ordinary matcher to `ProEt` (`regular:19`) in an isolated conversion | unfold `Site`, concrete `simp`/`rw`, or rebuild the category provider; the descendant leaf becomes `Scheme.instCategoryProEt` vs `instCategorySite` | fragile but effective |
| `B-HB-TRANSPORT` | whole-proposition transport supplies the helper's exact dependent premise before kernel comparison | replace transported `hb` by concrete `h`; the 239,340,712-call root returns | fragile but effective |
| `B-ABSTRACT-HELPER` | explicit generic helper/functor/equivalence parameters keep concrete data outside the dependent comparison | inline concrete functors or reconstruct category instances; the original large `hb` path reopens | fragile but effective |

The effective boundary demonstrated by B is `B-HB-TRANSPORT`; the `Site`
definition is a cheap representation boundary whose later reduction remains
fragile under ordinary refactoring.

## Synthesis row

| case | earliest divergence | primary origin | Elaborator causal? | Finalization causal? | Kernel-exposed latent difference? | effective boundary | boundary fragility |
| --- | --- | --- | --- | --- | --- | --- | --- |
| FiniteBaseChangeRestrictionMateTransport | S0 (retained through S1/S2) | source/API-authored concrete `ProEt` vs instantiated mode-indexed `Site` | Not observed | Unknown | Strongly supported: `Site` matcher/category descendants are exposed at S6 | Demonstrated: whole-`hb` transport removes the mismatch and workload | Demonstrated: restoration reopens the measured root; fragile but effective |

## Evidence limits

The whole-`hb` control changes the dependent proof proposition while preserving
the surrounding consumer and telescope; it is the valid representation control
for this case, not an isolated cost of the `Site` definition. A same-root
different-hints replay and exclusive costs for the `Site` delta versus its
category-instance continuation were not obtained.
