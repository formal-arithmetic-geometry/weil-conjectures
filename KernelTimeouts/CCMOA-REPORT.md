# Cross-Case Mismatch Origin Audit

## Scope and evidence rule

This is the section 4 synthesis for 17 cases. `KT` means the
`KernelTimeouts` repository and `KP` the `PerfIssues` repository; each case
name below identifies its `EXPERIMENTS-CCMOA.md`, except EtaleHom, whose
reference is `KT/KernelTimeouts/EtaleHomComparisonReversedExact/EXPERIMENTS-MOE.md`.
The case reports identify the exact source revision, Expr path or available
stage limit, reducibility hints, and READY4.2 roots. Current cases use the
pinned Lean 4.35.0 measurement build; the historical cone and Slow Derived
Tensor records identify their Lean 4.33.1 revisions.

Levels: **D** Demonstrated requires an exact stage snapshot, a type-correct
one-factor control that changes the elaborated pair under the same obligation,
and READY4.2 workload counters. **S** Strongly supported has an exact first
divergence and relevant successful control with a remaining confound.
**P** Plausible localizes a divergence without a valid one-factor causal
control. **N** Not observed means the relevant stage was inspected without a
contribution. **U** Unknown means a needed artifact or valid control is
unavailable. A measured fast variant alone is not D.

## Provenance map

| Case (evidence) | Earliest relevant divergence | Primary origin | Elaborator causal? | Finalization causal? | Kernel-exposed latent difference? | Effective boundary | Boundary fragility |
|---|---|---|---|---|---|---|---|
| EtaleHom (KT, MOE reference) | S0/S1 named predicate vs `forall` (D) | Source/API premise (D) | Provider assignment observed; cause N | U | Predicate unfolding, M1 (D) | Whole-proposition transport (D) | Direct premise restores 3.18M calls (D) |
| FiniteBaseChange (KT) | S0/S1 `ProEt` vs instantiated `Site` (D) | Source/API site representation (D) | N | U | `Site` matcher and category descent (S) | Argument-49 transport (D) | Direct handoff restores 239.34M calls (D) |
| F66Adj (KT) | S0/S1 `Over.mk` counit (D) | Source/API specialized proof (D) | N | U | Dependent scheme/functor descent (S) | Direct argument-39 counit (D) | Restoration gives 3.90M calls (D) |
| OrderedSpectralRawLattices (KT) | S2 ring-object provider leaf (S) | Authored R/H/D availability, selected provider bundle (S) | P | U | `Functor.obj` and lattice descent (S) | All-route alignment (S) | Single-route restoration reopens slow path (S) |
| RealPushforward (KT) | S0/S1 polynomial head (D) | `charpolyRev` vs `localPolynomial` API (D) | N | U | Regular-head stalk path (D) | Polynomial-head goal alignment (D) | Original goal restores 17.34M calls (D) |
| RealPurity (KT) | S0 API; S2 ring leaf (S) | Polynomial/object representation; ring leaf insufficient (P) | N | U | Later `Functor.obj`/coercion descent (S) | Whole-polynomial transport (S) | Direct `exact h` slow; other punctures untested (P) |
| ImageHomCounit (KT) | S0 API; S2 raw/wrapper child (S) | Raw vs wrapper endpoint (S) | N | U | Dependent category descent (S) | Full inferred-type alignment, broad control (S) | Direct goal and wrapper-only punctures slow (S) |
| IntegralComparison (KT) | S0 target; S2 provider leaf (S) | API/object path; first provider insufficient (P) | N | U | `Functor.obj`/module descent (S) | Localized endpoint wrapper (S) | Provider alignment ineffective; wrapper risk P |
| NativePullTensor (KP) | S2 `Functor.obj` major premise (S) | Hidden provider/domain representation (S) | P | U | `Exists.choose` domain descent (S) | Extracted endpoint alignment (S) | Reverse endpoint pair slow; root puncture U |
| PR1556 (KP) | S5 exact; S2 unavailable (P) | Concrete comm-shift component (S) | U | U | `comp`/`app` projection descent (S) | Whole-equality cancellation (S) | Concrete component restores slow path (S) |
| PR1625 (KP) | S0 API; S5 pair only (S) | Nested `.app` components (S) | U | U | Projection descent (S) | Whole natural-transformation equality (S) | Direct components slow (S) |
| PR1563 (KP) | S5 observed; S2 unavailable (P) | Concrete `Eq.mpr`/composition vs helper (P) | U | U | Composition continuation (S) | Generic pullback helper (P) | Concrete proof restores target cost (S) |
| PR1624 (KP) | S0 API; S5 pair only (S) | Concrete derived-functor composition (S) | U | U | `Functor.comp` unfolding (S) | Abstract functor helper (P) | Concrete composition slow (S) |
| PR1627 (KP) | S4 generated-law pair; S2 U (P) | Direct generated-field API (S) | N | U | Dependent `homMk`/`id` descendants (S) | `liftOfStr` construction (S) | Direct fields restore slow root (S) |
| PR2122 (KP) | U | Dependent recursor/API bundle is a hypothesis (U) | U | U | `Exists.casesOn` continuation, causal difference U | No cheap boundary established (U) | Untested |
| Derived-completion cone (KT) | S0/S1 naming; original proof path S4 (P) | Inline composition/provider representation (P) | P | U | Monoidal proof descendants (S) | Named diagram (P for original root) | Inline restoration slow (S) |
| Slow Derived Tensor (KT) | S4/S5 exact; metadata change S0 (S) | Declaration hints and Kernel strategy (S) | N | U | Predicate/provider descent (S) | Regular helper heads (S) | Restored abbrevs slow (S) |

The table separates an observed first unequal Expr child from a demonstrated
cause of cost. In particular, RealPurity's ring-leaf and IntegralComparison's
derived-category provider edits change Exprs but retain approximately 17.31M
and 9.43M calls. NativePullTensor's fast replacement operates on an extracted
endpoint, not the original dependent root. ImageHomCounit's `type_of%` goal
copies the whole inferred equality. The PR1625 and PR1624 current-closure
historical replays failed; their historical S2 snapshots and READY4.2
after-counters remain U and support no D cell.

## Triggered Batch 2

No concrete fresh unification constraint was found whose transparency mode
selected a different final Expr. The negative EtaleHom transparency trial is
already in the reference report; no project-wide sweep was run. Distinct
elaborated variants triggered local frozen replays for ImageHomCounit and
RealPushforward. With metavariables instantiated, original/aligned
`Kernel.isDefEq` times were 51,609/<1 ms and 73,666/1 ms respectively;
both variants returned equal. Their case `ccmoa/frozen-results.txt` files
record hashes and limits. These direct timings supplement, but do not
replace, READY4.2 counters or make a broad goal control one-factor.

The RealPurity and IntegralComparison saved same-root instance alignments
already replay distinct Exprs and are negative (unchanged call counts).
OrderedSpectral's one-route restoration, NativePullTensor's reverse endpoint
comparison, and the P2/P4 direct-restoration controls puncture their named
cheap boundaries one at a time. Other speculative boundaries are marked
untested in their case reports. For PR1627, the generated `_proof_2` law has
a stored `homMk`/`id` dependent pair; the source-local S2 attempt did not
finish, so finalization causality remains U. For the cone, stored generated
proof positions lack a matched pre-finalization Expr; finalization causality
also remains U. Neither historical failure was treated as a successful replay.

## Seven answers

1. **Source/API authored:** EtaleHom's named predicate, FiniteBaseChange's
   `ProEt`/`Site`, F66Adj's over-object counit, and RealPushforward's
   polynomial head have D controls and READY4.2 reductions. ImageHomCounit's
   raw/wrapper choice is S because the fast goal copies the entire inferred
   equality. PR1625, PR1624, the cone, and PR1627 visibly choose their
   component/construction APIs at source, but lack a matched one-factor
   historical or generated-field root control (their case reports).
2. **Elaborator-selected:** OrderedSpectral records R/H/D-dependent provider
   Exprs at S2; NativePullTensor records a hidden `Functor.obj` premise;
   RealPurity and IntegralComparison record instance leaves. No case
   demonstrates that an Elaborator-only selection caused the measured
   workload: the latter two leaf replacements leave 17.31M and 9.43M calls
   unchanged (their `ccmoa` counter files).
3. **Finalization:** No case proves a material S2-to-S4 change caused its
   expensive pair. PR1627 has three stored generated law constants and a
   `_proof_2` binder asymmetry; the cone has stored proof positions. Neither
   has the matching pre-finalization Expr, so both causal cells are U
   (PR1627 and cone reports).
4. **Kernel exposure:** EtaleHom unfolds a regular predicate; FiniteBaseChange
   unfolds `Site`; NativePullTensor descends through abbrev `Functor.obj`;
   PR1625 descends through nested `NatTrans.app`; Slow Derived Tensor changes
   behavior with helper hints. These expose existing representations rather
   than establish a single Kernel-created origin (case S4/S6 records).
5. **Fragile boundaries:** Whole-premise transport, direct counit use,
   polynomial-head alignment, named diagrams/generic helpers, and whole
   natural-transformation equalities all have saved inverse or concrete
   punctures. Provider sharing and several proof-field/let boundaries remain
   untested; PR2122's dependent telescope is a validity requirement, not an
   effective cheap boundary (case E inventories).
6. **Demonstrated source controls:** EtaleHom 3,180,470 to 7,039 calls;
   FiniteBaseChange 239,340,712 to at most 19,783 in its threshold-zero
   control; F66Adj 3,897,905 to at most 2,881; RealPushforward 17,340,236
   to a largest recorded 2,873-call root. The P2 fast counts use a different
   capture scope, as their reports state; each full proof and restoration was
   checked. ImageHomCounit's 6,359,958 to 2,881 calls is S because its goal
   alignment changes more than the isolated endpoint child.
7. **Still plausible or unknown:** OrderedSpectral has a route-bundle
   confound; NativePullTensor lacks an aligned original-root replay;
   RealPurity and IntegralComparison have negative leaf controls; PR1556,
   PR1563, PR1625, and PR1624 lack historical S2/after-counter pairs;
   PR1627 and the cone lack matched pre-finalization law Exprs; PR2122
   lacks a localized first Expr divergence and a valid standalone dependent-branch replay. Their case reports
   state which additional control would be required, without assigning a
   project-wide origin.
