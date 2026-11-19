# Workplan Cross-Case Validation

This report merges the eight KernelTimeouts cases with the seven PerfIssues
cases. The KernelTimeouts records are staged in this checkout under
`../staging/<case>/WORKPLAN-EXPERIMENTS.md`; their branch paths are
`KernelTimeouts/<case>/WORKPLAN-EXPERIMENTS.md`. PerfIssues records are cited
by their directory names on `dataset/perf-issues`.

The matrix records observations from the case records. Interpretations and
confidence limits are kept in the sections below. A control is called
successful only when ordinary Kernel checking was enabled, the same cost site
was measured, and the theorem obligation was preserved.

## 7.1 Cross-case matrix

| Case | First mismatch | Conversion context | Successful control | Mechanism supported | Remaining uncertainty |
|---|---|---|---|---|---|
| [NativePullTensor](dataset/perf-issues:PerfIssues/Current/NativePullTensor/WORKPLAN-EXPERIMENTS.md) | `Functor.obj` major premise under `Functor.comp`; regular versus `abbrev` field path | endpoint and dependent `Exists.choose` domain conversions | `NPT-major-align` and same-body regular/regular control | accessor major-premise alignment plus reducibility-hint interaction | exact internal Kernel sequence; whether `_proof_3` contributes |
| [#1556, `P1556-closing-proof`](dataset/perf-issues:PerfIssues/Old/PR1556-AmbientCounterexampleCoproducts/WORKPLAN-EXPERIMENTS.md) | `NatTrans.app` concrete major premise | generated `congr` proposition domain | `P1556-nat-major` | accessor-induced dependent proposition conversion | inner proof details beyond the aligned major premise |
| [#1563, `P1563-eq-mpr-domain`](dataset/perf-issues:PerfIssues/Old/PR1563-RawModuleScalarPullback/WORKPLAN-EXPERIMENTS.md) | nested `CategoryStruct.comp` argument 6 | `Eq.mpr` proof domain | `P1563-comp-args` localizes the nested cost; no complete one-factor speedup | same-head nested argument mismatch | projection contribution versus remaining nested data work |
| [#1624, `P1624-iso-trans-last-domain`](dataset/perf-issues:PerfIssues/Old/PR1624-IntegersSheafHomologyTower/WORKPLAN-EXPERIMENTS.md) | `Functor.comp` endpoint arguments 2/3/6/7 | final `Iso.trans` domain | `P1624-comp-args` records the endpoint; isolated alignments are ill-typed | enclosing-definition-mediated same-head definitional equality | dependent multi-argument alignment and exact layer below `Functor.mk` |
| [#1625, `P1625-result-lhs`](dataset/perf-issues:PerfIssues/Old/PR1625-TensorSheaf/WORKPLAN-EXPERIMENTS.md) | `NatTrans.app` concrete major premise | final inferred/declared result type | `P1625-major-align` | accessor-induced final type conversion | inner nested major premise |
| [#1627, `P1627-generated-law`](dataset/perf-issues:PerfIssues/Old/PR1627-WeilSheafTransport/WORKPLAN-EXPERIMENTS.md) | instantiated `id` proof proposition | generated law field value | generated-prefix reconstruction locates the site; no valid replacement control | dependent proof-domain conversion | first nested proposition term |
| [#2122, `P2122-value`](dataset/perf-issues:PerfIssues/Old/PR2122-DiagonalTraceFiniteEtaleIntegralBoundary/WORKPLAN-EXPERIMENTS.md) | branch-local pair under `Exists.casesOn` | stored theorem value | branch-boundary checks in `G4-B` | branch-boundary work only | exact final dependent branch pair and recursor causality |
| OrderedSpectralRawLattices | `Semifield.toCommSemiring` versus `CommRing.toCommSemiring`, then domain-instance leaves | final helper-result/goal conversion | `C1-RHD`, disabling all three competing paths | concrete instance-route interaction | exact Kernel order and third let value |
| EtaleHomComparisonReversedExact | named predicate/wrapper and nested `DerivedCategoryModule` versus raw domain; later `EtaleHomLeft` versus `Functor.comp` | helper argument 26 proposition domain | `B1-T`, exact expected proposition transport | multilevel dependent proposition alignment | which `Functor.comp` argument dominates after wrapper exposure |
| FiniteBaseChangeRestrictionMateTransport | `Scheme.ProEt` versus `Site .ordinary`, then category-instance leaves | helper argument 49 proof domain | `B2-T`, exact expected proposition transport | dependent site and category-instance representation | whether site and category alignment alone suffice |
| F66Adj | `Over.left (Over.mk f.left)` versus local scheme | helper argument 39 proof proposition | `B3-R`, direct `restriction_counit` argument | accessor-bearing proof-proposition representation | isolated share of `Over.left` versus changed proof interface |
| ImageHomCounit | raw `DerivedCategory` versus `DerivedCategoryModule`, followed by nested wrapper/raw difference | final inferred-type/goal conversion | `C2-I`, exact inferred target with unchanged proof | multilevel endpoint representation | dominant nested endpoint or instance |
| IntegralComparisonPullbackRealizationShifts | `integralTowerHasDerivedCategory` versus `integralOperationsCommHasDerivedCategory`, then `FullSubcategory` versus `CochainComplex` | explicit `change` goal conversion | no cost-reducing instance-leaf control; `C3-I` changes the pair only | first instance leaf is insufficient; deeper functor-object mismatch is implicated | causal child under `Functor.obj` |
| RealPurity | `Field.toCommRing` versus `AlgebraicClosure.instCommRing`, then `Functor.obj` versus local `P` | rewritten `h` type versus goal at `exact h` | no cost-reducing ring control; `C4-B` moves the first mismatch | ring leaves are insufficient; deeper object representation is implicated | causal object path |
| RealPushforward | `LinearMap.charpolyRev` versus `FrobeniusModule.localPolynomial` | final rewritten proof type/goal conversion | `RP-REF`, aligned polynomial goal | necessary initial regular-head unfolding | downstream stalk/module comparison |

## 7.2 Cross-case questions

### 1. Do several cases share the same first mismatch shape?

**Observation.** Yes. Three repeated shapes are visible. The accessor shape
appears in NativePullTensor (`NPT-endpoint-args`, `NPT-major-align`), #1556
(`P1556-comp-args`, `P1556-nat-major`), and #1625 (`P1625-comp-args`,
`P1625-major-align`). Dependent proposition or instantiated-domain shape
appears in EtaleHom (`B1-D`, `B1-T`), FiniteBaseChange (`B2-S`, `B2-T`),
F66Adj (`B3-L`, `B3-R`), and #1627 (`P1627-proof1-prefix`,
`P1627-proof2-prefix`). Same-head nested composition appears in #1563
(`P1563-eq-args`, `P1563-comp-args`) and #1624 (`P1624-iso-args`,
`P1624-comp-args`).

The remaining cases expose concrete instance or wrapper paths: OrderedSpectral
(`C1-R`, `C1-RH`, `C1-RHD`), ImageHom (`C2-W`, `C2-I`), IntegralComparison
(`C3-I`), and RealPurity (`C4-L`, `C4-R`, `C4-B`). RealPushforward (`RP-REF`)
is the regular-head unfolding reference. #2122 (`G4-B`) is the branch-local
case and remains unclassified.

**Interpretation.** The repeated shapes support mechanism families, but a
first structural difference is a location, not automatically the cause.
The negative wrapper and instance controls show this explicitly.

**Evidence level.** Confirmed as a classification of observed first
mismatches; causal strength is given by the controls in the next question.

### 2. Does the same kind of control remove the cost in more than one case?

**Observation.** Yes, in two especially clear groups.

* Exact instantiated proof-proposition alignment makes the same application
  cheap in EtaleHom (`B1-T`, 28.92 s to 3.40 s), FiniteBaseChange (`B2-T`,
  timeout to 4.40 s), and F66Adj (`B3-R`, 34.72 s to 3.40 s). The F66Adj
  replacement also changes the proof-producing interface, so its accessor
  leaf is not isolated.
* Major-premise alignment removes the same conversion in #1556
  (`P1556-nat-major`, 49.548 s to 0 ms), #1625 (`P1625-major-align`,
  95.869 s to 0 ms), and NativePullTensor (`NPT-major-align`, about 11.4 s
  to 0 ms). NativePullTensor additionally has the same-body reducibility
  matrix (`NPT-same-body-hints`), where regular/regular is immediate and
  `abbrev` paths remain slow.

Full representation alignment also succeeds in ImageHom (`C2-I`, 54.94 s to
2.60 s), OrderedSpectral (`C1-RHD`, timeout to a checked result), and
RealPushforward (`RP-REF`, timeout to 3.00 s), but these controls align a
larger expression and are not one-leaf controls.

**Interpretation.** Repeated response to the same controlled change supports
shared mechanism families. The exact-proposition family is the strongest
cross-case result; accessor alignment is independently reproduced three
times.

**Evidence level.** Confirmed for the listed controls. It does not establish
that every case in a family has the same first Kernel reduction.

### 3. Are different low-level unfold counters downstream consequences of the same high-level mismatch?

**Observation.** The data are consistent with that interpretation but do not
measure it directly. Aligning the first wrapper or instance leaves cost in
EtaleHom (`B1-D`, `B1-W`), ImageHom (`C2-W`), IntegralComparison (`C3-I`),
and RealPurity (`C4-B`), while moving the first visible difference deeper.
RealPushforward (`RP-REF`) shows that one initial regular-head reduction is
necessary, but its downstream stalk/module path is not traced. NativePullTensor
explicitly records large `Functor.obj`/`Functor.map` counters as downstream
observations rather than evidence of the first decision (`NPT-same-body-hints`).

**Interpretation.** A shared high-level representation mismatch can expose
different concrete children, so counter names should not be promoted to
independent causes. The permitted ordinary probes cannot establish the
Kernel's internal reduction order.

**Evidence level.** Strongly supported as a model by the moved first
mismatches and negative controls; not confirmed as a counter-level causal
claim.

### 4. Do same-head argument failures and dependent-domain failures reduce to the same underlying representation difference?

**Observation.** They meet at the application boundary. #1624 and #1563
have shared outer heads but expensive complete endpoint/composition checks
(`P1624-comp-args`, `P1563-comp-args`). EtaleHom, FiniteBaseChange, and F66Adj
encounter the same kind of representation discrepancy after preceding
arguments instantiate a dependent proof domain (`B1-T`, `B2-T`, `B3-R`).
The controls make a complete expected proposition or major premise cheap even
when independently checking constituent arguments was cheap.

**Interpretation.** Yes at the mechanism-family level: both are failures of
cheap comparison of corresponding concrete representations under a shared
high-level constructor. The dependent domain is where the mismatch becomes
observable in some cases; it is not a separate root cause by itself.

**Evidence level.** Confirmed for the family-level relation. The exact
enclosing body remains unresolved in #1624 and #1563, and #1627 has only
plausible evidence (`P1627-proof1-prefix`, `P1627-proof2-prefix`).

### 5. Are any cases genuinely different after the exact pair and controls are known?

**Observation.** Yes. RealPushforward has a direct two-definition regular
head relation and a successful one-step aligned polynomial control
(`RP-REF`). #2122 has only branch-boundary checks; its final dependent branch
cannot yet be isolated (`G4-B`). OrderedSpectral requires an interaction of
three instance routes (`C1-RHD`), while IntegralComparison and RealPurity
remain expensive after their first instance leaves are aligned (`C3-I`,
`C4-B`). NativePullTensor has a measured same-body reducibility-hint effect
in addition to its major-premise effect (`NPT-same-body-hints`).

**Interpretation.** The cases fit one broad representation-and-conversion
model, but they are not one identical low-level mechanism. Necessary regular
unfolding, branch-local work, instance-route interaction, accessor major
premises, and deeper functor/object paths must remain separate labels.

**Evidence level.** Confirmed for the distinctions above; the exact
unexplained child in each negative control remains open.

## Revised root-cause model

The results retain the §1 causal chain:

```text
Actual expression pair
        |
        v
A shared head, argument, dependent domain, accessor, or branch
does not finish cheaply
        |
        v
The current representation requires reduction or unfolding
        |
        v
The exposed expression contains concrete instances, projections,
dependent propositions, proof arguments, compositions, or fields
        |
        v
The conversion becomes expensive
```

The cross-case results revise the model in four ways.

1. **Dependent proposition alignment is confirmed in three cases.** Exact
   expected-proposition controls are successful in EtaleHom (`B1-T`),
   FiniteBaseChange (`B2-T`), and F66Adj (`B3-R`). #1627 has the same stored
   proof-domain shape, but only plausible evidence (`P1627-proof1-prefix`,
   `P1627-proof2-prefix`).
2. **Accessor major-premise alignment is confirmed in three cases.** The
   type-preserving controls for #1556, #1625, and NativePullTensor are
   successful (`P1556-nat-major`, `P1625-major-align`, `NPT-major-align`).
   F66Adj strongly supports the same trigger, but its replacement changes the
   proof interface (`B3-R`). NativePullTensor separately confirms that an
   `abbrev` field-access path can remove the regular-head shortcut
   (`NPT-same-body-hints`).
3. **Same-head enclosing reduction is strongly supported in two cases.**
   #1624 and #1563 have cheap individual argument checks but expensive whole
   `Functor.comp` or nested `CategoryStruct.comp` conversions
   (`P1624-comp-args`, `P1563-comp-args`). No single type-preserving child
   control has yet isolated the whole cause.
4. **Concrete representation effects remain heterogeneous.** OrderedSpectral
   confirms a three-path instance interaction (`C1-RHD`); ImageHom confirms
   full endpoint alignment but refutes wrapper-only sufficiency (`C2-W`,
   `C2-I`); IntegralComparison and RealPurity refute first-instance/ring-leaf
   sufficiency (`C3-I`, `C4-B`); RealPushforward confirms a necessary initial
   regular-head unfolding (`RP-REF`).

These counts overlap. They count cases with a controlled result, not unique
root causes. The exact Kernel reduction sequence is not observable from these
ordinary Lean probes.

## Remaining cases and deciding experiments

The following are the smallest single controlled experiments that would
decide the currently open child for each case. They are proposals, not new
results.

| Case | Open point | Deciding experiment |
|---|---|---|
| NativePullTensor | later reduction order and possible `_proof_3` contribution | retain the exact result pair and replace the next complete `Functor.obj` endpoint as one dependent unit, then remeasure `NPT-result` |
| #1556 | inner proof detail after major-premise alignment | align the next nested `NatTrans.app` major premise in the same `congr` proposition, preserving its result type |
| #1563 | projection versus remaining nested data work | replace the complete nested `CategoryStruct.comp` argument 6 with the exact expected term and remeasure the same `Eq.mpr` domain |
| #1624 | multi-argument endpoint body below `Functor.mk` | supply the complete expected source or target `Functor.comp` endpoint as one dependent unit and remeasure the final `Iso.trans` domain |
| #1625 | inner nested major premise | descend once below the aligned `NatTrans.app` and align its next concrete major premise |
| #1627 | first nested proposition term | construct a type-preserving exact-domain transport for the generated `id` proof argument and measure the generated field value |
| #2122 | final dependent branch pair | instantiate the full telescope and transport only the final `Exists.casesOn` branch to its exact expected dependent type |
| OrderedSpectralRawLattices | third `Functor.map` let value | after the three instance paths are aligned, align only the third let value/predicate and remeasure the final conversion |
| EtaleHomComparisonReversedExact | dominant `Functor.comp` child | descend from `B1-W` and align one corresponding `Functor.comp` argument while preserving the exact quantified proposition |
| FiniteBaseChangeRestrictionMateTransport | separate site versus category-instance share | align only the site and category-instance applications in the eight dependent equality occurrences, then remeasure argument 49 |
| F66Adj | isolated `Over.left` share | preserve the direct proof interface while replacing only the `Over.left` major premise in argument 39 |
| ImageHomCounit | dominant nested endpoint | align the next nonproof nested wrapper/raw endpoint after `C2-W`, leaving the original proof term unchanged |
| IntegralComparisonPullbackRealizationShifts | child under `Functor.obj` | align the first `FullSubcategory`/`CochainComplex` object child after `C3-I` |
| RealPurity | object path under `LinearMap.charpoly` | align only the `Functor.obj`/local `P` child on both equality sides after `C4-B` |
| RealPushforward | downstream stalk/module comparison | retain the `charpolyRev` alignment and align the first remaining stalk/module child in the same final conversion |

## Consistency check

Before writing this merge, the following samples were checked against their
source records: Kernel `C1-RHD`, `B1-T`, `B2-T`, `B3-R`, `C2-I`, `C3-I`,
`C4-B`, and `RP-REF`; PerfIssues `P1624-comp-args`, `P1563-comp-args`,
`P1627-proof1-prefix`, `G4-B`, `P1625-major-align`, `P1556-nat-major`, and
`NPT-major-align`/`NPT-same-body-hints`. Timings, first differences, control
outcomes, and confidence labels match the two matrices and the case records.
No sibling-branch inconsistency was found, so no sibling file was edited.
