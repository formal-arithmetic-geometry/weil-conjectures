# EtaleHomComparisonReversedExact: nested representation audit

Source: `8ca2e912b93`, `AlgebraicGeometry/Etale/Hom/EtaleHomComparisonModels`,
`etaleHomComparison_reversedExact_commShift_component`; Lean/Mathlib 4.35.0,
200,000 heartbeats. Measurements are reused from `WORKPLAN-EXPERIMENTS.md`;
unchanged links to the measured fixtures are in `probes/nd/`. Kernel-only
time/heartbeats and separate synthesis time are unavailable.

## Original context and A records

The expensive conversion is the concrete `hv` transpose premise at
argument 26 of `derivedTensorHomShiftComparison_component`, after 25 actual
arguments. Its source proposition is `IsEtaleHomTranspose X φ M v` and the
expected dependent binder is a quantified equality. Exposing the predicate
leaves `DerivedCategoryModule A X` versus raw `DerivedCategory (Sheaf ...)`
at the quantified domain; deeper in the equality body the same pair occurs
again. Expanding all wrappers moves the first nonproof difference to
`EtaleHomLeft` versus `Functor.comp`.
Section-10 fields shared by the rows: instance depth and field count are
the unchanged original helper structure; the instantiated equality uses
the quantified domain and both transpose sides. The selected wrapper
paths are in D. Source elaboration runs for each variant, but explicit
instance terms, synthesis time, Kernel-only time/heartbeats, and same-term
Kernel replay are unavailable. The original application diagnostic counted
hundreds of thousands of `Add.add` and `Functor.obj` unfolds downstream;
those counters do not identify a causal leaf.

| Record | Changed factor | First remaining data difference | Kernel result | Wall s | CPU user+sys s | RSS KB | Same site/obligation | Confidence |
|---|---|---|---|---:|---:|---:|---|---|
| A-EH-0 | original named predicate | predicate versus `forall` | ok, expensive | 28.92 | 27.92+1.08 | 5,495,832 | yes | confirmed site |
| A-EH-P | expose predicate only | wrapper/raw binder | ok, expensive | 28.72 | 27.75+0.94 | 5,480,764 | yes | negative single-factor |
| A-EH-D | raw quantified domain only | nested wrapper/raw equality endpoint | ok, expensive | 28.92 | 27.88+1.10 | 5,495,128 | yes | negative single-factor |
| A-EH-W | unfold all wrapper occurrences in premise | `EtaleHomLeft`/`Functor.comp` | ok, expensive | 29.12 | 28.10+1.13 | 5,525,772 | yes | negative wrapper factor |
| A-EH-T | transport `hv K` to exact expected domain | pair syntactically aligned | ok | 3.40 | 2.46+1.08 | 3,181,636 | same helper application | confirmed transport control |

All rows normally check the helper application. The diagnostic examples
end with `sorry` only afterward; `After.lean` checks the completed theorem.
The expanded binder and wrapper paths are definitionally equal to the
original proposition, and the head probes verify actual expression changes.
The transported proof changes construction and aligns the entire proposition,
so it is a whole-domain control, not proof that the wrapper leaf alone is
causal. It is the matched within-case fast control. No A/A, B/B, A/B, B/A
provider matrix or explicit-instance Kernel replay is available.

## B status

No fixed-leaf depth series was run. The quantified domain and body carry
distinct wrapper occurrences, and after their exposure the functor head
still diverges. A B test must first fix one leaf and retain the instantiated
`hv` binder and application while varying only the provider-chain depth.
The existing rows change successive representation stages, not depth.

## D: representation provenance

| Role | Supplied premise | Expected binder |
|---|---|---|
| Original declaration | local `hv : IsEtaleHomTranspose ...` | imported generic `derivedTensorHomShiftComparison_component` instantiated locally |
| Data | derived category, tensor-Hom functors, `CommShift`, `v.app` | same transpose square via generic functor parameters |
| Wrapper path | named predicate then `DerivedCategoryModule` in domain and body | expanded `forall`, raw `DerivedCategory` |
| Instance/proof path | concrete sheaf/category instances, including an auxiliary `HasSheafify` proof | generic-then-specialized category arguments |
| Construction | concrete predicate | generic helper application |

First divergence is the predicate head; after its necessary exposure, the
quantified domain is the first data divergence. The auxiliary proof
constant is a later syntactic difference and has not been shown to be a
Kernel cost source. The wrapper difference recurs in the equality body;
after removing it, a functor construction difference remains. D confidence:
strongly supported for this sequence, unresolved for the decisive inner leaf.

**Evidence level:** the full proposition alignment is locally effective,
but strict A symmetry and explicit replay are missing. Below section-12
Level 1; no Level 2/3.

## Lead-note follow-up

Fresh matched control: probes/nd/TransportHV.lean checked in 3.37 s
(2.46 s user, 1.06 s system, 3,204,732 KB RSS). The explicit helper
application
exposes the type and category slots, while remaining wrapper and instance
arguments are still inferred; it is partial A replay evidence.

The assigned B depth harness cannot vary the provider chain beneath the
quantified hv domain without replacing the consumer and its exact
instantiated proposition. No valid depth curve is reported.
