# Nested-data experiment report

Snapshot: Lean 4.35.0, master revision 1ef1fddac73e. All case records
reuse the completed baselines in their existing README, CLASSIFICATION,
HEAD-AUDIT, and WORKPLAN-EXPERIMENTS files. Kernel replays use the copied
probes under each case's probes/nd directory. Source elaboration and
instance synthesis are reported separately from explicit Kernel replay;
local instance priorities are never treated as rewriting imported terms.

## Outcome table

| Case | A representation symmetry | B nesting | C repeated fields | D provenance | Evidence level |
|---|---|---|---|---|---|
| NativePullTensor | 11,396 ms to 0 ms by major-premise alignment; regular/regular 0 ms versus abbrev/abbrev 11,251 ms | not run: a synthetic chain loses the Exists/Iso consumer | not run: no valid repeated-field consumer | concrete Functor.uncurry premise under Functor.obj abbrev | Level 1, A confirmed |
| PR1556 | congr proposition 50,090 ms to 0 ms; reverse 50,585 ms | not assigned in Batch 1 | not assigned in Batch 1 | old whiskered Iso/NatTrans component | Level 1, A confirmed |
| PR1625 | NatTrans.app 95,869 ms to 0 ms; reverse 93,567 ms | nested app remains 95,717 ms, but no independent depth ladder | no valid field-count matrix | concrete NatTrans major premise under abbrev accessor | Level 1, A confirmed; B inconclusive |
| PR1624 | no type-preserving one-factor alignment; endpoint checks 14,706/28,640 ms | concrete Iso/Functor.comp nesting localized, no ladder | four dependent endpoint mismatches, no fanout matrix | concrete derived-functor compositions under whiskering | below Level 2; localization only |
| PR1563 | no valid single-factor alignment | outer comp 31,026 ms; nested comp 21,537 ms | seven arguments distribute work; no field-count matrix | raw pullback/composition and CategoryStruct.comp projection | below Level 2; partial B/C |
| PR1627 | raw/generic matrix invalid without changing generated proofs | dependent id domains 7,508/33,863 ms, no depth ladder | three generated checks 27.8/55.3/14.6 s | concrete Functor.mk law generation | Level 1 for C; A/B inconclusive |
| PR2122 | not isolated after branch step | branch motive/witness 16,115/18,419 ms; no depth ladder | dependent final branch cannot be checked alone | concrete category/functor witnesses under Exists.casesOn | inconclusive |

## Common experiment records

### A-NPT

Original consumer: Iso endpoint, Functor.comp, Functor.obj, and two
Exists.choose domains. Variants: original A/B, A/A major-premise alignment,
reverse, and regular/abbrev same-body controls. Inference is the original
module elaboration; replay is explicit Kernel.isDefEq on stored terms. The
same endpoint conversion changes from 11,396 ms to 0 ms. The theorem type is
structurally preserved. Supports representation asymmetry and an abbrev
projection path; B/C remain unresolved.

### A-1556

Original consumer: generated congr proposition under Exists.intro and
CategoryStruct.comp. Variants: old whiskered component, major-premise
alignment, reverse. Source inference is the before prefix; replay is the
explicit proposition-domain probe. 50,090 ms becomes 0 ms with a preserved
proposition type. Supports representation asymmetry in a dependent proof
domain; no depth or fanout factor was assigned.

### A-1625

Original consumer: Eq, CategoryStruct.comp, nested NatTrans.app, and the
final inferred/declared type conversion. Variants: original, outer-major
alignment, reverse. Source inference is the before prefix; replay is the
explicit NatTrans probe. 95,869 ms becomes 0 ms with a structurally equal
checked result type. Supports representation asymmetry. The inner nested
app remains expensive, so depth amplification is not isolated.

### B/C-1624

Original consumer: Iso.trans and isoWhiskerLeft over concrete Functor.comp
endpoints. The source/target endpoint conversions are 14,706/28,640 ms;
arguments 2,3,6,7 are independently unequal in 0--8 ms, and all
single-factor replacements are rejected as ill-typed. This is a negative
symmetry and fanout control: the complete dependent endpoints, not isolated
arguments, are the measured site.

### B/C-1563

Original consumer: Eq.mpr's fourth dependent domain and nested
CategoryStruct.comp. The outer pair is 31,026 ms and nested argument 6 is
21,537 ms. Type-preserving nested replacements still cost 11,325--20,810
ms. This supports local nested/repeated work but does not vary a separate
depth or field-count parameter.

### C-1627

Original consumer: concrete Functor.mk generated law fields and their
dependent id proof domains. The three in-situ checks are 27.8, 55.3, and
14.6 s; replayed _proof_1/_proof_2 values are 20.341/33.929 s, with final
type conversions 0 ms. The id argument-1 domain conversions are 7,508 and
33,863 ms. All generated fields are used. Supports repeated generated-field
work, but non-monotone field costs prevent a field-count causal claim.

### B/C-2122

Original consumer: 14 binders, 12 lets, Exists.casesOn, and a dependent
branch. The motive and witness branches check in 16,115 and 18,419 ms; the
final branch cannot be checked independently because the recursor supplies
its type. No A/B, depth, or field-count substitution is valid at this
stage. The result is a validity boundary, not a performance result.

### D-all

Each case records the left/right declaration origin, data-bearing structure,
instance or construction route, wrapper/accessor, let/proof-abstraction
boundary, first observed divergence, and whether the fast control changes
the producer. The recurring producers are concrete functor/NatTrans
major-premise construction, concrete CategoryStruct.comp/Functor.comp
composition, and generated Functor.mk law fields. #2122 remains source-guided
at the inner leaf because its dependent branch cannot be replayed alone.

## Matched fast controls

| Slow case | Control | What is held in common | Caveat |
|---|---|---|---|
| NativePullTensor | nativePullTensor and A/A alignment | Iso/functor vocabulary and endpoint consumer | final declaration is only a nearby control |
| PR1556 | preceding theorem and fixed closing proof | imports and dependent categories | fixed proof changes construction route |
| PR1625 | earlier declaration and fixed whole-NatTrans proof | derived tensor context | fixed proof is an API control |
| PR1624 | two earlier checks and abstract helper | category hierarchy and imports | helper changes representation boundary |
| PR1563 | shared raw-pullback helper | module imports and category context | helper is still costly but much smaller |
| PR1627 | IsoAlgebra.liftOfStr after form | functor result type and coefficient context | generic construction removes generated fields |
| PR2122 | current split module | theorem result and mathematical construction | imports/helpers are split, so not a single-proof control |

## Observations

1. Three cases have type-preserving major-premise controls that reduce the
   same Kernel conversion to zero: NativePullTensor, PR1556, and PR1625.
2. PR1624 and PR1563 show shared outer heads with several dependent
   arguments that are cheap alone but expensive as complete endpoint or
   composition expressions.
3. PR1627 has three used generated law fields with different costs; two
   share the same dependent id-domain shape.
4. PR2122's branch-local checks are measurable, but its final dependent
   branch is not an independently checkable term.
5. In every valid replay, source instance synthesis is not the timed Kernel
   operation; explicit stored terms are checked in the original consumer.

## Interpretations

The strongest recurring mechanism is representation asymmetry at an
accessor major premise: an abbrev projection or concrete composition must
reconcile two separately constructed but definitionally equal data-bearing
objects. Generated proof fields add repeated dependent proposition checks,
as in PR1627. Nested consumers and repeated arguments distribute the work,
but the available controls do not establish a general monotone depth or
fanout law. The data therefore reaches Level 1 for three direct alignment
cases and for PR1627's repeated generated fields, with only partial
amplification evidence in PR1563 and no causal attribution for PR2122.

The records do not support the stronger project-level claim that instance
depth alone is the dominant mechanism. The valid evidence instead points to
concrete representation producers at stable interface boundaries, with
nesting and generated-field reuse as case-dependent amplifiers.
