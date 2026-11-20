# STRUCTURE EXPOSURE AUDIT

Case: `FiniteBaseChangeRestrictionMateTransport`
Source snapshot: `0676f555de6`, `finite_base_change_restriction_mate_transport`
Lean/Mathlib: 4.35.0, one Lean thread, normal Kernel checking

## R1. Exact Kernel cost site and initial mismatch

The exact site is application argument 49 (`hb`) of the private
`transport_from_unit` helper, after 48 concrete category, functor,
equivalence, adjunction, isomorphism, and `hγ` arguments. Both propositions are
`forall M : FiniteModules A X', Eq ...`, but the actual square uses
`Scheme.ProEt` while the expected instantiated domain uses
`OpenTensorNormalization.Site .ordinary`. The same site mismatch occurs in
both equality sides. The reduced-budget application is 88.46 s and times out;
the canonical 4,000,000-heartbeat Before is 577.08 s. `NoHB` is 4.70 s,
whereas replacing `hγ` does not remove the cost (90.56 s).

## R2. Candidate exposure boundary

The shared `forall`, `Eq`, `Quiver.Hom`, and `Mod` heads reach the differing
site argument. `Site` is a regular definition whose one-step body matches on
the mode and exposes `X.ProEt` for `.ordinary`; `ProEt` is a separate regular
definition. This is a dependent application boundary. No projection or
recursor is on the first raw path; the iota step is structurally inferred.

## R3. Exposed data-bearing structure

```text
hb : forall M, equality of restriction/transport morphisms
|- FiniteModules binder and Quiver.Hom domains
|  |- Scheme.ProEt versus Site .ordinary
|  |- four concrete equivalences and ordinaryTheta.inv
|  |- restriction/base-change functors and adjunctions
|  `- additive/module/category instances
`- equality sides repeat the dependent site and composition data
```

The data tree is from the preserved instantiated binder. The conversion
diagnostic records 2,226 `Functor.obj`, 1,168 `PresheafOfModules.obj`, and
812 `ModuleCat.isAddCommGroup` unfolds in the expensive path.

## R4. Cost distribution and reduction footprint

The direct helper application alone accounts for essentially all of the
canonical 577 s. `NoHB` removes it at 4.70 s; `NoHGamma` leaves the timeout.
The cost is therefore concentrated in one dependent-domain conversion, with
repeated object/module structure below the two square sides.

## R5. Causal control

`TransportHB.lean` replaces only `hb` by
`fun M => by transport_exact h M`, preserving the consumer, preceding
arguments, theorem obligation, and normal Kernel checking. `TransportHead`
verifies the resulting proposition is the exact instantiated expected domain;
the 400,000-heartbeat application passes in 4.80 s. The full `After.lean`
checks the complete theorem. Restoring the original `hb` reproduces the
timeout. The dependency on all preceding arguments prevents a simpler
single-field source replacement.

## R6. Exposure-footprint comparison

Original: the concrete site representation is compared under equivalences,
functor objects, and module instances, producing the recorded unfold chain.
Aligned: the square is presented at the helper's exact dependent domain and
the application is cheap.
Restored: `Before.lean` restores the `ProEt`/`Site` mismatch and the original
expensive result. The exact internal reduction order is unknown.

## R7. Classification and confidence

Classification: **P1 (single dependent-argument trigger)**, with a bundled
dependent square under the argument.
Confidence: **Confirmed** for the `hb` conversion and its causal alignment;
**Strongly supported** for the larger functor/module exposure.
Directly measured: argument boundary, positive/negative controls, timings, and
unfold counts. Structurally inferred: the `Site` iota route and full field
tree. Unknown: separate site versus category-instance shares.

## Most important result

The right-square proof argument, not the mate proof `hγ`, is the first expensive
conversion. Giving it the exact instantiated dependent proposition removes the
large downstream functor/module check.
## Round 2 and v2 addendum

Fresh diagnostics give 5.13 s wall (4.42 s user, 2.31 GB peak RSS) for aligned transport and 605.06 s wall (603.32 s user, 23.91 GB peak RSS) for restored original HB domain. Both retain the same helper application.

### STRUCTURE EXPOSURE AND AMPLIFICATION ADDENDUM

**A. MISMATCH SEMANTICS.** The site representation differs inside the instantiated FiniteModules binder. It becomes a DefEq obstruction only after 48 preceding arguments fix the dependent domain. hb is the single causal trigger; hgamma is not.

**B. EXPOSURE.** The boundary is the Quiver.Hom site argument in the dependent forall. The tree contains scheme/site objects, finite-module binders, four equivalences, restriction/base-change functors, adjunctions, and additive/module instances. Functor.obj, PresheafOfModules.obj, and ModuleCat.isAddCommGroup counters connect this tree to measured work.

**C. COST MECHANISM.** One dominant dependent-domain conversion is reduction-heavy and repeated on both square sides. Original/restored is 605.06 s; aligned is 5.13 s. Child counters are inclusive.

**D. FIXED-TRIGGER ABLATION.** Invalid: the site is part of the dependent telescope, so independent abstraction changes the expected proposition. Transported whole-domain control is the valid restoration.

**E. REDUCTION-PATH AUDIT.** Site ordinary unfolds to the pro-etale site, while Scheme.ProEt is a separate regular definition. Shared forall/Eq/Quiver.Hom heads compare cheaply until this argument. The iota order is inferred.

**F. MISMATCH PROVENANCE.** The actual square uses Scheme.ProEt; the generic transport helper expects OpenTensorNormalization.Site ordinary. Preceding dependent arguments introduce the divergence at consumption. No proof abstraction is implicated.

**G. CONCLUSION.** P1, evidence level 2. Reversible 605.06 s to 5.13 s control is strongest. Site versus category-instance shares remain unresolved. A typed control aligning one square-side functor while preserving the full telescope is the next falsifier.
