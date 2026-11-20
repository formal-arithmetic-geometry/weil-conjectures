# STRUCTURE EXPOSURE AUDIT

Case: `ImageHomCounit`
Source snapshot: `212f97dd22a`, `imageHomIso_counit`
Lean/Mathlib: 4.35.0, one Lean thread, normal Kernel checking, 200,000 heartbeats

## R1. Exact Kernel cost site and initial mismatch

The helper result `h := conjugateEquiv_counit ...` is cheap to construct. The
cost is the final `exact h`, converting its inferred equality to the declared
equality. Both outer propositions are `Eq` over `CategoryStruct.comp`; their
first data mismatch is raw `DerivedCategory (Sheaf ...)` versus the wrapper
`DerivedCategoryModule A X`, repeated in the morphism type and both equality
sides. Baseline `FinalExact` is 54.94 s (7.49 GB RSS); `HaveApplication` is
2.70 s.

## R2. Candidate exposure boundary

The wrapper is an abbrev whose immediate body exposes raw `DerivedCategory`.
The candidate boundary is the derived-category argument of `Quiver.Hom`, then
the nested wrapper/raw occurrences under compositions and counit maps. No
projection, let, or recursor is first on the raw path. `UnfoldWrapperHead`
and `UniformInferredHead` verify the intended expression changes.

## R3. Exposed data-bearing structure

```text
Eq of category morphisms
|- Quiver.Hom / DerivedCategoryModule versus raw DerivedCategory
|  |- Sheaf and ModuleCat structures
|  |- instCategoryDerivedCategory and HasDerivedCategory paths
|  `- generated wrapper proof fields (_proof_1, _proof_2, ...)
|- CategoryStruct.comp on both equality sides
|- functor objects, adjunction counit, and natural-transformation apps
`- concrete derived image/imageHom data
```

The raw pair and the downstream counters are direct observations; the precise
inner endpoint responsible for the remaining cost is unknown.

## R4. Cost distribution and reduction footprint

The final conversion dominates: 54.94 s and 842,612 `Add.add`, 604,585
`Functor.obj`, and 423,893 `DFunLike.coe` unfolds in the diagnostic. Expanding
only the outer wrapper is a negative control: 83.45 s and 9.87 GB RSS, with a
deeper wrapper/raw mismatch remaining. This establishes a multilevel path,
not a single outer leaf.

## R5. Causal control and §6 restoration

`UniformInferred.lean` changes the declared target to the exact inferred type
of the unchanged `h`, keeps the same final `exact h`, and is checked in 2.60 s.
The target, type, and both equality sides are syntactically aligned. The §6
restoration uses `UniformRaw`/`FinalExact`: reinstating the original raw/wrapper
target returns the 54.94 s cost. The wrapper-only edit is deliberately
recorded as a failed one-factor control.

## R6. Exposure-footprint comparison

Original: raw/wrapper derived-category endpoints expose nested category,
functor, and proof-field data; the large unfold footprint is measured.
Aligned: the original proof term is checked against its exact inferred target
and the conversion is immediate.
Restored: the original target representation and final conversion are back to
the measured expensive row. The exact dominant nested endpoint is unresolved.

## R7. Classification and confidence

Classification: **P2 (multilevel bundle-triggered exposure)**.
Confidence: **Confirmed** for full representation alignment at the same
consumer and **Strongly supported** for the multilevel wrapper mechanism;
**Plausible** for any particular inner child.
Directly measured: exact final site, wrapper-only negative control, full
alignment, restoration, and counters. Structurally inferred: the nested tree.

## Most important result

The outer wrapper mismatch is necessary but insufficient by itself. Uniform
alignment of the entire derived-category endpoint removes the cost and its
large reduction footprint, and restoration brings the cost back.
## Round 2 and v2 addendum

Fresh diagnostics give 2.62 s wall (1.71 s user, 2.83 GB peak RSS) for uniform target and 56.11 s wall (55.08 s user, 7.51 GB peak RSS) for restored raw target. One-step wrapper exposure takes 84.55 s and reports 1,263,620 Add.add, 906,156 Functor.obj, and 635,819 DFunLike.coe unfolds. This is the unresolved post-wrapper child footprint.

### STRUCTURE EXPOSURE AND AMPLIFICATION ADDENDUM

**A. MISMATCH SEMANTICS.** Raw DerivedCategory versus DerivedCategoryModule is syntactic and obstructs final equality conversion. Full uniform endpoint representation is the causal trigger; outer wrapper alone is insufficient. This is a multilevel bundle.

**B. EXPOSURE.** The boundary is the derived-category argument of Quiver.Hom under both composition sides. Visible nodes include sheaves, module-category objects, HasDerivedCategory instances, generated wrapper proof fields, functor objects, counits, and natural-transformation apps. Wrapper-only exposure is actually expensive; exact inner endpoint is unknown.

**C. COST MECHANISM.** Original/restored conversion is reduction-heavy and repeated over endpoint structure: 56.11 s. Wrapper-only is 84.55 s. Uniform alignment is 2.62 s. Counters are inclusive.

**D. FIXED-TRIGGER ABLATION.** Invalid: wrapper/raw is itself the trigger and each endpoint is dependent on the equality. Endpoint abstraction changes the theorem type. Uniform aligned/restored is the valid restoration.

**E. REDUCTION-PATH AUDIT.** The wrapper is an abbrev exposing raw DerivedCategory; outer Eq and composition heads match. One-sided exposure leaves a deeper mismatch and increases cost, while uniform alignment reaches the inferred type. No directionality claim is made.

**F. MISMATCH PROVENANCE.** conjugateEquiv_counit produces actual side; declared side uses concrete DerivedCategoryModule wrapper vocabulary. Elaboration and generated proof fields create the split, which matters at final exact h for every endpoint occurrence.

**G. CONCLUSION.** P2, evidence level 2. Reversible 56.11 s to 2.62 s full alignment is strongest. The 84.55 s wrapper-only result shows an independent inner child. Endpoint-by-endpoint typed alignment is the next falsifier.
