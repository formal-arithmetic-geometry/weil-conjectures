# STRUCTURE EXPOSURE AUDIT

Case: `F66Adj`
Source snapshot: `f66ad18a9ed`, `imageHomIso_naturality`
Lean/Mathlib: 4.35.0, one Lean thread, normal Kernel checking, 400,000 heartbeats

## R1. Exact Kernel cost site and initial mismatch

The hotspot is argument 39 (`hR`) of `homIso_naturality_of_counit`. The
actual proof proposition contains
`imageRestriction_counit A _ _ (Over.mk f.left)`; the expected proposition has
the direct restriction square at the local scheme `X`. Under matching `Eq`,
`Quiver.Hom`, and `CategoryStruct.comp` heads, the first material leaf is
`Over.left (Over.mk f.left)` versus `X`. This dependent proposition is checked
after 38 cheap arguments. Prefix 39 costs 35.22 s; `ReplaceHR` costs 3.70 s;
the full Before is 116.48 s and After 3.40 s.

## R2. Candidate exposure boundary

The boundary is the instantiated proposition type of argument 39, beneath
`DerivedCategoryModule` and `Quiver.Hom`. `Over.left` is an abbrev whose body
exposes `Comma.left`; the counterpart is a free scheme variable. The first
path is ordinary application (`Expr.app`), not `Expr.proj`; later field
reduction is only a structural possibility.

## R3. Exposed data-bearing structure

```text
hR : restriction-counit equality
|- Over.mk f.left / Over.left versus local scheme X
|- DerivedCategoryModule and scheme/category instances
|- seven-argument CategoryStruct.comp on each equality side
|- image/restriction functors and NatTrans.app
`- coefficient variance and concrete global-Hom paths
```

The prefix jump at argument 39 and the prior `Functor.obj`/additive diagnostics
connect the proposition to the measured work; the exact child order is
unknown.

## R4. Cost distribution and reduction footprint

Arguments through 38 remain 3.1--3.4 s. Supplying the original `hR` raises the
application to 35.22 s; changing the preceding tensor-isomorphism argument
does not help (35.12 s). `ReplaceHR` is 3.70 s. The full declaration's later
handoff adds another large component. This is one dominant dependent argument,
not seven independent equal costs.

## R5. Causal control

`ReplaceHR.lean` supplies `restriction_counit A f.left _ _` only at argument
39. `ReplaceHRHead` confirms that the elaborated proposition changes at the
intended `Over.left` path and the same helper application is checked. The
direct restriction interface is a type-preserving control for the application;
the original proof is restored by `Before.lean` and returns the jump.

## R6. Exposure-footprint comparison

Original: concrete `Over`/scheme representation is compared beneath dependent
derived-category and functor data; the 35 s prefix and downstream unfold counts
are measured.
Aligned: the scheme parameter is supplied through the direct restriction
interface; a different monoidal-instance leaf remains, yet the application is
3.70 s.
Restored: the original `imageRestriction_counit` proposition brings back the
35.22 s application cost. The full After is a broader interface fix.

## R7. Classification and confidence

Classification: **P1 (single dependent-argument trigger)**.
Confidence: **Confirmed** for the argument-39 representation trigger;
**Strongly supported** for the exposed category/functor structure.
Directly measured: prefix boundary, exact first leaf, positive/negative
controls, timings, and changed pair. Structurally inferred: `Comma.left` and
the nested field tree. Unknown: isolated `Over.left` share after the proof
interface is held completely fixed.

## Most important result

The expensive conversion begins exactly when the `Over.left`-bearing proof
proposition is supplied. A direct restriction proof makes that same application
cheap even though other concrete instance differences remain.
## Round 2 and v2 addendum

Fresh diagnostics give 3.73 s wall (2.82 s user, 2.87 GB peak RSS) for aligned restriction and 119.54 s wall (118.21 s user, 12.68 GB peak RSS) for restored original HR. Argument 39 and the theorem consumer are unchanged.

### STRUCTURE EXPOSURE AND AMPLIFICATION ADDENDUM

**A. MISMATCH SEMANTICS.** The first material difference is Over.left (Over.mk f.left) versus local X. It is syntactic and dependent; direct restriction is a causal control. This is one argument trigger, not seven equal costs.

**B. EXPOSURE.** The boundary is the instantiated proposition for hR. Visible nodes include Over/Comma data, derived-category module objects, seven-fold composition, image/restriction functors, and NatTrans applications. Prefix timing and downstream functor/additive counters make the proposition actually expensive; individual composition fields remain inferred.

**C. COST MECHANISM.** Argument 39 is a reduction-heavy dominant inclusive cost. Original/restored is 119.54 s; aligned is 3.73 s. Later full handoff is separate.

**D. FIXED-TRIGGER ABLATION.** Invalid: Over.left is the trigger inside the dependent proof type, so independent abstraction changes argument 39. Direct restriction and restored original are the valid controls.

**E. REDUCTION-PATH AUDIT.** Over.left is an abbrev exposing Comma.left; counterpart is local X. Outer equality and composition heads match until this ordinary application. Direct restriction changes the major premise; internal order is inferred.

**F. MISMATCH PROVENANCE.** imageRestriction_counit applied to Over.mk f.left produces the actual proof; direct restriction produces the expected one at X. Dependent instantiation at argument 39 makes the split relevant. Wrapper, zeta, and simp are not the source.

**G. CONCLUSION.** P1, evidence level 2. Reversible 119.54 s to 3.73 s control is strongest. Remaining monoidal leaf prevents full attribution. A typed seven-fold-composition ablation preserving Over is the next falsifier.
