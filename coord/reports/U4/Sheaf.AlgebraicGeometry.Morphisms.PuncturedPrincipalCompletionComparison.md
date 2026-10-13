## What changed

Replaced the sole hole in
`Sheaf.AlgebraicGeometry.Morphisms.PuncturedPrincipalCompletionComparison`
with a complete Lean assembly from two strictly smaller finite-stage inputs.
The statement and all three existing public imports are unchanged. Added private
scalar-restriction helpers proving compatibility with transitions and the exact
GammaSpecIso/pullback formula, and two nonpublic proof imports:
`Sheaf.AlgebraicGeometry.Morphisms.PuncturedPrincipalFiniteLevelLift` and
`Sheaf.AlgebraicGeometry.Morphisms.PuncturedPrincipalRestrictionKernel`.

The proof chooses scalar representatives of individual formal sections, moves them
to kernel-bound indices, and proves their quotient coherence by comparing two
representatives with a common later lift. Mathlib then constructs the completion
element from this Cauchy sequence. A separate kernel argument proves uniqueness.
The parent node now records precisely this assembly. Both new modules have real
statements, source citations and full natural-language proofs, with matching nodes.
No new data definition uses an unproved existence theorem; choices occur only
inside the theorem proof.

## Proved and sorry left

Closed `AlgebraicGeometry.Scheme.punctured_principal_completion_comparison`
(node `lem-sbc-punctured-principal-completion-comparison`): its entire proof now
compiles with no direct sorry. The original module has zero remaining holes.

Added two holes, each the whole proof of a public theorem in its own module:

- `AlgebraicGeometry.Scheme.punctured_principal_finite_level_lift`
  (node `lem-sbc-punctured-principal-finite-level-lift`): each section of a
  compatible family lifts to an individual scalar; it asserts neither compatible
  scalar lifts nor existence or uniqueness of a completion element.
- `AlgebraicGeometry.Scheme.punctured_principal_restriction_kernel`
  (node `lem-sbc-punctured-principal-restriction-kernel`): for each prescribed
  quotient level, restriction kernels at some deeper finite level die in that
  quotient; it asserts no lifting of any section family.

This is a decomposition: one upper hole closed and two strictly smaller lower
holes added, not an axiom-free proof or a net reduction in the hole count.
Single-file compiler checks succeeded on the complete assembly and both new
statements. Edge cases checked mathematically before stating the inputs: g=0,
nilpotent g, and zero divisors are included; no finite-level injectivity,
regularity of g or completeness of R is assumed. The index-zero completion
quotient is handled explicitly as a subsingleton in the Lean uniqueness proof.

## No longer needed

No existing imports or modules are pruned. The old direct proof dependencies
`def-weil-pbc-depth`, `def-weil-pbc-noetherian-ring`, and
`lem-sbc-depth-two-puncture-global-sections` are no longer used directly by the
parent proof. They remain needed by the new finite-stage nodes (and depth and
Noetherianity remain hypotheses of the unchanged parent statement). The original public imports
supply the statement's thickening definitions, depth and completion and remain.
The parent no longer applies `depth_two_puncture_globalSections_bijective`
directly: its use is retained inside the two new nodes' proof plans, so
`lem-sbc-depth-two-puncture-global-sections` and its module are still needed.
The finite-etale section-transfer theorem itself is not invoked; its module
remains necessary for the definitions used in the unchanged statement.
No claim of global reachability pruning is made.

## Where the brief, the DAG or earlier work was wrong

The original step 2 names only definitions, not a theorem giving the principal
formal comparison. In particular, neither the local-cohomology vanishing nor
Tag 0BLD's comparison has a directly applicable declaration among the named
proof dependencies. The finite-level consequences of the pro-isomorphism in
Tag 0H3E isolate this gap without restating the completion theorem.
The source pages for Tags 0BLD, 0H3E, 0BK0 and 0AVY were read online because the
local repository contains citation inventories but no Stacks text checkout.
LeanSearch returned Internal Server Error; LeanFinder, Loogle, Mathlib/project
source searches and whole-blueprint searches supplied the remaining searches.
The power-series punctured-thickening results have stronger, different hypotheses
and cannot specialize to an arbitrary principal zero divisor. The complete-ring
comparison imports this item and would introduce a cycle.
No existing signature or definition was corrected; no adaptations are required.
The unit and chapter routes are retained.

## New nodes

`lem-sbc-punctured-principal-finite-level-lift`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-punctured-principal-finite-level-lift.json`,
states finite scalar lifting for each member of a compatible formal section family.
Its proof uses the pro-zero cokernel of the two-term-cone comparison from 0H3E,
after canonical depth-two Hartogs and H1 vanishing from depth three. Its module is
`Sheaf.AlgebraicGeometry.Morphisms.PuncturedPrincipalFiniteLevelLift`.

`lem-sbc-punctured-principal-restriction-kernel`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-punctured-principal-restriction-kernel.json`,
states eventual vanishing of finite scalar restriction kernels. The other side of
the same pro-isomorphism gives this input independently of finite scalar lifting.
Its module is `Sheaf.AlgebraicGeometry.Morphisms.PuncturedPrincipalRestrictionKernel`.
Both new nodes carry three kinds of Mathlib searches, with service unavailability
recorded honestly, and inherit the parent's chapter, unit and blueprint ancestry.
There are no change records because all existing interfaces are unchanged.


## Second reading by U4

1. **Interfaces: PASS.** Read the diff of every delivered module against the
repository. The only previously existing module is the parent comparison module;
its theorem signature and docstring are byte-for-byte unchanged, as are its three
public imports. The two new imports are proof-only. The helper abbreviation is
private and is a concrete composite of existing ring homomorphisms. No existing
definition, statement or public visibility changed; no change record is needed.
No open change record naming this interface was found.

2. **Proof and axioms: PASS as a decomposition.** Independently compiled all three
files in dependency order with lcompile.py (2.2 s, 2.3 s, 4.1 s). A scratch copy
with explicit #print axioms commands confirmed that the parent and both new
statements use only propext, Classical.choice, Quot.sound and sorryAx. Read the
entire assembly, including the scalar-transition and quotient-naturality helpers,
the common-later-index comparison (which does not assume monotone kernel bounds),
the Cauchy construction, and uniqueness at positive and zero indices. The only
direct holes are the two named, public new theorems, each with a complete source
proof and its node. No forbidden declarations or hollow data definitions occur.
The scalar and index choices from unproved existence assertions are confined to
the proof of a proposition, not the construction of a public data definition.

3. **Split statements: PASS.** Independently read the source arguments at
[Stacks 0H3E](https://stacks.math.columbia.edu/tag/0H3E),
[0BLD](https://stacks.math.columbia.edu/tag/0BLD),
[0BK0](https://stacks.math.columbia.edu/tag/0BK0), and
[0AVY](https://stacks.math.columbia.edu/tag/0AVY).
The map of two-term complexes to ordinary sheaf quotients has error cone
F[g^j][2]. Stabilization makes its sufficiently long transitions zero, hence
its derived sections have pro-zero errors. H1(W,F)=0 identifies degree-zero
cone sections with R/g^j. The resulting pro-zero cokernels give finite lifting
of compatible families; the pro-zero kernels give the uniform scalar difference
bound. These are separate proper parts of the argument, neither restates
existence and uniqueness in the completion. Checked g=0, nilpotent g, ordinary
nonzerodivisors, and zero divisors without assuming finite-stage injectivity.
For example R=k[[x,y,z,e]]/(e^2) has depth three: g=e is eventually constant,
while g=x is a nonzerodivisor. At n=0 the kernel claim concerns I, whereas the
completion's own zero-index quotient is zero; these indices are not confused.
Fresh LeanFinder search for Hartogs modulo powers/eventual injectivity and
Loogle query `AdicCompletion, Function.Injective` found only local germ and
completion injectivity facts, not either new assertion. Read project candidates
for power-series thickenings, TorStrictlyProZero and TensorTowerKernelProZero;
they concern different hypotheses or algebraic tensor kernels. No available
lemma closes either new hole in a short proof.

4. **Route and pruning: PASS with report repair.** Mathlib supplies the elementary
completion assembly; the remaining source comparison is isolated in the two
finite-stage statements. All imports serve signatures or the written proof.
The depth-two Hartogs input remains in the lower proof plans. Read
`dag/units/sk-prop-input-spreading.json`, including its recorded statement and
step texts: no unit statement or step is bypassed or altered. The separate
blueprint source path is absent from this machine; the review used the unit
record rather than claiming to read an unavailable file. Its realized arrays are already empty in the
repository; this delivery does not change them or claim to fill them. Corrected
No longer needed to enumerate all three old direct proof dependencies absent
from the parent's new proof_deps; none is claimed globally pruned.

5. **Nodes: PASS.** Checked the parent steps against the Lean scalar comparison,
choice, coherence, construction and uniqueness argument. proof_deps is exactly
the union of the step uses. The two new records match their Lean signatures,
source proofs, chapter/unit, ancestry, creation metadata, search records and
status. Existing statement/stmt_deps fields are unchanged. No target meaning
changes and no statement change record or consumer adaptation is needed.

**Changes by this reading:** completed the direct-dependency pruning account and
added this independent review. No Lean proof or signature needed repair. One
original hole is closed by assembly; two lower holes remain newly split off.
