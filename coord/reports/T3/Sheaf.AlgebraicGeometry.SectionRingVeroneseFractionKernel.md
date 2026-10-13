## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.Modules.sectionRingVeroneseFractionMap_kernel`
with the generic direct-sum kernel calculation, the localization zero criterion, and the
Veronese numerator transition identity. The existing theorem signature, definitions,
visibility, and public imports are unchanged. Added the proof-only import
`Sheaf.AlgebraicGeometry.SectionRingVeroneseNumeratorTransition` and its new module.
No interface change or forced adaptation is made; no change record is needed.

Return repair: removed the duplicate private theorem `span_additive` entirely.
The forward inclusion now uses `Submodule.span_induction` with predicate
`∀ r, f (r • z) = 0`, then specializes to scalar one. This proves only the
needed inclusion and does not restate or reprove the existing span/closure theorem.
Both delivered modules compile without warnings through `lcompile.py --all`.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.Modules.sectionRingVeroneseFractionMap_kernel`
(node `lem-sc-section-ring-veronese-fraction-kernel`). Its proof body is complete.
Hole added and left: `AlgebraicGeometry.Scheme.Modules.sectionRingVeroneseNumerator_transition`
(node `lem-sc-section-ring-veronese-numerator-transition`). There are no other delivered holes.
This is a decomposition: one upper hole closed, one strictly simpler tensor-coherence hole
added, hence net zero holes closed before any import-closure pruning. The kernel theorem
is not yet an axiom-clean theorem: both declarations' axiom checks return exactly
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.

## No longer needed

Every old proof dependency remains used: `def-sc-section-fraction-presentation` and
`def-sc-section-ring-veronese-fraction-map`. No old dependency node or library module is
pruned. Removed the first worker's redundant proof imports
`Mathlib.GroupTheory.QuotientGroup.Basic` and `Mathlib.RingTheory.Localization.Basic`.
In the new transition module, replaced `public import
Sheaf.AlgebraicGeometry.SectionFractionPresentation` with `public import
WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators`: its statement uses
`mulTensorPowSection`, not the fraction-relation submodule or quotient presentation.
No separate scalar compatibility lemma or finite-support maximum argument is required.
The duplicate helper `span_additive` is removed. No import of
`Sheaf.AlgebraicGeometry.AffineOpenSectionFractionLocalization` is needed: its
`span_toAddSubgroup_eq_closure` is private and unavailable to importers. The new
forward-inclusion proof does not use the additive-closure comparison at all.

## Where the brief, the DAG or earlier work was wrong

The first worker reported a missing local compiled `SectionRingVeroneseFractionMap` dependency
and compiled its unchanged source into the sandbox cache. Both delivered modules now compile
against the available local library and sandbox artifacts. No dependency source is delivered.
The earlier report called the kernel theorem proved without identifying the zero-net
one-for-one decomposition. The old change record was unnecessary and incorrectly said imports
were unchanged; it has been removed. There is no definition or statement repair.
The returned delivery correctly identified the private span/closure helper as a duplicate.
An import probe confirms the existing private theorem is not exposed; direct span induction
removes the duplicated result without changing that other module or any existing signature.

## New nodes

`lem-sc-section-ring-veronese-numerator-transition` states the tensor-power coherence
identity needed for both directions of the kernel proof. It compares explicitly constructed
numerators, without mentioning localization kernels or choosing arbitrary witnesses.
It has a complete local-generator and sheaf-separatedness proof in its docstring and node,
source, statement dependencies, proof dependencies, search records, creation information,
blueprint provenance, chapter, unit, and exact Lean signature. There are no change records.

## Earlier second reading (a previous round; superseded)

1. PASS: compared the delivered kernel module with the repository using diff and checked its
existing theorem signature byte for byte. Only its proof, private helpers, and proof-only imports changed. No existing data, hypothesis, conclusion,
visibility, or target statement changed. The transition module is new.

2. PASS with the explicitly reported remaining hole: compiled both modules in import order
through lcompile.py after import cleanup (about 2 and 6 seconds). Read every helper and both
kernel inclusions. The relation-generating set is closed under scalars by transition linearity;
direct-sum induction uses common degree n+m; the reverse inclusion uses the localization zero
criterion and injectivity of the explicit numerator map. No axiom, unsafe, opaque,
implemented_by, extern, or sorry in data occurs. A scratch copy with #print axioms on both
public theorems returned only the three permitted axioms and sorryAx. The scratch source was
removed before delivery. The only literal sorry is the named, documented transition theorem.

3. PASS: the split-off identity is a strict part of the argument, not a restatement of the
kernel theorem. Checked the definitions of tensorPowMulIso, tensorPowAddIso,
mulTensorPowSection, and graded multiplication. Their recursive unitors and associators
preserve local tensor generators, so both expressions have coefficient f*c^b. Edge cases
n=0, b=0, d=0, zero or nilpotent s, the zero numerator, and the empty scheme require no division
or cancellation of s. The local proof glues without quasi-compactness; the kernel proof is
purely algebraic. Checked the cited source context online at Stacks
[0B5L](https://stacks.math.columbia.edu/tag/0B5L),
[01PW](https://stacks.math.columbia.edu/tag/01PW), and
[01Q1](https://stacks.math.columbia.edu/tag/01Q1); the quasi-compactness assumptions for restriction
to a principal open are not assumptions of this internal kernel calculation.
Independent msearch queries used leanfinder for iterated tensor powers and multiplication,
loogle for span and additive closure, and grep for the tensor operations. The search results
concern algebraic tensor powers and integer spans, not this scheme-module identity.
Repository searches also inspected SectionRingCoefficientNumerator and
SectionRingLocalizationBijective: their private power identities only address powers of s,
not arbitrary numerators and transitions. No directly reusable proof closes the remaining
coherence identity in a few minutes; retained the sourced, simpler hole.

4. PASS: the proof takes elementary additive and localization routes before using its one
open tensor-coherence lemma. Removed redundant proof imports and narrowed the new module's
public dependency. All old proof_deps are used and accounted for above. The kernel node lies
below the unit level. Read dag/units/sk-thm-curveestimate.json: realized.statement remains
thm-sc-proper-cohomology and realized.steps is empty. No unit statement, step, route, or
realized field is changed or bypassed.

5. PASS: both node Lean statements exactly match their files. The kernel node's proof describes
scalar stability and direct-sum induction as actually implemented, and proof_deps includes
the two retained definition nodes and the new transition node. The new node's dependencies,
source, proof_origin, and provenance agree with its Lean statement and docstring.

Second reading changed: removed two redundant proof imports; narrowed the new module's
public import to ClearDenominators; removed the unnecessary, inaccurate change record;
corrected this report to identify the decomposition and axiom status. The first dry run classified the added universe and section-variable commands as an
interface change. Moved those parameters into the private helper signatures and restored
the existing universe command, preserving all proof bodies and avoiding that interface change.


## Second reading by T3

1. PASS. Independently diffed the kernel module against the read-only repository and
   checked its existing theorem signature byte for byte. Only private helpers, the
   proof body, and a plain proof import were added. No existing definition, public
   import, visibility, target, hypothesis, or conclusion changed. The transition
   module is new; no interface change record or forced adaptation is required.
2. PASS with the declared hole. Both modules compile cleanly in import order through
   lcompile.py (2.5 and 6.8 seconds). Read rel_normal, kernel_rel, both localization
   helpers, and the specialization: common degree n+m suffices without transition
   composition, span induction treats all scalar multiples, and numerator injectivity
   follows from the inverse isomorphism and graded injection. The sole literal sorry
   is sectionRingVeroneseNumerator_transition, a named documented theorem. A scratch
   copy printing axioms for both public theorems reports exactly propext,
   Classical.choice, Quot.sound, sorryAx; removed that copy. No forbidden declaration
   or hollow data occurs. This remains one closed upper hole plus one added lower
   hole, a net-zero decomposition rather than an axiom-clean proof.
3. PASS. Read the recursive tensorPowAddIso and tensorPowMulIso definitions,
   mulTensorPowSection_app, and the section-ring multiplication. On an open where L
   has generator e, their maps preserve the iterated generator; transition and ring
   multiplication both give coefficient f*c^b. Restrictions and separatedness prove
   the stated equality. Cases n=0, b=0, d=0, zero t, zero/nilpotent s, and empty X
   need no cancellation or division. The lemma concerns only numerator coherence,
   not the kernel conclusion. Read Stacks 0B5L, 01PW, and 01Q1 online: compactness
   there concerns comparison with sections on X_s, not this internal identity.
   Independent msearch queries: leanfinder, "Compatibility of iterated tensor power
   isomorphisms with product of arbitrary sections"; loogle,
   "Localization.mk_eq_mk_iff"; grep, "tensorPow.*(tmul|mul)|mulTensorPowSection_app".
   The results are algebraic TensorPower identities and the localization criterion,
   not this scheme-module coherence statement. Also searched both Lean roots and
   the upstream Modules sources. ClearDenominators handles powers of the same s;
   private ring_power_of in SectionRingCoefficientNumerator handles s^n, not
   arbitrary t. No existing result closes the remaining identity directly in a few
   minutes; retained its full sourced local-generator proof and matching new node.
4. PASS. Elementary direct-sum/span arguments and Mathlib localization criteria
   precede the one open geometric coherence identity. Imports serve the statements
   or the proof; the new lemma's ClearDenominators import is needed for its signature.
   Every old proof_deps node is still used; the No longer needed section is complete.
   Read sk-thm-curveestimate.json: its realized statement is thm-sc-proper-cohomology
   and its realized steps are empty. This reduction changes no unit route.
5. PASS. Parsed and compared the existing node: only proof and proof_deps differ.
   Both lean.statement fields occur verbatim in their modules. The kernel steps
   describe exactly the scalar-stable span induction, common-degree reduction,
   localization annihilator, and injective numerator argument. The new node contains
   its source, dependency union, proof_origin, searches, creation and blueprint
   provenance, chapter, unit, and complete Lean record matching its docstring.

Second reading changed: appended this independent review; no Lean or DAG repair was
needed. The earlier returned duplicate helper is absent and its replacement uses
Submodule.span_induction directly.
