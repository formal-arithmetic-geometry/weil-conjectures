## What changed

Constructed `Scheme.strictHenselizationPointCocone` explicitly from the geometric
points and `Scheme.strictHenselizationPointEvaluation` by `colimit.desc` in
`Sheaf.Paper.StrictHenselizationPointEvaluation`. No arbitrary data is selected
from an unproved existence theorem.

Proved `Scheme.strictHenselizationPointEvaluation_pointed` in its own module
`Sheaf.Paper.StrictHenselizationPointEvaluationPointed` by the colimit coprojection
equation and the Γ/Spec triangle. Proved
`Scheme.strictHenselizationPointEvaluation_mem` in its own module
`Sheaf.Paper.StrictHenselizationPointEvaluationImage`, directly from filtered-colimit
representatives, separability of étale residue extensions, and compatibility of the
base residue embeddings. Its two proof imports are plain imports.

Defined `Scheme.strictHenselizationPointEvaluationToSep` by codomain restriction
using the proved image-containment theorem in
`Sheaf.Paper.StrictHenselizationPointEvaluationProperties`. Isolated only its
surjectivity as a named theorem in that module. The proof-dependency imports for
its documented triple-colimit argument are plain imports. The target proof uses
this surjectivity, Mathlib `IsLocalRing.ker_eq_maximalIdeal`, and the proved
pointedness equation. All existing declaration signatures, visibility and docstrings
are unchanged. `AlgebraicGeometry.strictHenselizationPointedMap_core` is unchanged.

Corrected the main and core nodes' stale proof plans and dependencies to match
the actual Lean, and added the missing canonical-evaluation definition node.

## Proved and sorry left

Original hole closed:
`AlgebraicGeometry.strictHenselizationPointedMap`
(`lem-weil-pbc-strict-henselization-pointed-map`).

New proved theorem declarations:
`AlgebraicGeometry.Scheme.strictHenselizationPointEvaluation_pointed`
(`lem-weil-pbc-strict-henselization-point-evaluation-pointed`) and
`AlgebraicGeometry.Scheme.strictHenselizationPointEvaluation_mem`
(`lem-weil-pbc-strict-henselization-point-evaluation-image`).
The cocone, evaluation and codomain restriction are concrete definitions.

Only new hole:
`AlgebraicGeometry.Scheme.strictHenselizationPointEvaluationToSep_surjective`
(`lem-weil-pbc-strict-henselization-point-evaluation-properties`), with its complete
natural-language proof and source in its docstring. There are no other sorries in
the delivered files. Surjectivity needs no local-ring assumption; the kernel
assertion is proved in the target using Mathlib, rather than left inside this hole.

This is a decomposition: one original hole closed, one strictly smaller hole added,
net zero holes closed relative to the repository baseline. The second reader closed
the first worker's proposed image-containment hole and removed its unnecessary
kernel obligation. The core theorem was already proved in the repository and is
not counted as a newly closed hole. No claim of axiom-free completion of the target
or of its import closure is made.

## No longer needed

No existing import was removed and no module is claimed as pruned. The target no
longer uses its old node dependencies
`lem-weil-pbc-strict-henselization-pointed-map-factorization` and
`strict-henselization-pointed-map-properties`; both are removed from its proof_deps.
These are replaced by the concrete construction and its genuinely separate image,
pointedness and surjectivity assertions. The core node's old dependency on
`lem-weil-pbc-strict-henselization-pointed-map` is also removed: its existing Lean
proof independently constructs an abstract surjection using the triple theorem.
The two existing triple imports stay because this unchanged core proof uses them.

## Where the brief, the DAG or earlier work was wrong

The main node described an obsolete factorization/properties route, whereas the
repository file still had a sorry. The core node described projection from the main
theorem, whereas its actual Lean proof independently transported a triple-colimit
surjection; that stale description created a misleading dependency.

The first report incorrectly counted the already-proved core as a newly closed
hole and omitted unused old DAG dependencies. Its search records contained queries
not supported by the sandbox search log, and its new statements were grouped in
modules instead of having their own modules. The second reader corrected these.
The first worker left image containment open despite available Mathlib components;
the second reader proved it. The new surjectivity/kernel hole also contained an
immediate Mathlib consequence, now proved directly in the target.

## New nodes

`def-weil-pbc-strict-henselization-point-evaluation` records the real compatible
cocone and its canonical colimit map. It is a construction from the pointed
transition equations and the colimit universal property.

`lem-weil-pbc-strict-henselization-point-evaluation-image` records the proved image
containment theorem. Its proof uses filtered representatives and the étale
residue-field separability Mathlib leaf, not the still-open triple comparison.

`lem-weil-pbc-strict-henselization-point-evaluation-pointed` records the proved
coprojection pointedness equation, independently of image containment and
surjectivity.

`lem-weil-pbc-strict-henselization-point-evaluation-properties` records only the
surjectivity of the specified codomain-restricted map, the single remaining hole.
Its comparison must respect embeddings into Ω; an arbitrary abstract equivalence
of separable closures is insufficient. All new nodes have real Mathlib searches,
including a recorded unavailable LeanSearch query. No change record is needed:
no existing interface or node statement changes.

## Second reading by F2

1. Compared every delivered module against the repository. The only existing file
   changed is StrictHenselizationPointedMap: two plain proof imports and its target
   proof body. Its two existing signatures and docstrings are byte-for-byte
   unchanged; the already-proved core body is unchanged. Verdict: no accidental
   interface, hypothesis, conclusion or definition change.
2. Compiled all delivered modules in import order through lcompile.py. Checked
   forbidden declarations and the sole named sorry; all definitions are concrete.
   Checked #print axioms for every new declaration and both existing theorems in a
   scratch module: only propext, Classical.choice, Quot.sound and upstream/open
   sorryAx are allowed. Verdict: type-correct reduction, with one explicit open
   surjectivity theorem, not a complete axiom-free proof.
3. Independently searched Mathlib with msearch.py (LeanFinder/Loogle/grep, and a
   recorded unavailable LeanSearch call), and searched lean/Sheaf and upstream
   lean/WeilConjectures under residue, filtered-colimit and prescribed-residue-field
   terminology. No existing public theorem states the specified evaluation
   surjectivity. The core's abstract surjection does not have the required
   pointedness. The similar residue-image and filtered-étale-fibre theorems have
   different hypotheses and conclusions. Checked the sources against
   [Stacks 04HX](https://stacks.math.columbia.edu/tag/04HX) and
   [Stacks 04GW](https://stacks.math.columbia.edu/tag/04GW).
   For Y=Spec of an algebraically closed field at its identity point, the assertions
   specialize to the usual evaluation into that field; inseparable elements are
   excluded by the étale separability hypothesis in positive characteristic.
   An empty scheme admits no such geometric point, and the constructed evaluation
   into Ω forces its domain nontrivial. Verdict: the remaining theorem is true,
   strictly smaller, and has a complete comparison argument in its docstring.
4. Read the proof from the target down. Replaced the image hole with a direct
   Mathlib proof, and discharged kernel equality using ker_eq_maximalIdeal. Kept
   the existing core's required imports; all new proof-only imports are plain.
   Recorded every obsolete proof_deps entry above. Read dag/units/sk-thm-p1.json,
   including realized: this change refines the strict-henselization tool below
   the geometric-stalk step and bypasses no unit statement or realized step.
   Verdict: shorter route below the unit, with honest decomposition accounting.
5. Matched all new nodes' lean signatures, files, proof steps and proof_deps to
   the final sources. Corrected both existing nodes' proof metadata, preserving
   their statements and stmt_deps. Added the missing definition node and replaced
   unsupported search claims with actual logged search results. Verdict: DAG and
   Lean agree; the unit route is retained.

Second-reading changes: proved image containment; removed the kernel obligation
and local-ring assumption from the new surjectivity theorem; gave the new
statements their own modules; added the canonical-evaluation definition node;
corrected proof metadata, source tags, searches and net-hole reporting.
