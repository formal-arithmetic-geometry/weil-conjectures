## What changed

The item now combines signed differential, naturality, coproduct-summand,
transition and coefficient/tensor square calculations. The four new modules
separate the mathematical results: normalized kappa values, scalar tensor
transitions, the whole coefficient-transition squares, and generalized pullback
tensor sections. Their proof terms contain no `sorry`.

The differential calculation is proved generically in additive monoidal
categories and specialized to module sheaves. The signed second differential
retains the integer sign in every degree, including negative odd degrees.
The existing cochain comparison supplies the full direct-sum map and its
coproduct equations. Canonical uniqueness identifies the normalized module
comparisons and scalar association; existing cochain coherence then gives the
coefficient/tensor square. Arbitrary-arrow naturality and its section formula
supply the remaining square value by specialization and linearity.

Named maps share the original tensor comparison, total maps, differential
summands and inclusions. Existing section predicates and formulas delegate to
the same formulas in the calculation modules. All replacements are
mathematically and definitionally equal to the original expressions. The
existing theorem signature is unchanged. No adopted source module is edited.
Definition changes and their complete old/new texts are recorded in
coord/changes/strict-totalization-map-presentation.md. The signed total itself
keeps its body and binders, with a semireducible `def` replacing its `abbrev`;
coord/changes/named-signed-total.md records this definitional presentation repair.

## Proved and sorry left

Original hole: one, in
CategoryTheory.CochainPullback.StrictCoefficient.coefficientComparisonsStrictTotalization.
Its proof term is filled. No holes are added; none remain in the six changed source
files of the packet, and no definition or private helper contains a hole.

The four new proved theorem statements are:

- CategoryTheory.CochainPullback.StrictCoefficient.KappaCalculation.normalizedKappaTransitionValues
  (lem-pur-normalized-kappa-transition-calculus).
- CategoryTheory.CochainPullback.StrictCoefficient.ScalarCalculation.normalizedScalarTensorTransitions
  (lem-pur-normalized-scalar-tensor-transitions).
- CategoryTheory.CochainPullback.StrictCoefficient.normalizedCoefficientTransitionSquares
  (lem-pur-normalized-coefficient-transition-squares).
- CategoryTheory.CochainPullback.StrictCoefficient.PullCalculation.normalizedPullTensorGeneratorSections
  (lem-pur-normalized-pull-tensor-generator-sections).

All six delivery files compiled in import order on the project server without
diagnostics; the complete main theorem took 50.5 seconds. The original theorem
text is preserved exactly. The unchanged H1 unit/composition consumer also
compiled against the repaired total in 7.9 seconds in the earlier check.
All four original consumers compiled without diagnostics against the completed
packet: unit/composition (0.7 seconds), strict coefficient calculus (11.6 seconds),
balanced finite-tower comparison (27.3 seconds), and completed quotient realization
(58.7 seconds). Their sources and signatures are unchanged; no adaptations are
necessary.

## No longer needed

The main module does not require explicit proof imports of ModuleTensorGenerators,
HasLimits, Adjunction.Limits, ModulePullbackPushforwardAdjunction or
TensorBilinearUniversal. The new normalized transition modules own the needed
calculations. CochainPullbackTensorCoherence is a private proof import; its data
are already available from the existing interface.

The kappa calculation itself uses no module tensor calculations. Its exploratory
imports of ModuleTensorGenerators, HasLimits and TensorBilinearUniversal were removed,
as were redundant public imports of RingedSiteModules, CochainTensorUniverses
and BifunctorShift, which NormalizedCoefficientDiagram already exposes.

The main proof does not directly invoke lem-weil-pbc-left-adjoint-preserves-colimits
or def-weil-pbc-category-colimit: it uses the existing constructed total comparison
and Mathlib coproduct-desc equations. Their underlying library declarations remain
untouched. The scalar tensor extensionality proof uses the proved pure-section test in
CochainTensoratorExistence, so it needs no direct TensorBilinearUniversal import.
Tensor universality and scalar adjunctions remain needed elsewhere in
the argument, so those nodes are not pruned transitively. No existing module is
withdrawn, and the blueprint unit route is retained.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original plan understates the Lean distinction
between module scalar-extension objects and degree components of their cochain
lifts; explicit identifications are needed for several rewrites. The coefficient/
tensor square already follows from the existing cochain coherence theorem once
uniqueness identifies the given normalized comparisons.

The downstream strict coefficient calculus now imports the item and uses its
full theorem. The original consumer sources are checked against the completed
packet. The unfinished DAG parents remain needed.

Earlier delivery attempts stopped at the 60-second file limit on the mirrored
compile service. The project-server compile then validated the entire six-file
packet within the same limit. No compiler limit or launcher file was changed.

The prior attempt began at 2026-10-23T12:40:43Z. A launcher resume reset the reference
clock to start 1792769009.199156; this worker has not edited budget metadata.
Interrupted compiler results were checked before resuming work. No delivery had
started before the resume.

## New nodes

lem-pur-normalized-kappa-transition-calculus records the forward and inverse
coefficient formulas on arbitrary algebraic inverse-image sections. Its proof
uses normalization, scalar linearity, adjoint uniqueness and the ring-diagram
square, with no inversion of the arbitrary transition adjoints.

lem-pur-normalized-scalar-tensor-transitions records scalar tensor transition
naturality together with both coefficient formulas. Coproduct equations lift
the normalized module formulas to totals; two scalar adjunctions and sheaf
tensor universality turn the formulas into equality of whole maps.

lem-pur-normalized-coefficient-transition-squares records the whole kappa
transition square and the two scalar tensor squares. Kappa generator tests and
the proved value formula handle the first, and the preceding scalar theorem
handles the other two.

lem-pur-normalized-pull-tensor-generator-sections records the generalized
pullback tensor formula. Its hypothesis explicitly specifies the homogeneous
tensor section, and generator naturality, the scalar tensor formula, and kappa
normalization prove its value without assuming local lifting of sections.

The statements allow zero rings, zero modules and zero transition adjoints,
identity coefficient changes, non-flat ring maps, unbounded complexes and
arbitrary negative degrees. No flatness, boundedness or invertibility assumption
was added. Change records: coord/changes/strict-totalization-map-presentation.md and
coord/changes/named-signed-total.md.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
