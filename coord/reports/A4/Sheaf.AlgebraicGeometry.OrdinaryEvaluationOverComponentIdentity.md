## What changed

Replaced the hole in `AlgebraicGeometry.ordinaryEvaluation_over_component_identity`
by a reduction to module contraction transport and the inverse dual projection.
The active-degree branch supplies the degreewise output equality and the proved
inverse dual projection to contraction transport. Explicit reduction of
`homComplex`, followed by conversion and congruence for the degreewise
complex functor, identifies the resulting component formula. The inactive branch uses preservation of zero morphisms.
Existing signatures, definitions and public imports are unchanged.

Two proof-only imports were added: `Sheaf.AlgebraicGeometry.OpenModuleContractionTransport`
and `Sheaf.AlgebraicGeometry.OrdinaryEvaluationOverDualProjection`.
The second reader proved `ordinaryEvaluation_over_dual_projection` directly
from the existing Hom projection specification, internal-Hom naturality,
the single-complex component lemmas and inverse cancellation. The new modules
publicly import only evaluation data, the existing `moduleRings` carrier and
the prescribed unit-comparison API, instead of the scheme evaluation formula.

## Proved and sorry left

Closed the existing hole:

- `AlgebraicGeometry.ordinaryEvaluation_over_component_identity`.

Also closed the first worker's proposed split-off hole:

- `AlgebraicGeometry.ordinaryEvaluation_over_dual_projection`, node
  `lem-pc-ordinary-evaluation-over-dual-projection`.

One hole is added by this delivery and remains:

- `AlgebraicGeometry.openModule_contraction_transport`, node
  `lem-pc-open-module-contraction-transport`.

The parent is a decomposition, not an axiom-free proof: one original hole
closed and one new hole added, hence net zero against the repository. The
projection lemma is proved without a new hole. The contraction theorem is a
module-level pairing identity with arbitrary dual-input and output maps; it
contains no complexes, degrees, b, hπ or evaluation-component definitions.
It does not restate the parent. All remaining `sorry` occurs in that named
public theorem with its source, complete natural-language proof and DAG node.
No data is chosen from a new existence theorem or from an arbitrary witness.

The mathematical edge-case review includes zero modules and complexes, zero
rings and empty opens. The projection proof requires neither boundedness nor
freeness. Outside r+q=0 the parent proof gives zero on both sides. No proof
introduces an extra mathematical hypothesis.

## No longer needed

No original import or original proof dependency of the parent is removed:
`def-pc-ordinary-evaluation-data`, `lem-sc-hom-complex-projections` and
`def-pc-scheme-ordinary-evaluation-component` all remain used.

From both new modules removed the oversized public import
`Sheaf.AlgebraicGeometry.SchemeOrdinaryEvaluationComponent`, replacing it with
`Sheaf.AlgebraicGeometry.OrdinaryEvaluationData` and
`Sheaf.Paper.DerivedHomMayerVietoris` (which defines the existing `moduleRings`).
From the dual-projection node removed `def-pc-scheme-ordinary-evaluation-component`
from stmt_deps, proof steps and proof_deps: its statement and proof use no
scheme evaluation component. This import trimming prunes no whole module
from the targets' closure, because the parent still uses the scheme component.
No unit step or chapter route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The parent's scalar and normalized tensorator calculation has no existing
module-level declaration implementing it. Its original dependencies provide
the constructions and Hom projection API, rather than the transport identity.
The module-contraction node records the remaining mathematical step.
The first worker also left the projection calculation as a hole; it follows
from the existing projection naturality specification and is now proved.

The first worker's report described two new holes and no import trimming;
the final delivery has one new hole and narrower imports in both new modules.
The original component proof could time out while reducing the large Hom
construction during conversion. Explicit reduction of only the Hom wrapper
and conversion at the component level avoids chasing that construction.

Independent searches used LeanFinder (single-complex component/naturality),
Loogle (monoidal and closed functors), and source grep (internal-Hom map
composition, open-equivalence transport, scalar naturality and contraction).
The search found the API used to close the projection lemma and no duplicate
contraction statement. LeanSearch was unavailable to the first worker.

Source review: [Stacks 03EO](https://stacks.math.columbia.edu/tag/03EO) gives the
ordinary tensor-Hom adjunction; [08DL](https://stacks.math.columbia.edu/tag/08DL)
gives compatibility of derived internal Hom with open restriction; the
representative computation in [08DQ](https://stacks.math.columbia.edu/tag/08DQ)
motivates the evaluation formula. The scalar-center and normalized tensorator
argument is explicitly agent-written in the theorem docstring and node,
rather than claimed to be a verbatim theorem at those tags.

## New nodes

`lem-pc-open-module-contraction-transport` is stated in
`lean/Sheaf/AlgebraicGeometry/OpenModuleContractionTransport.lean`. It isolates
module contraction compatibility, including local-section testing by extension
by zero and the common scalar in the natural Hom comparison.

`lem-pc-ordinary-evaluation-over-dual-projection` is proved in
`lean/Sheaf/AlgebraicGeometry/OrdinaryEvaluationOverDualProjection.lean`. It
isolates projection naturality and the normalized single-unit calculation.
Neither new node changes the unit's realization. No change record is needed:
existing signatures and definitions are unchanged.

## Second reading by A4

1. Compared the delivered parent against the repository with `diff` and the
   declaration scanner. All existing signatures and visibility are unchanged;
   the only existing-node fields changed are proof, proof_deps and proof_origin.
   The two extra modules are new statements. Verdict: pass.
2. Read every proof and data declaration. The parent and dual projection have
   real proofs; the only remaining hole is the named contraction theorem.
   No axiom, unsafe, opaque, implemented_by, extern or hollow definition is
   introduced. The local instances choose only the proof of the existing
   MonoidalPreadditive property. Local compilation and axiom checks are
   recorded below. Verdict: pass.
3. Reviewed both intermediate statements and their edge cases. The projection
   equality follows by naturality and cancellation and is now proved. For
   contraction, arbitrary natural Hom comparison differs from the canonical
   one by a common scalar: extension-by-zero modules test every local section.
   The normalized tensorator is determined by the unit on the same local tests.
   The scalar multiplies the dual input and output equally, so the contraction
   formula holds for arbitrary V, W, h, v and k. Empty opens and zero rings
   require no invertibility of vectors or finite-projectivity assumption.
   Both statements are strict parts of the parent's proof, not restatements.
   Independent library/Mathlib searches found no duplicate. Verdict: pass.
4. Read the three old dependencies and the unit record
   `dag/units/sk-thm-picard-duality.json`. All old dependencies remain genuinely
   used; its realized fields and every unit/chapter route are untouched.
   The new modules now import their actual carrier/data dependencies rather
   than the scheme component. The projection hole was closed by the shorter
   existing-API route. Verdict: pass.
5. Matched Lean signatures with node lean.statement after whitespace
   normalization, proof_deps with each proof's uses, and the new-node metadata
   with the stage-3 required fields. Removed the unused scheme-component node
   dependency from the projection node and updated proof origins to the final
   proofs. Verdict: pass.

Second-reading changes: proved the dual projection; narrowed imports in both
new modules; repaired parent formula reduction; corrected the module heading
and the contraction docstring's module-valued local formula; updated nodes and
this report. Existing statements and definitions were not changed.

Final checks: all three delivered modules compiled locally without warnings
(the contraction module in 7.5 seconds, dual projection in 35.6 seconds,
and parent in 56.5 seconds). The scratch axiom import check reported:
`ordinaryEvaluation_over_dual_projection` uses only propext, Classical.choice
and Quot.sound; `openModule_contraction_transport` and the parent use those
plus sorryAx from the single documented contraction hole. The delivery tool
also probes every declaration when running its preflight.
