## What changed

Replaced the sole hole in perfect_descent_affine_open with a proof combining a
canonical coordinate-ring diagram, a limit bounded-projective model, the existing
algebraic colimit descent theorem, and the stage realization comparison.
The theorem's signature and public imports are unchanged.

Added AffineDescentRingDiagram (explicit constructions, no holes),
AffineDescentSpectrumIso (proved geometric comparison), AffineDescentColimitModel
(proved representation transport), and AffineDescentStageRealization (proved perfectness
and derived pullback comparison). All modules compile with lcompile.py --all.

## Proved and sorry left

Closed AlgebraicGeometry.perfect_descent_affine_open
(lem-pc-perfect-descent-affine-open). One original hole closed; zero holes added.
No delivered declaration contains sorry. The four new modules contain actual
constructions and complete proofs, including
AlgebraicGeometry.isIso_affine_descent_colimit_toSpec,
AlgebraicGeometry.exists_affine_descent_colimit_model, and
AlgebraicGeometry.affine_descent_stage_realization.

The target obtains the stage from the existing
CochainComplex.exists_finite_projective_model_of_directed_colimit and composes
three isomorphisms. The geometric comparison is proved from finality of the upper
tail, connected pullback limits, and preservation by global sections on affine schemes.
This delivery closes one hole without splitting off another; it does not assert that
all transitive existing dependencies are free of sorryAx. The second reader's
#print axioms checks found only propext, Classical.choice and Quot.sound in all
new public declarations; perfect_descent_affine_open also has sorryAx through the
existing CochainComplex.exists_finite_projective_model_of_directed_colimit.

## No longer needed

Removed the direct proof import Sheaf.AlgebraicGeometry.PerfectAffineBoundedProjective
from the assigned module; it is still needed transitively by AffineDescentColimitModel,
so neither its node nor its module is pruned from the target closure.
The old direct proof dependencies lem-pc-perfect-affine-bounded-projective,
def-pc-perfect-complex and def-pc-derived-pullback are no longer direct dependencies
of the assigned proof node: the bounded-projective criterion is used through
lem-pc-affine-descent-colimit-model, and perfectness and derived pullback through
lem-pc-affine-descent-stage-realization and the descent predicate. The old dependency
lem-pc-affine-perfect-colimit-descent remains directly used.
No original proof-dependency node or module is globally pruned.
The new proofs use generic source tools directly instead of the separate nodes
lem-weil-pbc-limit-affine-transition-affine-comparison,
lem-pc-module-bounded-flat-kflat and lem-weil-pbc-tilde-pullback-base-change.
These were considered during the construction but are not proof dependencies here;
other targets may still need them. The definitions of
perfectness and derived pullback remain used transitively. No separate empty-derived-
category lemma is needed: isAffineOpen_bot includes that case in the affine proof.

## Where the brief, the DAG or earlier work was wrong

The earlier missing PerfectDescentOnOpen.olean blocker is resolved: the unchanged
module now compiles against the refreshed shared baseline.
The plan's two algebraic theorems do not alone supply canonical geometric ring/derived
comparisons. The delivery makes those constructions explicit, proves all the derived
model glue, and proves the affine spectrum comparison from Mathlib categorical infrastructure.

The stage realization comparison is stronger than needed in that its cocone need not
be colimiting. Its proof only uses colimit.ι_desc, whose equality holds for every cocone.
No finite-presentation, Noetherian, or nonzero-ring assumption is needed for either
geometric comparison. Those original hypotheses remain in the assigned signature.

The empty affine source, zero rings, zero complexes, and an interval with reversed bounds
were checked mathematically: the constructions yield zero objects/retractions, the
pointwise perfectness assertion is vacuous on the empty scheme, and the bounded-complex
K-flat argument uses IsZero outside the given bounds. The tail is explicitly inhabited
by i, so no nonempty-index hypothesis is added.

Source pages read: Stacks Tags 09RF (affine proof), 08EB (affine perfect criterion),
and 06YJ (K-flat computation). Repository searches found the proved affine K-flat chart
comparison and scheme-isomorphism derived transports. LeanFinder, Loogle and Mathlib
grep queries are recorded in searches.jsonl; LeanSearch returned HTTP 500, recorded
as unavailable. Blueprint searches for perfect/affine, 09RF and affine/colimit found no
node stating these exact canonical constructions or comparisons. The existing unit
sk-thm-picard-semicon has no realized affine route to bypass; the affine route of 09RF
is retained.

## New nodes

- def-pc-affine-descent-ring-diagram: explicit base changes, transition maps, coordinate
  rings, cocone, sheafification and derived realization. No arbitrary witness choice.
- lem-pc-affine-descent-spectrum-iso: the canonical scheme comparison is an isomorphism;
  proved using finality, connected pullback limits, and affine global sections.
- lem-pc-affine-descent-colimit-model: proved transport of the existing affine bounded
  finite-projective criterion across the canonical spectrum isomorphism.
- lem-pc-affine-descent-stage-realization: proved finite-free retraction construction
  and derived pullback comparison for any specified stage complex.

No existing interface changes, forced adaptations, or change records.
The affine K-flat chart comparison is used as a proved generic tool from the Picard
representability unit; it computes one supplied model and does not bypass a unit step.


## Second reading by U1

1. **Existing interfaces — pass.** Read all five modules and compared the assigned
   module with the repository using diff. Its theorem signature is byte for byte
   unchanged; public imports and existing definitions are unchanged. Only its proof,
   proof imports and proof docstring changed. The other four modules are new.
   No target or other group's module is adapted, and no change record is required.
2. **Proof and axioms — pass.** Independently compiled all five modules with
   lcompile.py --all, without errors or warnings. Searched all delivered Lean for
   sorry, axiom, unsafe, opaque, extern, implemented_by and arbitrary witness choice:
   none occurs. A scratch-copy #print axioms probe checked every new public
   declaration and the assigned theorem. The new declarations have only propext,
   Classical.choice and Quot.sound. The assigned theorem also has sorryAx via the
   existing algebraic colimit-descent theorem, whose axiom list was checked separately.
   This is one local hole closed, zero added; the target's whole dependency closure
   is not yet proved. All data in the new definitions are explicit constructions.
3. **New statements — pass.** There are no split-off sorry statements. The three
   new proved comparisons are strictly separate components: a canonical spectrum
   isomorphism, representation over its ring, and realization of a specified stage
   complex. None merely restates descent. Read their word proofs and checked zero
   rings, empty affine schemes, zero complexes and reversed bounds (which force
   every term to be zero). The tail contains i and needs no extra nonemptiness
   assumption. The stage comparison correctly permits a non-colimiting cocone.
   Independent LeanFinder search for base change of inverse limits and global
   sections, Loogle search for extendScalarsComp, and repository searches using
   colimit/model, spectrum comparison and affine descent found component tools,
   already used here, rather than a duplicate theorem. Read Stacks
   [09RF](https://stacks.math.columbia.edu/tag/09RF),
   [08EB](https://stacks.math.columbia.edu/tag/08EB) and
   [06YJ](https://stacks.math.columbia.edu/tag/06YJ) against the argument.
4. **Route and pruning — pass with report clarification.** The target starts with
   its own hole and combines the affine ring model, existing algebraic finite-stage
   descent and canonical pullback comparison. The geometry uses Mathlib finality,
   connected pullback limits and global-sections preservation directly; the derived
   comparison uses the existing proved affine K-flat chart theorem. Proof-only
   imports are plain imports; public imports supply signature or construction data.
   No shorter existing complete descent theorem was found. Checked the old
   proof_deps against the new direct route and clarified their transitive uses under
   No longer needed. No module is pruned from the target closure. The unit
   sk-thm-picard-semicon has empty realized lists for its statement and step; no
   realized unit route is bypassed or changed.
5. **DAG — pass after formatting repair.** Checked all five node records: Lean
   declarations, canonical constructions, proof steps, proof_deps unions,
   proof_origin, source, chapter/unit, creation and search records match the code.
   The existing node's interface record remains unchanged. Restored verbatim
   multiline Lean signatures in the three new theorem records. The construction's
   signature record follows preflight's convention, which omits the noncomputable modifier.

Second reading changed only node signature formatting and the report's explicit
axiom/pruning accounting; the Lean proofs and mathematical statements needed no repair.
