## What changed

Reduced AlgebraicGeometry.formalComparison_completed_affine_transport, preserving its
signature and existing docstring, to two strictly smaller intermediate statements:
FormalComparisonCompletedAffineData handles the algebraic comparison before sections;
FormalSystemCompletedAffineSections handles termwise sections naturally for arbitrary
formal systems, independently of a proper morphism. Added proof-only imports of these
modules and Mathlib limit preservation and scalar-change tools. A proved private lemma
limit_square_restrict assembles natural diagram squares into scalar-restricted limit
squares. The main proof constructs the two section-diagram isomorphisms, proves their
square by whiskering the transported alpha equation, and invokes that lemma.

Every delivered module compiles using lcompile.py. The main proof's heartbeat option
is scoped to that theorem; its compile takes about 20 seconds, below the 60-second
limit. No definitions, existing signatures, target signatures or public imports changed.
No data definition chooses an arbitrary witness from an unproved existence theorem.

## Proved and sorry left

Closed the original hole in
AlgebraicGeometry.formalComparison_completed_affine_transport
(node lem-weil-pbc-formal-comparison-completed-affine-transport).
There is no sorry in the item's module. The private limit_square_restrict is proved.

Added two holes, so this is a decomposition, not a proof free of new holes:

- AlgebraicGeometry.formalComparison_completed_affine_data
  (lem-weil-pbc-formal-comparison-completed-affine-data), in its own new module.
  It asserts the transported algebraic data and the natural completion comparison;
  it does not assert either section-limit isomorphism or their square.
- AlgebraicGeometry.formalSystem_completed_affine_sections
  (lem-weil-pbc-formal-system-completed-affine-sections), in its own new module.
  It asserts a natural isomorphism of termwise section diagrams, with no proper
  morphism, beta, kappa, adjunction, algebraization, or inverse limit.

These are the only sorries delivered. Each is a whole public named theorem proof,
with a source, complete proof in words, and a corresponding new node. The new
statements include the zero ideal, unit ideal, zero completion and empty affine
chart: the positive-power quotient formula and tensor unit remain valid in each.

## No longer needed

No import of the original module was removed: all six original public imports serve
its unchanged statement interface. Neither new module imports proof dependencies
that its current statement does not need. Unused ModuleCat.Limits was omitted from
both new modules; Morphisms.Proper was omitted from the section-diagram module.

The original node's direct dependencies are replaced by the two new nodes. The
formal-systems-pullback, noetherian-completion-flat, flat-base-change-resolution-iso,
flat-base-change-map-sections, coherent-hi and adic-completion-mod-power nodes remain
needed beneath the appropriate new node. They are not claimed as pruned.

The old dependency lem-weil-pbc-coherent-formal-modules-affine and its module
Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine are no longer needed by this
proof route. The generic section-diagram statement uses affine pullback sections,
power annihilation, and the completion quotient formula directly; the equivalence
with finite completed modules and its limit cones are unnecessary. This is local
pruning of this route, not a claim that no other target branch uses that module.

## Where the brief, the DAG or earlier work was wrong

The DAG gave the general formal-system and derived flat-base-change interfaces, but
none states their combination with the particular completed affine chart, arbitrary
supplied adjunction, quotient projection equations, and transported alpha. Those
interfaces require substantial glue. The data lemma isolates precisely this glue
from the independent affine section calculation. The original node's third step
needlessly called for the full affine formal-module equivalence to compare limits:
natural termwise diagram isomorphisms and Mathlib's preservation of limits suffice.

LeanSearch returned an Internal Server Error and is recorded as unavailable.
LeanFinder found completion/tensor tools; Loogle found completion/tensor tools;
Mathlib grep found no formal-sheaf transport theorem. The actual searches are logged
in searches.jsonl. No mathematical error in a unit route was asserted: this node
realizes none of sk-thm-p1's own statement or step nodes; the change is below unit
level, retaining completed base change and the positive-power quotient argument.

## New nodes

lem-weil-pbc-formal-comparison-completed-affine-data is the part before taking
sections, with a completion comparison delta and its alpha square. Its future proof
uses the original pullback and flat-base-change nodes and proper coherent direct
image. Its module is FormalComparisonCompletedAffineData.lean.

lem-weil-pbc-formal-system-completed-affine-sections is the natural termwise section
comparison for every coherent formal system. It uses the already stated affine
pullback section formula, affine formal-term annihilation, and Mathlib's completed
power quotient formula. Its module is FormalSystemCompletedAffineSections.lean.

No change records or forced adaptations are needed.

## Second reading by G3

1. **Visible declarations and signatures.** Compared the delivered transport module with the repository version. The theorem signature and all existing declarations are unchanged byte for byte; only proof-only imports, a private proof helper, and the theorem proof were added. The two added public theorem signatures are recorded verbatim in their node files.

2. **Proof checks.** Compiled all three delivered modules with `lcompile.py --all`; all compile without errors or warnings. The transport target has no `sorry`, and the only remaining `sorry`s are the two named split-off theorem declarations, each with a source, natural-language proof, and matching DAG node. No forbidden axioms, definitions containing `sorry`, or unsafe declarations were introduced.

3. **Truth and strength of split statements.** Read both split statements against their uses and edge cases. The data statement records actual pullback objects and only the required comparison data; the section statement is termwise, natural, and independent of properness. Their hypotheses and conclusions are strictly smaller than the transport target and do not restate it. The zero/unit ideal, zero completion, and empty affine cases are covered by the stated quotient formulation.

4. **Shortest route and pruning.** The target proof uses the two split interfaces and a private limit-square lemma, then Mathlib preservation of limits and scalar restriction. The old coherent-formal-modules-affine dependency and its module are no longer used by this route; all remaining proof dependencies are beneath the two split nodes. The transport unit route is retained: no unit statement or step is bypassed.

5. **DAG agreement.** Updated the target node proof, proof dependencies, and proof origin to match the delivered proof. The two new nodes include their statements, sources, proof steps, searches, Lean records, and unit/chapter metadata. No statement or definition change record is needed.

The second reading made no code changes; it added this review record and verified the delivered modules and node metadata.
