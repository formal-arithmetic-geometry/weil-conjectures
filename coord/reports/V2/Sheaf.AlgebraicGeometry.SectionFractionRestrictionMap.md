## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_sectionFraction_restriction_map`
in `Sheaf.AlgebraicGeometry.SectionFractionRestrictionMap`, with the existing signature,
visibility unchanged. The second reading removed the redundant proof import
`Mathlib.LinearAlgebra.Quotient.Basic`. The proof follows the node's canonical-map argument.

For each numerator degree, tensoring with the free generator is a linear bijection by
`isFreeGenerator_tensorPowSectionOne` and
`IsFreeGenerator.bijective_tmulSection_right`. Its inverse, composed with restriction,
is semilinear over restriction of scalars. `DirectSum.toAddMonoid` combines these maps;
direct-sum induction proves scalar compatibility. Tensor injectivity,
`mulTensorPowSection_app_tmulSection`, and `Hom.app_presheaf_map` show that every
relation is killed. `Submodule.span_le` and `Submodule.liftQ` give the quotient map,
and `liftQ_apply` gives its tensor formula.

These are existing proved declarations exposed by SectionFractionPresentation's
imports. No new theorem, definition, module, import or DAG node is needed. The node's
proof and its dependency route are unchanged. The unit has no realized statement or
step nodes that this construction bypasses.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Scheme.Modules.exists_sectionFraction_restriction_map`
(node `lem-sc-p1-section-fraction-restriction-map`).

Holes closed: 1. Holes added: 0. Sorries left in the delivered module: none.
This is a proof, not a decomposition. The inverse is chosen from a proved linear
bijection and is uniquely determined; no arbitrary existence witness is used.

The module compiles cleanly with lcompile.py. The proof handles degree zero,
zero transition exponent, the empty open, and the zero numerator module without
extra hypotheses. The delivery dry run checks the axioms as well as compilation.

## No longer needed

`Mathlib.LinearAlgebra.Quotient.Basic`: removed its redundant explicit proof import;
its quotient API is already available through SectionFractionPresentation. Compilation
without it succeeds. SectionFractionPresentation remains necessary for the statement
and construction. The old proof_deps list is empty, so no dependency node is bypassed
and no project module is pruned from the target closure.

## Where the brief, the DAG or earlier work was wrong

No statement or interface error was found. The node's proof plan is executable using
already proved source-library tensor identities, despite its empty proof_deps list.
No missing intermediate statement needs to be added. The local literature files named
by the node were absent; the Stacks source was read at
https://stacks.math.columbia.edu/tag/01PW instead. The canonical-map construction is
exactly the recorded restriction-and-division route and uses neither quasi-coherence
nor compactness. Search found generic quotient and presentation APIs, but no complete
Mathlib section-fraction restriction map.


## Second reading by V2

1. Compared the entire delivered module with the read-only repository using diff.
   The existing declaration signature, docstring, visibility, universes and surrounding
   commands are byte for byte unchanged. The only initial change was replacement of
   the theorem's sorry by its proof. No definition or statement changed; no change
   record is required. Verdict: pass.
2. Compiled the delivered module locally with lcompile.py, without errors or warnings.
   A scratch copy with #print axioms reports exactly propext, Classical.choice and
   Quot.sound. There are no sorries, axioms, unsafe declarations, opaque declarations,
   extern attributes or implemented_by directives in the delivery. The inverse of
   the explicitly constructed tensor map comes from a proved bijection and is
   uniquely determined. Verdict: pass.
3. No statements were split off, and no new statements or nodes were introduced.
   Checked the existing tensor-generator lemmas and their proofs. Their degree-zero
   cases use the unit generator; the relation argument also applies when b = 0.
   Nothing excludes the empty open or zero module. Verdict: pass, no new holes.
4. Read the construction from its conclusion back through quotient descent, relations,
   scalar compatibility and tensor inverses. Searched the library for fraction and
   restriction maps and ran LeanFinder with a different query about semilinear
   direct-sum descent. The existing DirectSum.toModule API is linear over one ring;
   the current additive-map construction plus scalar induction directly handles
   restriction of scalars. No existing complete restriction map was found. Tested
   removal of Quotient.Basic in a scratch copy: compilation passed, so removed that
   redundant explicit import. No longer needed now records it. The unit
   sk-thm-picard-duality has realized.statement = [] and realized.steps = [[]];
   no recorded unit node or route is bypassed. Verdict: pass after import cleanup.
5. Read lem-sc-p1-section-fraction-restriction-map in full. Its proof describes precisely
   the inverse tensor maps, direct-sum construction, relation cancellation and quotient
   descent in the Lean proof; its empty proof_deps list and document proof_origin remain
   accurate. There are no new nodes to check. Verdict: pass.

Changed only the redundant proof import and this report; the proof is retained.
Holes closed: AlgebraicGeometry.Scheme.Modules.exists_sectionFraction_restriction_map
(1). Holes added: none (0). No decomposition or project-module pruning.
