## What changed

The second reader replaced the unsound two-lemma split with one single-stage geometric
lemma, `Sheaf.AlgebraicGeometry.Morphisms.NormalFiniteStageUniversal`. The existing
`exists_normal_finite_stage_diagram` signature is byte-for-byte unchanged. Its proof now
chooses universal single-stage replacements, defines every transition map by its unique
lifting property, proves the identity and composition laws by uniqueness, and constructs
the two natural transformations and their composite equation. Only proof imports changed.
No existing definition or statement changed, and no change record is required.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.exists_normal_finite_stage_diagram`
(node `lem-sbc-normal-finite-stage-diagram`).
Hole added and left: `AlgebraicGeometry.Scheme.exists_normal_finite_stage_universal`
(node `lem-sbc-normal-finite-stage-universal`), in the new module
`Sheaf.AlgebraicGeometry.Morphisms.NormalFiniteStageUniversal`.
One of one original holes is replaced by one strictly single-stage hole. This is a
**decomposition**, not a completed geometric proof; net holes closed is zero.
The rejected proposed holes `exists_normal_finite_stage_core` and
`normal_finite_stage_integral` are not delivered.

## No longer needed

No original node or module is pruned from the transitive proof dependencies.
The original direct proof import `Sheaf.RingTheory.FiniteTypeZDomainNormalizationFinite`
is replaced by `Sheaf.AlgebraicGeometry.Morphisms.NormalFiniteStageUniversal`;
normalization finiteness remains a proof dependency of that new single-stage lemma.
The original node's old dependency
`lem-weil-pbc-finite-type-z-domain-normalization-finite` is therefore no longer DIRECT,
but is still needed transitively. Neither rejected new module is delivered.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the first worker's `normal_finite_stage_integral` was false.
Its hypotheses described arbitrary finite dominant replacements, not normalized images.
For a small counterexample take S = Spec F_p[t] and a two-stage Noetherian approximation
whose stages are S and the cusp Spec F_p[t²,t³], with the normalization arrow from S to
the cusp. The diagram has limit S and affine transitions. Take X = N.D and p the identity
natural transformation; alpha is N.pi. All its required finite and dominant hypotheses
hold, but the cusp stage is not normal. The docstring's normalization construction was
absent from its hypotheses. The proposed new nodes also lacked required metadata, and
the report incorrectly claimed that the original normalization-finiteness import remained.
The repository's original statement and image-normalization route remain intact.

## New nodes

`lem-sbc-normal-finite-stage-universal` states only the replacement of one stage, with
normality, integrality, finite and dominant maps, and the universal property needed to
construct transitions. It neither states nor constructs a diagram. Its docstring contains
the full affine-chart proof and literature source; its node carries statement dependencies,
three search kinds, creation and blueprint metadata, and the verbatim Lean signature.
No change records.

## Second reading by K2

1. Compared the delivered existing module with the repository using diff. The existing
   declaration's signature, visibility and all definitions are unchanged. No other existing
   Lean module is delivered. New statements are confined to their new module.
2. Both delivered files compile locally in import order through lcompile.py without errors
   or warnings. Explicit scratch `#print axioms` checks for both declarations show only
   propext, Classical.choice, Quot.sound and sorryAx. There is exactly one named theorem
   with sorry, listed above. No axiom, unsafe, opaque, extern, implemented_by, or holed
   definition occurs. The stage objects are specified by a universal property up to unique
   compatible isomorphism; transition maps are specified uniquely up to equality. All
   choices occur inside a theorem proof, and no data definition is introduced.
3. Rejected the false normality lemma using the two-stage cusp example above. The new
   single-stage statement is true: normalize the integral scheme-theoretic image in its
   own function field; any normal integral Y with a dominant beta has its g factor
   dominantly through that image, hence uniquely through its normalization. The normal
   stage case gives the identity, the cusp case gives its normalization, and empty sources
   are excluded by IsIntegral. Leansearch was unavailable (Internal Server Error). Leanfinder, Loogle, grep, and
   searches of both library roots
   found relative normalization APIs but no existing single-stage finite absolute-image
   normalization theorem with this universal property. The remaining construction is not
   a few-minute formalization and remains the named geometric hole.
4. The target proof now carries out the full diagram assembly, rather than applying a
   restatement of the target. All imports are justified: public imports supply the unchanged
   statement, and private proof imports supply the stage lemma and its finiteness input.
   The old dependency remains transitively needed, so there is no pruning to claim.
   Read dag/units/sk-prop-input-spreading.json and its realized fields; the normal
   approximation step and unit route are preserved, and no realized entry is bypassed.
5. Updated the original node's proof, proof_deps and proof_origin to match the actual
   assembly. Checked the new node against its Lean signature, source, proof steps,
   dependencies, chapter and unit. Removed both incomplete rejected new node files.

Second-reading changes: removed the false arbitrary-replacement normality assertion and
its companion split; added a universal single-stage replacement; implemented the actual
functor and natural-transformation assembly; repaired DAG metadata and this report.
