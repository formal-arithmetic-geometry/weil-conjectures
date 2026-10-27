## What changed

Completed `AlgebraicGeometry.Scheme.pbcPurityCompact_lattices` in
`Sheaf.Paper.RationalPurityCompactLattices`, preserving its signature and docstring.
The proof uses the existing completed local-perfect criterion for the lifted PBC
ring and extension-by-zero preservation of its stratified perfect models. Proper
actual-coefficient constructible preservation then applies to the identity
Cartesian square. The residue annihilation calculation transports ideal membership
along `ULift.ringEquiv.symm`; the coefficient and open-adjoint comparisons identify
the result with the published proper/open composite. Updated only this item's DAG
proof, proof dependencies and proof origin. All added imports are private proof
imports. No shared definitions or other modules are changed.

Validation: `lcompile.py` compiled the completed item successfully in 5.3 seconds
with no diagnostics. The theorem signature is verbatim unchanged; every Lean line
is within 100 columns. All proof imports supply declarations used by the proof.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.pbcPurityCompact_lattices`
(node `lem-pur-lifted-compact-support-lattices`).
No holes remain in the item and no holes or split statements were added.
The proof uses already stated dependencies, including the still-unproved
`integralCompletedLocalPerfectCriterion`, as authorized by stage 3.

## No longer needed

No original imports were removed, and no modules or nodes are withdrawn.
The additional ULift/local-model transport argument suggested by the original
proof plan is unnecessary: `integralCompletedLocalPerfectCriterion` and
`cbc_extension_zero_stratified_perfect` already use exactly `pbcIntegralDatum`.
Both original proof dependencies remain needed: actual-coefficient proper
preservation supplies the proper step; the uniform-restriction module supplies
`coefficientIso_eq` and `openExtensionIso` for the final identification.
No scalar, rationalization, summand or finite-field arguments are imported for
this proof. The blueprint unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The earlier node correctly noted that the unlifted uniform-restriction theorem
cannot be applied directly, but its proposed additional transport of local models
is unnecessary. Existing lifted-ring declarations already provide that part of
the argument. No statement dispute or definition repair was needed. The proof
works for the empty schemes and zero input through the existing local-perfect
criterion and extension-by-zero theorem, without a nonemptiness assumption.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
