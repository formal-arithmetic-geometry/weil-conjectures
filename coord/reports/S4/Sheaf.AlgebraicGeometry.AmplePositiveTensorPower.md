## What changed

Completed the retirement assigned by coord/retire-items.tsv. Withdrew
Sheaf.AlgebraicGeometry.AmplePositiveTensorPower through deleted.txt and replaced its
private proof import by WeilConjectures.AlgebraicGeometry.AmplePositiveTensorPower in
Sheaf.AlgebraicGeometry.GluedComponentAffineSection,
Sheaf.AlgebraicGeometry.NoetherianFibreAmpleNeighbourhood and
Sheaf.TraceFormula.GradedImmersionAmpleCriterion. Each adapted module replaces one
private import. The returned-packet repair also removes the warning-suppression command
`set_option warn.sorry false` from GradedImmersionAmpleCriterion: the landing census
misread its option name as an unattributed hole. All declaration signatures and proof
bodies are unchanged. All three consumers are recompiled on the server before delivery. The DAG node lem-sc-ample-positive-tensor-power
now points at the existing upstream theorem and describes its local-frame proof.

The public signatures and public imports of the two modules agree. The upstream twin's
private proof detects nonvanishing by a unit coefficient in a local frame, raises that
coefficient to k, and transports the section along the tensor-power isomorphism. This
matches Stacks properties.tex, lemma-ample-power-ample (01PT), following Definition 01PS.
The local-frame proof handles the zero section and empty scheme and uses k > 0 in
isUnit_pow_iff. No unit-level argument is bypassed.

Change record: coord/changes/retire-ample-positive-tensor-power-S4.md.

## Proved and sorry left

This is a retirement with zero holes in the assigned module: 0 holes closed, 0 holes
added, 0 split off. AlgebraicGeometry.Scheme.Modules.isAmple_positive_tensorPow was
already proved in both modules; its proof is retained in the upstream module.
The upstream #print axioms check reports exactly propext, Classical.choice and Quot.sound.

The import-only consumer adaptations preserve their two pre-existing holes:
AlgebraicGeometry.Scheme.Modules.exists_affine_isAmple_of_fiber_of_noetherian
(node lem-trf-noetherian-fibre-ample-neighbourhood) and
AlgebraicGeometry.Scheme.Modules.graded_immersion_ample_criterion
(node lem-trf-graded-immersion-ample-criterion). Neither hole is introduced by this packet.
GluedComponentAffineSection has no hole.

## No longer needed

Retire Sheaf.AlgebraicGeometry.AmplePositiveTensorPower and its unused-outside-the-file
private nonvanishingLocus_app_one helper. Remove its import from all three direct
consumers and replace it with the upstream twin. The mathematical node and public
isAmple_positive_tensorPow declaration remain available at the upstream attachment.
The retired proof's private AffineComplement import is no longer needed by this proof;
the source AffineComplement module and all its declarations remain intact. The upstream
proof uses the existing SectionNonvanishingZeroLocus and AmpleIso private helpers.
No additional modules or mathematical nodes are claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief described a repeated unfinished obligation, but the live module
is already proved and the current queue explicitly assigns retirement (three consumers).
The reported DIFFERENT API consists of a private helper with no external users. The
retirement therefore needs no replacement lemma or consumer proof edit. The old DAG
proof described the retired zero-locus proof; it now records the upstream local-frame route.

The returned head af33c0a1a passed review but failed landing because the hole census
counted the `sorry` component of the warning option as an unattributed hole at line 34.
Removing that nonessential warning-suppression command repairs the packet; the real
existing hole remains in its named theorem. The retained packet was compared against
that returned head and current sheaf-dag; no intervening consumer edits were lost.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
