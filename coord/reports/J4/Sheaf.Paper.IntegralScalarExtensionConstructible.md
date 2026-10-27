## What changed

Preserve the current V5 arguments of restricted integer linearity and the normalized
completion chain, together with every existing declaration signature and public
import. Add a private component equation for `ordinaryScalarModelIso` and keep that
model irreducible while proving its tensor-section transport. This avoids unfolding
its sheafification naturality proof. Use normal transparency in the tensor-model
section (keeping the type-level compatibility setting and the localized tensor
induction setting), and the additive composition map’s `map_zero` identity.
Avoid a broad private localization import: construct the good representative with the
public K-flat resolution theorem and transport its termwise flatness through the
site tensor-right comparison. Replace `integralScalarExtension_constructible` by
an argument on this representative:
choose a good complex representing the input, apply the finite-level bound and tower
effectivity statements, and transport constructibility and cohomological bounds
through the resulting isomorphisms. The support interval is unchanged.

Two new one-statement modules isolate the actual mathematical steps: residue-field
extension followed by the target uniformizer filtration, and effectivity of the
normalized strict scalar quotient tower. These are a decomposition, not a claim to
have proved either mathematical input. Private proof imports are added for the two
inputs, the tensor-right comparison, and invariance of finite constructibility.

## Proved and sorry left

The current shared item began with three holes. Closed:
`WeilConjectures.integralScalarExtension_constructible`, by reduction to the two
strictly smaller statements below.

Remaining in the item (node `lem-weil-integral-scalar-extension-constructible`):
`WeilConjectures.integralOrdinaryDerivedScalar_constructible` and
`WeilConjectures.integralConstructibleScalarComparison_existsUnique`.

Added holes:
`WeilConjectures.integralScalarFiniteLevel_bounds`
(node `lem-sf-integral-scalar-finite-level-bounds`) and
`WeilConjectures.integralScalarTower_effectivity`
(node `lem-sf-integral-scalar-tower-effectivity`).

This currently closes one upper hole and adds two lower holes: a decomposition.
Every added hole is a public theorem in its own module with a complete mathematical
proof and source in its docstring. No definition has a hole.

## No longer needed

No existing public imports, declarations, modules or unit steps are removed.
The parent node now depends directly on the two split statements instead of directly
on their residue-field, filtration, strict-Roos and normalized-tower substeps. Those
substeps remain needed through the new nodes, so no module is claimed pruned.
The preservation proof needs only the source residue reduction and its support
interval; it does not need constructibility or bounds of higher source reductions.
The finite tensor bound has no completeness assumption, while effectivity has no
constructibility or boundedness assumption. The original low-level dependencies
remain in the plan for these split statements, or for the item's other declarations;
none is claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

The shared checkout changed while the session was running. The final packet is
based on the current V5 item and retains its two completed proofs; older temporary
versions with five holes are not delivered. The unit record has no separately
realized statement or step that this argument bypasses.

The literature used for normalized system effectivity is Bhatt--Scholze
Lemmas 3.5.4--3.5.5 (the regular uniformizer ideal permits the unbounded clause),
in addition to the parent node's completion references. No new theorem asserts
flatness of target finite quotients over source finite quotients.

## New nodes

`lem-sf-integral-scalar-finite-level-bounds` records steps 1, 3--5 of the parent's
finite-filtration argument. Its hypothesis is solely constructibility and a bound
for the source residue complex; its conclusion concerns the actual finite tensor
complexes, without any completion assertion.

`lem-sf-integral-scalar-tower-effectivity` records normalization and strict Roos
comparison followed by the existing normalized-DVR effectivity theorem. It gives
completeness and actual reduction isomorphisms without bounds or constructibility.
Both records retain the parent's chapter and unit and include search records and
verbatim Lean attachments. No existing definition or statement changes, so no
change record is needed.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
