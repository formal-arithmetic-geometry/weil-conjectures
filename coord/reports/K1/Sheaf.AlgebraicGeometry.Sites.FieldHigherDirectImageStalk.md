## What changed

Repaired the returned delivery against the current restored source, as requested in
`coord/returns/K1.md` (2026-10-21 19:26 UTC, returned head `3aa275ca46d`).
The file now exists on the shared branch; this packet starts from that current file,
rather than overwriting it with the older quarantine-restoration version.

Reapplied the substantive proof change in
`AlgebraicGeometry.Etale.nonempty_addEquiv_sheafFiber_rightDerived_lowerStar_of_isAlgClosure`:
work directly over `strictLocalizationToBase`, factor the geometric point through
`Spec.map (strictHenselizationEval s)` by the upstream compatibility theorem, and
use the existing private `nonempty_addEquiv_strictLocalization_toBase`.
Pullback preserves the universal-homeomorphism property, and `cohomologyEquiv`
and `upperStarComp` complete the additive equivalence.

Preserved every current import, all five signatures and all four private helper
proofs exactly. In particular, retained the current short comparison proof via
`smallStrictHenselizationColimitIso_toBase` and the explicit inverse in the
small-model pullback compatibility proof. The older sandbox's longer comparison
proof, extra helper spelling and stale import replacements are not reapplied.
No definition, public signature, source-library module or consumer is edited.

Updated the item's DAG proof and provenance to match the direct field argument
and the retained compatibility helpers. The Lean attachment, dependency set,
statement and unit route remain unchanged. The unit `sk-prop-sf-cbc` has empty
realized statement/step lists. Change record:
`coord/changes/K1-field-higher-direct-image-stalk-restoration.md`.

Validation: the reconciled module compiled cleanly with `lcompile.py` in
35.5 seconds. A source comparison checks all five signatures, every import and
all private helper proofs against the current source. The delivery tool performs
its own compilation, axiom checks and preflight before pushing.

## Proved and sorry left

This is a zero-hole returned repair: current source 0 sorries; delivery 0 sorries.
Holes closed: 0 of 0. Holes added: 0. Split off: 0.

The public theorem
`AlgebraicGeometry.Etale.nonempty_addEquiv_sheafFiber_rightDerived_lowerStar_of_isAlgClosure`
has a complete proof. All four current private helpers remain proved:
`isUniversalHomeomorphism_field_strictHenselizationEval`,
`strictHenselizationComparison_over`, `nonempty_addEquiv_strictLocalization_toBase`,
and `nonempty_addEquiv_strictLocalization`.
No remaining or added sorry declaration exists in the packet.

## No longer needed

No import is removed and no module or DAG node is pruned. The small-colimit
comparison is no longer used by the public field argument, but remains necessary
for the existing private compatibility API and its `import all` consumers, so
its imports, declarations and dependencies are preserved. Nothing is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The returned packet described a quarantine restoration and was based on
`c3a75e812`; the landing tools found this file had meanwhile been restored on
`sheaf-dag`. The repair follows the return exactly: read the current file, retain
its independently restored interfaces and proofs, apply the direct upstream field
argument to that file, compile and deliver again. The quarantine archive is untouched.
The previous report's claims that the item and its two consumers were absent from
`lean/` are no longer current. The consumers now exist and require no adaptations.

`tools/downstream.py` now finds nine downstream modules. The direct `import all`
consumers are `AffinePolynomialProjectionSupport` and `AffineInfinityBoundarySupport`;
their private calls keep identical signatures and proofs. Their complete modules
are not part of this packet; the consumed private helpers are retained verbatim.
The DAG's stalk-formula attachment still names a retired Sheaf wrapper; this proof
uses the official WeilConjectures owner without changing that other node.

Read Stacks `etale-cohomology.tex`, `theorem-higher-direct-images` (03Q9) and
`proposition-topological-invariance` (03SI), the current node and dependency
statements/attachments, the upstream field theorem, stalk formula and cohomology
comparison APIs. Repeated LeanFinder search returned eight structure-sheaf stalk
results; Loogle for `"IsUniversalHomeomorphism"` and Mathlib grep for
`sheafFiber.*rightDerived|rightDerived.*sheafFiber` returned no matches.
The existing upstream field theorem gives the shortest route here.
Degree zero, zero sheaves, empty sources, either characteristic and an already
algebraically closed ground field require no new hypotheses.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
