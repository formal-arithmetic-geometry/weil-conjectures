## What changed

Replace the upper-bound proof of
`AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_adicConstant`
in `WeilConjectures.WeilSheaf.Finiteness`, preserving its signature and all public imports.
Use the existing ordinary finite-coefficient direct-image bound, its existing constant-adic
transfer theorem, proper coincidence, and localization on a dense proper compactification.
The boundary has strictly smaller dimension. Its empty geometric fiber is handled separately.
Six new private declarations construct the required identifications and prove the glue;
none contains a hole. The retained revision passed the required delivery compiler check
and preflight on 2026-10-19 (dry-run commit fb07cb116d).

Withdraw `Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison` under brief step 8d.
Finiteness is its sole direct importer and sole external declaration consumer. Update both
DAG node copies to record this route and the withdrawal. No target statement changes.

## Proved and sorry left

The assigned module originally has one hole:
`AlgebraicGeometry.WeilSheaf.exists_injective_compactSupportFiniteCoefficientComparison`
(node `lem-pod-compact-support-finite-coefficient-comparison`). It is pruned by withdrawal,
not claimed proved: 0 of 1 holes proved, 1 hole pruned, 0 holes added, 0 split off.
There are no holes in the delivered Finiteness module or the withdrawn empty module.

The unchanged parent statement now has a complete Lean proof from existing declarations.
The already stated dependency
`AlgebraicGeometry.ProEtale.isLE_rightDerivedFunctor_adicLowerStar_unit_of_finite_bound`
(node `lem-pod-adic-unit-direct-image-finite-bound`) remains an existing unproved theorem;
this delivery does not claim to prove its transitive dependencies.

## No longer needed

Withdraw the comparison module, including `finiteLevelCompactSupportSections` and
`exists_injective_compactSupportFiniteCoefficientComparison`; remove its proof import from
Finiteness. Remove the redundant private imports
`WeilConjectures.WeilSheaf.LowerStarPairing`,
`WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension`, and
`WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CohomologicalDimension`.
The retained public LowerStarPairing import preserves that API; FieldBaseChangeDimension is
publicly supplied by the new DirectImageVanishing import.

The withdrawn comparison's nine planned dependencies need no proof for that embedding:
`def-weil-integral-rational-qbar-compact-support`, `def-weil-finite-coefficient-point`,
`lem-weil-constant-coefficient-objects-constructible`,
`prop-finite-compact-support-constructibility`, `lem-weil-pbc-mittag-leffler`,
`def-weil-l-adic-coefficient-extension`, `lem-pc-flat-tensor-complex-cohom`,
`def-weil-ordinary-compact-cohomology`, and `def-weil-constant-weil-structure`.
The withdrawn file's proof imports are CoefficientExtensionFinite,
CommonStageCompactWeilCohomology, ConstantCoefficientScalarNormalization,
ConstantWeilStructure, FiniteCoefficientPoint, FiniteCompactSupportConstructibility,
FiniteMittagLeffler, and QcqsCompactSupportRealization in their original Sheaf namespaces.
They may still be needed elsewhere; no global unreachability is asserted for shared modules.

The parent's superseded integral-amplitude route no longer uses these proof dependencies:
`def-weil-finite-tor-amplitude`, `def-weil-integral-rational-qbar-compact-support`,
`def-weil-l-adic-coefficient-extension`, `def-weil-point-fg-complete-complexes`,
`lem-coef-integral-compact-support`, `lem-pod-dvr-complex-amplitude-mod-uniformizer`,
`lem-pod-point-sections-derived-reduction`, and
`lem-weil-constant-coefficient-objects-constructible`.
Remove the obsolete `tool_uses` approval `lem-pod-point-sections-derived-reduction`;
retain the proper-coincidence and its Frobenius-compatibility approvals in their old order. Unchanged dependency copies of CohomologySequence,
OpenClosedTriangle and UpperStarConstant are omitted from the delivery.

## Where the brief, the DAG or earlier work was wrong

The comparison embedding is stronger than its only consumer requires. Ordinary vanishing
on the compactification and its lower-dimensional boundary proves the same compact-support
range. The earlier sandbox's unfinished route had missing instances, dependent equality
transport errors, and implicit instance search across cohomology definitions. These have been
repaired using the existing equality isomorphism and explicit transport of subsingleton proofs.

Sources are Milne, Lectures on Etale Cohomology, Theorems 15.1 and 19.2, §8.15 and
Proposition 18.3(a), together with the proved dense compactification and dimension theorems.
The current unit record's realized lists do not contain the withdrawn auxiliary embedding;
its perfectness statements and coefficient-stage route are retained.

The change record is `coord/changes/Y5-compact-support-comparison-withdrawal.md`.
No new DAG nodes or public theorem interfaces are introduced.

Verification: the required resumed dry run returned OK at commit fb07cb116d, with review
class CODEX. The adapted Finiteness module compiled and the preflight passed. The axiom
probe received no answer from the compile service and is explicitly deferred by deliver3.py
to the merge check; no successful axiom-probe result is claimed. A separate profiling run
encountered an unavailable published OpenClosedTriangle artifact, whereas the successful
delivery compiler check had the imports available. Earlier attempts, including a trivial
Mathlib-only probe, received no compile-service answer rather than a Lean timeout.
No timeout limit was changed and no launcher script was modified.

## Second reading by Y5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
