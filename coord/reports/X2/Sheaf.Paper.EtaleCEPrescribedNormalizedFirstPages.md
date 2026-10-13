## What changed

Replaced the sorry in `AlgebraicGeometry.Etale.exists_etaleCE_prescribed_normalized_first_pages`
by a reduction to the local cohomology calculation on filtered cycle representatives.
The public signature, visibility, existing docstring and both public imports are unchanged.
Added the proof import `Sheaf.Paper.EtaleCENormalizedRepresentativeCohomology` and the existing
representative-cover module. A proved private generic descent lemma chooses filtration
restrictions, constructs the target graded cycle by pullback and image factorization,
applies the two representative equations, and cancels an epic cover followed by the actual
boundary-cokernel projection and the page comparison inverse. It constructs no spectral
sequence morphism. A local `lia` macro uses `decide` for the omitted closed numeral page bounds, avoiding
a scan of the large CE context without changing the statement text or elaborated type.
Explicit bounds in the proof also use `decide`. No proof-only `import all` remains.

Updated the item's node to match this route and added one node/module for the remaining
construction and local cohomology computation (the original plan's steps 1–3).

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Etale.exists_etaleCE_prescribed_normalized_first_pages`, node
`lem-weil-pbc-ce-prescribed-normalized-first-pages`. The private `firstPage_descend` proof
has no holes and uses the existing epic differential-representative cover.
The two final representative equations are applied directly using definitional equality
of isomorphism components; no simplifier traverses their large CE types.

Added one hole:
`AlgebraicGeometry.Etale.exists_etaleCE_normalized_representative_cohomology`, node
`lem-weil-pbc-ce-normalized-representative-cohomology`, in
`Sheaf.Paper.EtaleCENormalizedRepresentativeCohomology`.
This is a decomposition (one closed, one added), not a net sorry reduction or an
axiom-free proof of the cohomological construction. The remaining theorem only computes
classes of related representatives; it has no arbitrary first-page map M and no
filtration-restriction hypothesis. Descent to M is genuinely proved in the delivered item.

The item has no remaining sorry. The new public theorem is the only sorry in the delivery.
No definitions, axioms, existing statements or other existing modules are changed.

## No longer needed

No original imports were removed and no original planned dependency is globally pruned:
the construction/row-computation dependencies remain in the new node's proof plan.
`Sheaf.CategoryTheory.FilteredComplexQuotientComponents` and higher-page quotient descent
are not needed for the delivered descent argument and are not imported. The target cycle
factorization is proved directly instead. The original cover dependency remains directly
used; the other original proof dependencies now belong to the representative-computation
node. Neither a compatible higher-page map nor stationary-page comparisons are used in
the proof; the latter module remains a public statement dependency of the original file.

The old direct proof dependencies moved to the new computation node are:
`def-weil-pbc-ext-resolution-sections-iso`, `lem-sp-cartan-eilenberg-row-pages`,
`lem-sp-filtered-complex-graded-homology`, `lem-sp-filtered-complex-normalized-homology`,
`lem-sp-filtered-complex-page-differential`, `lem-weil-pbc-ext-pullback-resolution-sections`,
`lem-weil-pbc-sheafH-ext-derived-comparison`, and `thm-sp-if-e1`.
They are no longer direct proof dependencies of the item; none is globally pruned.
The normalized-homology module remains a public statement import.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt compiled standalone but its dry run timed out. The first resumed
full-sandbox compile passed (9.1 seconds for the new module and 54.5 seconds for the
item); the next dry run again exceeded 60 seconds on the item. Replaced the two
final simplifier calls by direct applications, using the definition of isoApp.
The revised full-sandbox compile passed without warnings, with the item at 37.4 seconds.
The wrapper reported 105.0 seconds for the new module, including compile-slot queue time before
starting Lean; no compiler timeout or error occurred. The final delivery dry run
printed OK at commit 782b3aa970: compilation and preflight passed, with only the
second reading outstanding as required. The per-compiler limit remained 60 seconds.
Both axiom probes ran without a reported rejection. Nothing was pushed.
No mathematical statement was changed or disputed. The dependency signatures do not
supply the simultaneous prescribed, normalized presentation with its signed ordinary
cohomology calculation; this interface glue is now a precisely stated local computation.
The generic quotient-components module is present in the source checkout but was absent
from the shared compiled build during this work, so it was not used or restated.

The new statement was checked on degree zero, zero rows, empty schemes and zero filtered
representatives. Its representative equations impose precisely the needed relation; it
does not assert a map of higher pages. The generic descent uses no projectivity, elementwise
lifting or finite-filtration hypothesis. The unit record `sk-prop-h2` has no realized node
among these statements, and its statement and proof route are unchanged.

## New nodes

`lem-weil-pbc-ce-normalized-representative-cohomology` records the construction and local
calculation before quotient-map descent, with the Stacks sources and the original steps
1–3 as its proof plan. Its Lean statement is verbatim in its node. It preserves prescribed
I and normalized successor comparisons, but its last conclusion concerns maps from an
individual test object to ordinary cohomology. The original theorem combines this result
with a proved representative-cover and cancellation argument; this is not an application
to a renamed copy of the original conclusion. The local elaboration-only macro is documented in
`coord/changes/EtaleCEClosedPageBounds.md`, because the static command checker classifies it
as an interface change; no actual exported interface changes or adaptations occur.

## Second reading by X2

1. Compared both delivered modules with the repository. The item has one existing
   public theorem; after removing an accidental extra space before its proof delimiter,
   its signature is byte for byte identical. Its visibility, docstring and original public
   imports are unchanged. There are no changed definitions or adaptations. The new module
   states a new theorem only. The local `lia` override elaborates closed numeral bounds
   with kernel-checked `decide`; it is local, with a change record for the static checker.
   Verdict: pass.
2. The full sandbox compiled without errors or warnings (new module 53.3 seconds,
   item 35.3 seconds including wrapper overhead). Read the chain-map restriction equations,
   source cover, target pullback/image factorization and epic cancellation in
   `firstPage_descend`. Its scratch `#print axioms` contains only `propext`,
   `Classical.choice` and `Quot.sound`. The item's public theorem additionally contains
   `sorryAx`, accounted for by the named computation theorem below. The new theorem
   itself was probed and has the same permitted set plus `sorryAx`. The only delivered
   `sorry` is `exists_etaleCE_normalized_representative_cohomology`; no forbidden command,
   hollow definition or data definition chosen from an arbitrary existence theorem occurs.
   Obtaining the existential witnesses is confined to an existential theorem proof.
   Verdict: pass as a decomposition, with zero net holes closed.
3. Read the split-off theorem, its docstring and node. It retains the construction and
   signed row calculation but has no arbitrary M and no filtration-restriction assumption;
   the delivered generic proof supplies the missing descent argument. Thus this is a
   strictly earlier part of the argument, rather than a renamed copy of the target.
   At p = 0 the sign is 1 and ordinary degree-zero cohomology uses the same augmentation;
   zero representatives give zero graded cycles by monicity; zero rows and empty schemes
   give zero cohomology. Negative q does not change the argument: the common signed factor
   is invertible and cancels. No projectivity or lifting of elements is assumed.
   Repeated searches with different queries using leanfinder, loogle and grep, and searched
   lean/Sheaf and upstream SixFunctors. The hits on injective-resolution naturality and
   spectral-object first-page isomorphisms do not supply prescribed CE presentations,
   normalized successor comparisons and their cross-scheme cohomology calculation.
   Existing generic representative covers are used. The remaining construction cannot
   be closed by a short application of these hits. Verdict: pass; one split-off hole.
4. Read the proof from its conclusion down to the generic cancellation and the local
   computation. Both added imports are proof-only plain imports; the two public imports
   supply signature notions. No higher-page comparison morphism is constructed.
   The report now explicitly enumerates every old dependency moved off the item's direct
   proof plan. None is globally pruned. Read `dag/units/sk-prop-h2.json`: its realized
   statement list is empty and its steps contain an empty list, so this route bypasses no
   realized unit node and changes no unit statement or step. Verdict: pass.
5. Compared the node records to the Lean declarations and the proof. The existing node
   changes only proof, proof_deps and proof_origin. The new node has matching verbatim Lean,
   source, docstring route, search records and all required provenance fields. Its proof_deps
   equal the union of its planned step uses; the item uses exactly the local computation
   and differential-representative cover nodes. Updated the item's proof_origin wording
   to include the actual descent and cancellation. Verdict: pass.

Changes in this reading: restored exact signature whitespace, corrected the new module's
copied author group from R3 to X2, enumerated moved dependencies, clarified proof provenance,
and added this independent review. No mathematical statement or proof argument was changed.
