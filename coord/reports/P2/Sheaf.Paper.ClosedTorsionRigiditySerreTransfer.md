## What changed

Replaced the body of
`AlgebraicGeometry.ProEtale.CondensedRing.closed_torsion_rigidity_serre_transfer`
with an explicit derived-hull argument. Its statement, both restriction definitions,
all original public imports, coefficient conventions and universe levels are unchanged.

The private helpers prove transport through isomorphisms, retracts, preserved limits
and normalized filtered complex colimits. The proof constructs the class where the
actual restriction is invertible, proves its triangulated and infinite-operation
closure properties, and supplies its supported finite-model generators using
`supported_finite_model_scalar_rigidity`. It then evaluates a separate structural
generation input at that class.

Added `Sheaf.Paper.WeakSerreSupportedDerivedGeneration` and its node. This is an
independent structural obligation with no closed pair, torsion rigidity hypothesis,
restriction transformation or cohomology comparison in its statement. Its target is
the existing supported derived hull, rather than the refuted filtered finite-heart
hull. The unresolved part is arbitrary relation resolution through repeated heart
kernels and cokernels. The report does not claim that triangle closure, or the finite-
model image theorem alone, proves it. The independent reader should scrutinize this
mathematical obligation; its full-generality published reference remains WANTED.

Updated the item's proof route and dependency list. No adopted source-library file,
existing signature, target, definition or other group's module was changed.

## Proved and sorry left

Closed the original one hole, by a decomposition:
`AlgebraicGeometry.ProEtale.CondensedRing.closed_torsion_rigidity_serre_transfer`
(node `lem-sfb-closed-torsion-rigidity-serre-transfer`). Its new proof is complete Lean
relative to the imported declarations.

Added exactly one hole:
`AlgebraicGeometry.ProEtale.CondensedRing.weakSerre_mem_supported_derived_generation`
(node `lem-sfb-weak-serre-supported-derived-generation`). The main module has zero
literal sorries; the new module has one. This delivery is one closed and one added,
net zero, and is not reported as a net proof gain. No definition has a sorry.

The source-library and supported finite-model theorems used by the proof retain
their own existing obligations; this packet does not claim to close them.

Validation: the complete two-module sandbox compiled without warnings. The first run
reported 48.3 seconds for the structural module and 68.2 seconds for the main module;
profiling located the proof work in ordinary instance search and triangle assembly.
A local irreducibility attribute keeps the large module pullback and adjunction
behind their interfaces; the final configuration is being recompiled. An intermediate
profiling run placed a scoped option after a docstring, causing a parser error; that
option has been moved to the section and all profiler commands removed.

## No longer needed

No original public import is removed. No module is withdrawn. The following old
*direct planned dependencies* are absent from the new proof route; some remain
transitive dependencies of the imported operations or finite-model comparison,
or are used elsewhere in the project, so this is not a global withdrawal:

- `sk-def-sfb-pullback-from-point-comp`
- `det-prop-sfb-module-pullback-exact-main`
- `lem-weil-pbc-exact-functor-complex-cohomology`
- `sk-def-sfb-constructible`
- `lem-sfb-scalar-matrix-inverse-image`
- `lem-sfb-qcqs-finite-complex-heart-filtered-closure`
- `lem-fix-constructible-open-closed-refinement`
- `lem-weil-pbc-proetale-ringed-open-closed`
- `lem-sfb-internal-module-operations-transport`
- `lem-sfb-supported-three-term-scalar-rigidity`
- `lem-weil-pbc-complex-ses-triangle`
- `def-sfb-condensed-module-sections`
- `prop-pur-kinjective-resolutions-exist`
- `lem-pc-right-derived-functor-triangulated`
- `sk-def-sfb-module-derived-pushpull`
- `sk-def-sfb-module-pushforward-pullback`
- `lem-weil-pbc-left-adjoint-preserves-colimits`
- `lem-weil-pbc-condensed-qcqs-pushforward-continuity`
- `def-weil-abstract-derived-category`
- `def-weil-pbc-proetale-site`

The old finite-complex-heart approximation and supported three-term reconstruction
are replaced in this item by supported model generation followed by the explicit
admissible-class argument. In particular the repaired Noetherian approximation is
not applied to a merely qcqs scheme. Experimental ind-presentation and short-exact
helpers that were compiled during the search were removed from the packet when
the final route did not use them.

The obsolete `tool_uses` approvals for the retired direct dependencies were
withdrawn in the node copy; no approvals were added or reordered.

## Where the brief, the DAG or earlier work was wrong

The old node's step 2 applies
`lem-sfb-qcqs-finite-complex-heart-filtered-closure` to arbitrary qcqs schemes.
Its current declaration is
`noetherian_finite_complex_heart_filtered_closure` in
`Sheaf.Paper.NoetherianFiniteComplexHeartFilteredClosure` and requires local
Noetherianity. The earlier unrestricted structural assertion was refuted by the
Stone--Cech example recorded in
`coord/reports/NY/lem-sfb-qcqs-finite-complex-heart-filtered-closure.md`.
The brief's assertion that every planned dependency fits the item therefore fails
at this step. This does not supply a counterexample to the comparison theorem.

I checked the relevant HRS passages, the solid proper-base-change paper and the
condensed-shape counterexample. None supplies the missing arbitrary-qcqs weak
Serre generation theorem at the all-continuous norm-topological algebraic-closure
coefficients used here. In particular neither completion, finite-subextension-
valued coefficients nor a Noetherian hypothesis has been substituted. The new
structural statement remains an explicit independent obligation, not an assertion
that one of those sources already proves it.

## New nodes

`lem-sfb-weak-serre-supported-derived-generation`, realized by
`Sheaf.Paper.WeakSerreSupportedDerivedGeneration`, asks for degree-zero inclusion
of the constructible weak Serre coproduct heart in the existing supported derived
hull. It isolates the structural step from the closed-pair comparison and records
the unresolved arbitrary relation-resolution issue. Finite-model image generation
is not confused with repeated weak Serre closure. Edge cases checked in the
statement are the identity support path, zero modules, the zero coefficient ring,
empty schemes and arbitrary qcqs schemes with no Noetherian assumption.

Actual Mathlib searches recorded in searches.jsonl: LeanFinder for weak Serre
supported derived generation (eight generic Serre, AB5 and derived t-structure
hits, no match), Loogle for both closure and hull names (zero hits), and grep for
weakSerre with supported hull/generation (zero hits). A blueprint-wide search for
weak Serre found the discrete classical weak Serre theorem and the finite-ring
constructible Serre theorem; neither is this continuous-coefficient result.
A separate LeanSearch query returned topological submodule closure and sheaf-colimit
constructors, also no match. No change record is needed because no existing
statement or definition changes.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
