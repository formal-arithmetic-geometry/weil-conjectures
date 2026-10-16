## What changed

Repaired H10 from reviewer X-18231 at returned head 182318d4b. Timing probes
located the expensive elaboration in the long dependent `obtain` inside
`finite_range_exchange_comparison`'s cohomology argument. The same witness
extraction now names two intermediate remainders and uses three short
`obtain` commands. All subsequent proof steps, the theorem signature, the
local irreducibility setting, and the module boundaries remain unchanged.
No theorem or proof obligation is split off. The repair changes no definition.

The retained sandbox was compared with the returned version and the current
shared sources. Its earlier proof, import pruning, and helper reuse remain:
`DerivedCoupleFunctoriality` exposes `exactCoupleFiniteTransport` and
`factors_iff_image_le` in place; both delivered modules reuse the public
`ExactFunctorHalfPlane.transport_square` at the identity functor. This retry
makes no further change to `DerivedCoupleFunctoriality`. The node's
`proof_origin` additionally records the elaboration repair; its mathematical
proof steps and dependencies are unchanged.

New change record: coord/changes/finite-range-comparison-elaboration.md.
Retained records:
coord/changes/finite-range-comparison-reuse-functoriality.md,
coord/changes/finite-range-comparison-import-pruning.md, and
coord/changes/finite-range-comparison-private-context.md.

Validation: the unchanged returned version reproduced exit 124 after 60 s.
After repair, `lcompile.py --all` compiled both modules without warnings
(4.9 s and 14.2 s). Standalone compilation of FiniteRangeComparison passed
in 14.0 s. The compiled-module `#print axioms` audit of the target, both
exposed helpers, reused transport lemma, and derivedCoupleFunctoriality
reports only propext, Classical.choice, and Quot.sound. Both delivered
modules have zero sorry tokens, no forbidden declarations, and no Lean line
over 100 characters. Profiling commands have been removed.

A fresh downstream.py audit reports zero downstream consumers of the item.
No consumer adaptation is needed. The earlier DerivedCoupleFunctoriality
consumer audit and its Users table are retained in the earlier change record.
The old second-reading section is removed for a fresh independent reading.

## Proved and sorry left

The retained delivery closes the sole original hole:
AlgebraicGeometry.Etale.finite_range_exchange_comparison
(node sbc-lem-finite-range-comparison): 1 of 1 original holes closed.
This H10 repair closes no additional holes. Holes added: zero.
Split off: zero. Holes left in both delivered Lean modules: zero.
All private helpers are proved. The theorem's complete signature is unchanged.
The item is outside the current targets' import closure according to the
retained import-pruning audit; no closure-wide hole decrease is claimed.

## No longer needed

No further import, node, or module is pruned by this elaboration repair.

Retained pruning: node lem-sp-page-induction and proof import
Sheaf.CategoryTheory.SpectralSequencePageInduction are unused; page
isomorphism induction is proved locally. The duplicate private
transport_square is removed from DerivedCoupleFunctoriality; both modules
reuse the already public functorial version in ExactFunctorHalfPlane.
The four copied helpers remain absent from FiniteRangeComparison.
No module is withdrawn.

Retained removed public imports:
Sheaf.AlgebraicGeometry.ChosenCartesianSquare,
Sheaf.AlgebraicGeometry.DerivedCategories, and
Sheaf.AlgebraicGeometry.HypercohomologyFiltrations.

## Where the brief, the DAG or earlier work was wrong

Earlier timings of 53–56 seconds gave insufficient margin below the fixed
60-second limit. The retained local irreducibility setting did not repair
the expensive dependent witness elimination; the return correctly required
an additional elaboration repair. That extraction now completes quickly
without changing the data or any mathematical step.

The earlier incorrect duplicate-helper exposure was already repaired by
reusing ExactFunctorHalfPlane.transport_square, as recorded in the retained
change records. No new mathematical issue was found. No unit route, target
statement, or tool is changed.

## Second reading by C3

Independent second reading, 2026-10-16, after the H10 elaboration repair.

1. **Visible statements and definitions: PASS.** Diffed both delivered Lean
   modules against the shared repository. The full 2,196-character signature of
   `AlgebraicGeometry.Etale.finite_range_exchange_comparison` is byte-for-byte
   identical. No definition body or existing public signature changes. The two
   helper visibility changes, deleted private transport duplicate, proof-only
   transport import, removed public imports, and private proof context are all
   declared in the retained change records. Compared the repaired item with the
   retained returned source: only the long dependent witness elimination and its
   explanatory comment differ. The three shorter eliminations recover exactly
   the same witnesses. Rechecked downstream sources: zero item consumers and
   1,337 transitive consumers of DerivedCoupleFunctoriality. The two newly public
   helpers have no existing external source uses.

2. **Kernel proofs and compilation: PASS.** Ran the required local
   `lcompile.py --all` on the actual delivery: both modules compiled without
   warnings in 4.9 s and 12.9 s. Made fresh scratch copies of these exact files
   and appended `#print axioms` for every theorem, including all private helpers:
   all 17 declarations use only `propext`, `Classical.choice`, and `Quot.sound`
   (family_conj uses only propext). These scratch copies also compiled in
   4.3 s and 14.6 s. Both delivery files have zero sorry tokens, no forbidden
   declaration or kernel-check bypass, and no line over 100 characters. There
   is no new definition or arbitrary witness chosen from an unproved theorem.

3. **Split-off statements and small cases: PASS.** No statements or holes are
   split off, and neither delivered module contains an open theorem. Read the
   private page-kernel, successor-cokernel, inverse-transport, limit restriction,
   finite-image, and filtered-map arguments. Their hypotheses supply exactly
   the squares and isomorphisms used. Checked the zero page, zero subobjects,
   a = b, and total degree n < a: none requires a nonzero object, a nonempty
   cohomology range, or a stronger lower bound. Only vanishing below a is used;
   retaining the unused upper-bound hypotheses preserves the original theorem.

4. **Route, reuse, and pruning: PASS.** Read the blueprint proof and the unit
   record sk-rem-rest, whose realized statement and steps are empty and stay
   unchanged. The proof retains the comparison, E2-to-Einfinity argument, finite
   filtration induction, and derived conservativity. Searched the shared Lean
   sources for page, limit, restriction, and filtered-isomorphism alternatives,
   and read SpectralSequencePageInduction and SpectralSequenceComparison. Their
   Mathlib spectral-sequence/colimit interfaces do not shorten the direct
   exact-couple argument here. Existing finite transport and image-factorization
   helpers are reused in place, as is ExactFunctorHalfPlane.transport_square
   at the identity functor. Every remaining public import supplies statement
   data; new imports are proof-only. No longer needed records all four removed
   imports and the sole removed old proof dependency lem-sp-page-induction.
   No whole-module withdrawal or targets-closure decrease is claimed.

5. **DAG agreement: PASS.** Compared the delivered node with the shared node.
   Only proof, proof_deps, and proof_origin change; the statement and Lean
   attachment stay unchanged. Checked every proof dependency's declaration.
   The proof_deps set is exactly the union of the five proof steps' uses.
   The new route records helper reuse, local page induction, separate global
   and degree-specific limiting data, finite image filtrations, and the final
   geometric-stalk criterion, matching the Lean proof. There are no new nodes.

Second-reading changes: appended this independent review and added scratch
axiom-audit copies only. No further Lean or DAG repair was needed. The retained
delivery proves the sole original hole, adds no holes, and splits off none.
