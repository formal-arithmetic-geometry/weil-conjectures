## What changed

Proved `AlgebraicGeometry.ProEtale.exactAt_cechComplex_comparisonUpperStar_of_injective`
in `Sheaf.AlgebraicGeometry.AffineComparisonInjectiveVanishingAux`, with its exact
original signature and visibility. The existing theorem
`AlgebraicGeometry.ProEtale.exists_etale_cech_cocycle_lift` supplies the geometric
two-stage descent for arbitrary coefficients. Apply
`CategoryTheory.injective_sheaf_cech_acyclic` on the original etale site, convert
vanishing homology into a primitive using Mathlib's exactness equivalences, and
map that primitive back using the chain-map equation. This handles empty covers
and empty schemes without adding a nonemptiness hypothesis.

Added the proof-only import
`Sheaf.AlgebraicGeometry.AffineComparisonCechCocycleDescent`, kept the proof-only
injective-sheaf Cech theorem import, and removed the ten unnecessary direct
imports listed below. Public imports are unchanged. Updated only `proof`,
`proof_deps`, and `proof_origin` in the existing node
`lem-cbc-abelian-affine-comparison-vanishing-aux` to describe this actual proof.
No definition, statement, other module, target, or public interface changed.

Validation: the single-file `lcompile.py` compile passes cleanly (2.0 seconds).
Both proof imports pass `tools/import_direction.py may`. LeanFinder found no direct
comparison-acyclicity theorem; Loogle and grep found the Mathlib equivalence
`HomologicalComplex.exactAt_iff_isZero_homology`, used in the proof. The source
Tag 099U proof was read in `literature/stacks-project/proetale.tex`.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.ProEtale.exactAt_cechComplex_comparisonUpperStar_of_injective`
(node `lem-cbc-abelian-affine-comparison-vanishing-aux`).

Holes added: 0. Split-offs: 0. Sorries left in the item module: 0. This is a proof
from existing declarations, not a new decomposition. The geometric descent and
injective Cech acyclicity declarations already have complete Lean proofs in the
shared source; no new assumptions or unproved witnesses are introduced here.

## No longer needed

Removed these ten direct proof imports, which are also absent from the delivered
module's transitive source import closure:

- `Sheaf.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes`
  (`lem-weil-pbc-etale-cohomology-limit-of-schemes`).
- `Sheaf.RingTheory.IndEtaleStability` (`lem-weil-pbc-ind-etale-stability`).
- `Sheaf.CategoryTheory.ExistsDirectedReindexing`
  (`lem-weil-pbc-filtered-category-directed-cofinal`).
- `Sheaf.AlgebraicGeometry.FibreProductLimit` (`lem-kun-fibre-product-limits`).
- `Sheaf.AlgebraicGeometry.LimitAffineTransition`
  (`lem-weil-pbc-limit-affine-transition`,
  `lem-weil-pbc-limit-affine-transition-core`,
  `lem-weil-pbc-limit-affine-transition-affine-comparison`).
- `Sheaf.AlgebraicGeometry.AffineEtaleSiteColimitStatement`
  (`lem-weil-pbc-affine-etale-site-colimit`).
- `Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections`
  (`lem-cbc-comparison-pullback-sections`).
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`
  (`def-weil-pbc-site-comparison-morphism`).
- `Sheaf.CategoryTheory.SiteCoveringAxioms` (`def-weil-pbc-sites-and-cohomology`).
- `Sheaf.RingTheory.IndPrincipalZariski` (`def-weil-pbc-ind-etale-algebra`).

These nodes are unnecessary for this proof through their former direct route;
other targets or modules may still use them. The equivalent geometric work is
encapsulated by the existing cocycle-descent theorem and its own dependencies.

Also removed these redundant direct proof imports, retained transitively:

- `WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`
  (`def-weil-pbc-ind-etale-basis`, `lem-weil-pbc-ind-etale-basis`).
- `WeilConjectures.CategoryTheory.SiteCechComplex`
  (`def-weil-pbc-site-cech-complex`, still recorded as a proof dependency).
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
  (the original direct proof dependency `lem-weil-pbc-etale-base-change-continuous`
  is unnecessary here; inverse-image APIs in this module remain used transitively).

Additional former direct proof dependencies no longer called by this proof:
`lem-weil-pbc-affine-scheme-qcqs`,
`lem-weil-pbc-filtered-colimit-abelian-groups-exact`,
`lem-weil-pbc-etale-composition-cancellation`, and
`lem-weil-pbc-etale-base-change-finite-limits`.
No unit statement or unit proof step was bypassed: `sk-prop-sf-comparison` has
empty `realized.statement` and `realized.steps` lists, and the same Tag 099U
geometric-descent / etale-injective-acyclicity route is preserved.

## Where the brief, the DAG or earlier work was wrong

The assigned module and its proof-dependency imports still described the original
large geometric argument. The shared library now already proves its geometric
part in `AffineComparisonCechCocycleDescent`; using that theorem avoids repeating
that work and introducing further holes. The original mathematical statement is
unchanged and no false lemma was needed. The old return for a different group's
delivery concerned an unnecessary adaptation of `HomComparison`; this delivery
contains no adapted modules.

## Second reading by C3

1. **Signatures and accidental changes — pass.** I diffed the delivered module
   and node against the shared repository. The theorem statement, declaration
   name, universes, hypotheses, conclusion, visibility, and all public imports
   are byte-for-byte unchanged. The only module changes are the proof and
   proof-only imports; the node changes only `proof`, `proof_deps`, and
   `proof_origin`.

2. **Proof and axioms — pass.** `lcompile.py` compiles the module cleanly in
   2.0 seconds. The module has no `sorry`, `axiom`, `unsafe`, `opaque`,
   `extern`, or `implemented_by`. A scratch `#print axioms` reports only
   `propext`, `Classical.choice`, and `Quot.sound` for the proved theorem.

3. **Split statements and mathematical strength — pass.** No statements were
   split off and no new nodes were added. The proof uses the existing cocycle
   descent theorem, injective étale Čech acyclicity, and the standard homology
   exactness equivalences. The cocycle-to-coboundary transport is exactly the
   original conclusion, including empty covers; no hypothesis was added and no
   conclusion weakened.

4. **Shortest route and pruning — pass.** The proof follows the existing
   affine cocycle descent route, then lifts a primitive on the fixed étale site
   and transports it through the chain map. The ten obsolete direct imports and
   their unused proof dependencies are removed as listed above. The unit route
   is preserved: `sk-prop-sf-comparison` has no realized statement or steps to
   bypass.

5. **DAG agreement — pass.** The node's three proof fields match the Lean proof:
   the descent and injective Čech nodes are the only substantive dependencies,
   with the Čech-complex definition retained. The recorded source remains Tag
   099U, and the report's hole counts match the module: one original hole
   closed, zero holes added, zero sorries left.

I changed only this report section and corrected the import count from thirteen
to ten; no Lean code or node content was changed during second reading.
