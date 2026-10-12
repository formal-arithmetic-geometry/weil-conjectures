## What changed

Replaced the single sorry in `Sheaf.AlgebraicGeometry.EtaleFilteredInjectiveAcyclic`
with a complete Lean proof from the Čech criterion, injective Čech acyclicity and
one new structural comparison theorem, proved entirely from Mathlib. The original theorem signature and public
import are unchanged. Retained the proof-only imports for sections, the Čech
criterion and injective Čech acyclicity; added proof-only imports for the source
geometry results and the new finite Čech comparison. Removed the unused direct
import of `Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings`.
The integer-module equivalence is already provided by the source geometry import. Reused the source library's proved finite affine refinement
and qcqs finite-product lemmas via `WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit`.

The proof constructs the qcqs basis and its finite coverings, verifies all three
geometric hypotheses, transfers the module sections result through lifted integer
coefficients, obtains a zero diagram of positive Čech homology, applies the criterion,
and explicitly transports derived evaluation to derived global sections.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.isZero_rightDerived_globalSections_colimit_of_injective`
(node `lem-weil-pbc-etale-filtered-injective-acyclic`) from named dependencies.
Its module contains no sorry. The private `abelianSectionsColimit` helper is proved.

Also proved `AlgebraicGeometry.Scheme.preservesColimitsOfShape_finiteEtaleCechHomology`
(node `lem-weil-pbc-finite-etale-cech-filtered-colimit`) entirely from Mathlib.
Its three private helpers are proved: `shortComplexHomologyColimit`,
`complexHomologyColimit`, and `finiteEtaleCechComplexColimit`.
Neither delivered module contains a sorry; no sorry is split off or added.

The sections and injective Čech acyclicity declarations imported from existing
modules still contain their own sorries. The Čech criterion is already proved in
the current repository, although its dependency closure still contains sorries.
They are unchanged by this delivery. Thus the original target declaration is closed
from named dependencies, rather than claiming that its entire axiom closure is closed.

## No longer needed

Removed the proof-only import
`Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings`. Its node
`lem-weil-pbc-etale-qcqs-cofinal-finite-coverings` is no longer a direct proof
dependency: the proof uses the proved source-library refinement theorem. It is
still reached indirectly through the sections theorem, so it is not globally pruned.
The target no longer directly uses `def-weil-pbc-cech-complex` or
`lem-weil-pbc-filtered-colimit-abelian-groups-exact`; the new structural comparison
node uses both, so neither is globally pruned.

No original geometric branch is pruned: finite affine refinements, affine qcqsness,
qcqs permanence and étale composition remain needed through the reused source
geometry proofs. `Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings` need not be
imported by this proof: the source library's already proved refinement handles an
arbitrary object of the ambient étale site directly. No other planned module is
made unnecessary. The unit's statement and realized steps are not bypassed.

## Where the brief, the DAG or earlier work was wrong

The current repository module imports its planned stated dependencies. The recorded finite
refinement interface is over the terminal object in the object's own small étale
site; the Čech criterion asks for coverings of arbitrary objects in the ambient
small étale site. The proved source-library
`exists_finite_affine_of_mem_smallEtaleTopology` supplies exactly this interface.
The recorded qcqs permanence facts also have a proved assembled source-library
interface, `compactSpace_and_quasiSeparatedSpace_piObj`.

The DAG's statement-level ingredients do not themselves state a Čech-colimit
comparison. This delivery states and proves that comparison. The proof identifies
the degree-q functor with a finite product of sections via `Pi.isoLimit`; the
product preserves colimits through `HasBiproductsOfShape.colimIsoLim`. For homology,
it uncarries an arbitrary diagram of short complexes into a short complex of
functors, applies the exact colimit functor, and uses `mapHomologyIso` and
`homologyMap_mapNatTrans` to identify the actual cocone legs. Degreewise evaluation
then gives the complex homology result. No injectivity is assumed in this comparison. Searches: LeanFinder and grep found only ingredients; LeanSearch returned
Internal Server Error and is recorded as unavailable. Blueprint Čech search found
no duplicate of this structural statement. The correct Tag 0739 source label is
`lemma-colim-works-over-collection`, whose final paragraph was read from the local
Stacks source copy. The new lemma was checked for empty finite families (all
positive-length tuple types are empty, so the complexes are zero), singleton
families, degree zero and arbitrary small filtered categories; no cover is needed.

## New nodes

`lem-weil-pbc-finite-etale-cech-filtered-colimit` is stated in
`lean/Sheaf/AlgebraicGeometry/FiniteEtaleCechFilteredColimit.lean`. It isolates the
finite-products/complex/homology comparison in step 2 of the item's plan, strictly
below the final acyclicity statement. Its theorem is fully proved from Mathlib,
so it introduces no new proof item. Its source is Tag 0739's final paragraph,
and its blueprint ancestor is `lem-weil-pbc-cohomology-filtered-colimit`, paragraph
2 (the Čech comparison), through the current acyclicity item. No change records
are needed because no existing statement, definition or public import changed.

Validation: both delivered module files compile cleanly with `lcompile.py --all`.
The second reader runs the final dry run and delivers after it passes.


## Second reading by R2

1. **Existing interfaces: pass.** Compared the delivered acyclicity module with the
   repository using `diff`, and separately compared its theorem signature as raw
   text: byte-for-byte identical through `:= by`. No existing definition or public
   import changes. The second module and its sole public theorem are new; its node
   records its exact multiline signature. No change record is required.
2. **Proof and trust: pass.** Read both modules in full and compiled the set cleanly
   with `lcompile.py --all`. Neither file has a sorry or forbidden declaration.
   Scratch copies with `#print axioms` checked both public theorems and all four
   private helpers. The new comparison theorem and its three helpers have only
   `propext`, `Classical.choice`, and `Quot.sound`. The sections-transfer helper and
   the acyclicity theorem additionally have `sorryAx` from existing dependencies;
   no nonstandard axiom occurs. In particular the comparison constructs actual
   colimit cocones and checks their legs, not merely abstract object isomorphisms.
3. **New statements: pass.** No statement is left split off with sorry. The new
   comparison is a strict structural part of step 2, independent of injectivity or
   coverings. Read Stacks `sites-cohomology.tex`, label
   `lemma-colim-works-over-collection`, final paragraph (local source copy
   `/tmp/stacks-project2/sites-cohomology.tex`, lines 2604–2626). Finite products
   commute with colimits in abelian groups because they are finite coproducts;
   filtered exactness then commutes with homology, including degree zero. Empty
   families have empty positive-length tuple types and zero complexes; singleton
   families reduce to sections; `p = 0` uses kernels, with no positivity assumption.
   The proof treats arbitrary small filtered categories, including the terminal
   category. Ran fresh LeanFinder and grep searches for homology commuting with
   exact filtered colimits, and searched `lean/Sheaf` and `lean/WeilConjectures`.
   Results give the exact-colimit ingredients, not this Čech preservation theorem.
   The source-library cofan theorem handles coproducts, not the filtered diagram
   required here. The docstring and node state the complete comparison argument.
4. **Route and pruning: pass after record repair.** Read the imported sections,
   injective Čech acyclicity, and criterion statements. The proof supplies the
   criterion's cofinality on arbitrary ambient étale objects, uses module sections
   via the lifted-integer equivalence, and transports derived evaluation to global
   sections with inverse derived natural transformations. No shorter matching
   theorem was found. `dag/units/sk-prop-h2.json` has empty realized arrays, and
   neither that unit's Kummer route nor its ancestor route changes. The old direct
   Čech-complex and exact-colimit dependencies move into the proved comparison;
   all geometry ingredients remain in the source proofs. The cofinal-coverings
   node is only indirectly needed through sections and was removed from this
   item's direct dependencies. No module is globally pruned.
5. **DAG agreement: pass after repair.** Checked each proof step against the Lean,
   checked that `proof_deps` is the union of `uses`, and checked the new node's
   source, statement dependencies, proof origin, searches, created record,
   blueprint ancestor, unit, chapter, and Lean record. Removed the unused direct
   cofinal-coverings node from step 1 and `proof_deps`; that step already names
   the proved source-library refinement that the Lean actually applies. The
   affine, qcqs-permanence and étale-composition Mathlib leaves describe the
   instances and source geometry proofs actually used.

Second-reading changes: replaced the new module's unnecessarily broad public
`Mathlib.AlgebraicGeometry.Sites.AffineEtale` import with
`Mathlib.AlgebraicGeometry.Sites.Etale` (both files still compile); removed the
unused direct cofinal-coverings DAG edge; corrected stale report claims about
original imports, the criterion's proof status, and pruning. The public
short-complex imports were checked and retained: they provide the homology
functor and its homology instances used in the public signature. No theorem
statement, definition, or proof body was changed.
