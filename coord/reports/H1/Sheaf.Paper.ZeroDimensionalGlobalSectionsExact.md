## What changed

Proved AlgebraicGeometry.zero_dimensional_global_sections_preservesFiniteColimits in
Sheaf.Paper.ZeroDimensionalGlobalSectionsExact without changing its signature or public imports.
The proof uses the existing canonical degree-zero product-of-germs comparison from
Sheaf.Paper.ZeroDimensionalEtaleCohomologyIso. After removing its two invertible derived
comparison factors, it constructs a natural isomorphism from global sections to the finite
product of geometric stalk functors. Stalks preserve epimorphisms; finite products of their
maps do too. Global sections already preserve kernels, so Mathlib's homology preservation
lemmas finish the finite-colimit argument. Mathlib proves the finite discrete geometry directly.

Added proof-only imports Mathlib.AlgebraicGeometry.AlgClosed.Basic,
Mathlib.AlgebraicGeometry.Artinian,
WeilConjectures.Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products, and
Sheaf.Paper.ZeroDimensionalEtaleCohomologyIso. Updated the node's proof, proof_deps, and
proof_origin to match. No new modules or nodes are delivered.

## Proved and sorry left

Proved AlgebraicGeometry.zero_dimensional_global_sections_preservesFiniteColimits
(node zero-dimensional-global-sections-exact), closing the item's only sorry.
No sorry remains in the delivered module; no new sorry is added.
The existing imported theorem AlgebraicGeometry.zero_dimensional_etale_cohomology_iso
(node zero-dimensional-etale-cohomology-iso) remains sorry in the repository and becomes
the geometric comparison dependency. This is a reduction from an existing strictly
geometric canonical isomorphism to exactness, not a claim of axiom-free target closure.

## No longer needed

No original imports were removed. The trial imports Mathlib.AlgebraicGeometry.Noetherian
and Mathlib.Algebra.Homology.ShortComplex.ExactFunctor were redundant and omitted.
No node or module is globally pruned: all original geometry and strictly henselian
comparison dependencies remain needed through zero-dimensional-etale-cohomology-iso.
The direct proof dependencies on lem-weil-pbc-reduction-universal-homeomorphism,
lem-weil-pbc-finite-discrete-scheme-affine, lem-weil-pbc-scheme-coproduct-family,
thm-weil-pbc-universal-homeomorphism-invariance, and
lem-weil-pbc-strictly-henselian-sections-stalk are replaced by that existing comparison
node; their modules are not imported directly here. The finite-type/dimension-zero,
closed-point residue-field, and geometric-stalk exactness Mathlib nodes remain directly
used. The two provisional intermediate modules in the scratch work are unnecessary and
were removed from the delivery.

## Where the brief, the DAG or earlier work was wrong

The node plan is mathematically sound. Some dependencies have mathlib_match rather than
lean records, so the absence of a lean record is not an obstacle. The existing
ZeroDimensionalEtaleCohomologyIso theorem provides the required canonical comparison:
its proof does not import this module, and import_direction.py confirms the import has
no cycle. Its invertibility is not sufficient alone: the delivered proof supplies the
naturality and finite-product epimorphism argument explicitly. Neither separatedness nor
any other binder was changed, and no additional hypothesis is assumed.

The geometry and comparison handle the empty scheme (empty product), a single point,
and nonreduced schemes. Arbitrary sheaves of abelian groups are retained. The finite
product is indexed by the actual points of C in Type u, so no universe is changed.

## Second reading by H1

1. **Unchanged interface — pass.** Compared the sole delivered Lean module with the
   repository using diff. The existing declaration's signature and docstring are
   byte-for-byte unchanged; all five public imports are unchanged. The only added
   imports are the four proof-only imports listed above. No definitions, statements,
   change records, or new nodes are added.
2. **Proof — pass, conditional on the existing comparison.** Independently compiled
   the delivered file with lcompile.py: exit 0, no warnings. Scanned the delivery for
   sorry and prohibited declarations: none. A scratch copy with #print axioms for
   zero_dimensional_global_sections_preservesFiniteColimits compiled and reported
   exactly propext, Classical.choice, Quot.sound, and sorryAx. The latter is expected
   from the existing, explicitly reported zero_dimensional_etale_cohomology_iso;
   this delivery closes the local sorry, not the transitive axiom-free closure.
   Checked cancellation of the two comparison isomorphisms, projectionwise naturality
   of the germ map, the finite-product epimorphism lemma, and the conversion from
   epimorphism and kernel preservation to finite-colimit preservation.
3. **Split-off statements — pass (none).** No new split-off statement is delivered.
   The imported degree-zero comparison is an existing geometric statement, strictly
   different from finite-colimit preservation; the proof supplies its naturality and
   exactness consequences. Traversed its transitive DAG proof dependencies (154 nodes):
   no path returns to this exactness node. Empty C, one point, nonreduced C, and
   arbitrary abelian sheaves require no extra hypothesis in this reduction.
4. **Route and pruning — pass.** Independently searched for an exact-global-sections
   epimorphism theorem using Loogle (no hits) and searched lean/Sheaf and
   lean/WeilConjectures. Read the analogous finite-direct-image exactness proof and
   the proved piObj_map and epi_piObj_map declarations. The finite-direct-image result
   is not itself a theorem about Γ, and does not supply a shorter direct application.
   Each added import supplies declarations used by this proof. The No longer needed
   section lists every old proof dependency replaced by the comparison node; none is
   globally pruned because the comparison still needs them. The sk-prop-cd unit's
   realized fields are empty; no recorded unit realization is bypassed, and its
   finite-point acyclicity route is retained through the geometric comparison.
5. **DAG agreement — pass.** Compared the node JSONs: only proof, proof_deps, and
   proof_origin differ. Their three steps describe precisely the geometry instances,
   natural product-of-germs isomorphism, and finite-product exactness argument in Lean.
   The listed Mathlib geometry and stalk nodes and the comparison node match those
   uses; the node's statement and lean record are unchanged.

Second reading changed only this report: added the independent review and explicit
axiom/dependency audit. No Lean or node repair was necessary.
