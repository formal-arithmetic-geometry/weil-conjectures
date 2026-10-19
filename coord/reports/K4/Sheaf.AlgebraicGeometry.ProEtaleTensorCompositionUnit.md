## What changed

Proved `AlgebraicGeometry.Scheme.proEtale_tensor_composition_unit` in
`Sheaf.AlgebraicGeometry.ProEtaleTensorCompositionUnit`, retaining its exact signature
and both existing generator/scalar definitions. Eight proved private helpers express
linearity and restriction compatibility of the module unit and compatibility of the
coefficient maps with composition, indexing-arrow cancellation, and sectionwise
inverse-isomorphism cancellation, the composite-unit formula, and injectivity of the
adjunction transpose. The eighth helper packages the generic mate and its unit equation.
The coefficient identity constructs the actual
restriction comparison on direct images. Its adjunction mate satisfies the composite-unit
equation. Linearity and naturality prove the forward generator formula; its specialization
at intermediate scalar 1 and cancellation prove the inverse formula. Injectivity of the
adjunction Hom equivalence proves uniqueness among all natural transformations.

The existing node's proof, proof dependencies and proof origin now describe this route.
Obsolete top-level tool-use approvals for the three unused dependencies were removed.
No statements, definitions, public imports, instances or visibility were changed.
Preflight conservatively classifies the explicitly local irreducibility commands as an
interface change; their scope and every transitive consumer are documented in
`coord/changes/K4-proetale-tensor-composition-local-attributes.md`.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.proEtale_tensor_composition_unit`
(node `lem-sf-proetale-tensor-composition-unit`).
Added zero holes; zero holes remain in the item. No results were split off.
All eight new private helpers have complete proofs. The retained item compiled cleanly
against the current published build through `lcompile.py` in 10.3 seconds on resumption.
The required resumed dry run stopped at the missing change record; this delivery adds it.
The generic proved helper `mate_iso` constructs the comparison and proves its unit
equation before specializing to the concrete module adjunctions. This avoids unfolding
their concrete constructions while elaborating the equation. Generic helpers likewise
handle inverse cancellation, composite units and transpose injectivity. No heartbeat
or wall-clock limits were raised. The existing definitions and theorem signature are
unchanged; local irreducibility attributes affect only this file's proofs.
The proof caches the three existing commutative-ring sheafification instances as local
facts, avoiding repeated expensive instance synthesis without changing their values.
All three unchanged direct importers compiled against the candidate in an isolated
scratchpad: `FrobeniusTrivializationPullback` (8.1 s), `AmbientProperOpenPasting` (13.7 s),
and `GraphFrobeniusOpenExchange` (25.3 s). The candidate in that compile took 22.9 s.
A textual comparison verifies that the full theorem signature and both definition
bodies are identical to current sources; every delivered Lean line is at most 100 columns.

## No longer needed

Removed proof imports:
- `WeilConjectures.CategoryTheory.SiteMorphismComposition`;
- `Sheaf.CategoryTheory.SiteInverseImageTensor`;
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`;
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`;
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage` (already provided by public imports).

The proof no longer uses nodes `lem-weil-pbc-site-morphism-composition`,
`lem-weil-pbc-left-exact-site-inverse-image-tensor`, or `def-pur-sheaf-tensor-product`.
The generic site-composition theorem concerns set/abelian inverse images; the actual
ring comparison in the hypothesis is already defined by adjunction mates in
`ProfiniteCoefficientInverseImage`. Its defining mate equation suffices directly.
Since the local generators are defined by the normalized module units, linearity and
naturality give the tensor formulas without separately rebuilding the tensor comparison.
Thus the two tensor modules and their cochain monoidal machinery are unnecessary here.
The module inverse-image construction and fibre-product, composite-adjunction and
mate/unit-equation dependencies remain used. The item's unit record has no realized
statement or proof step for this auxiliary node; no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The saved attempt timed out against the current compiled sources. Caching sheafification
instances inside the theorem repaired the compile performance. Earlier iterations of the
direct-image comparison also needed the final `SheafOfModules.pushforwardComp` to identify direct image along the
composite site functor with successive direct images. This was repaired, together with
restricted scalar actions and the inverse generator formula.

The planned independent construction on relative tensor products is longer than necessary
for the existing exact statement. Constructing the adjunction mate and then proving both
specified generator formulas supplies the same explicit comparison and all five clauses.
No mathematical statement was disputed or weakened. No new nodes or consumer adaptations.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
