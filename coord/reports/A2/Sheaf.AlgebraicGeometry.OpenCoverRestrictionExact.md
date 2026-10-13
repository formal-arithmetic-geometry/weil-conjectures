## What changed

Proved `AlgebraicGeometry.exactAt_over_of_open_cover` in
`Sheaf.AlgebraicGeometry.OpenCoverRestrictionExact`, preserving its signature and visibility.
Added the proof-only import `Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing`.
The proved private helper `AlgebraicGeometry.isZero_over_of_open_cover` shows vanishing
on the union by applying sheaf separation to the intersections of each open with the cover.
The main proof uses `ShortComplex.LeftHomologyData.exact_map_iff` and the existing exact
restriction instances to apply that helper to the left homology object of `K.sc n`.
Updated the node's proof and proof_origin to describe this route.

## Proved and sorry left

Closed: `AlgebraicGeometry.exactAt_over_of_open_cover`
(node `lem-r4-open-cover-restriction-exact`), the item's only original hole.
Added holes: none. Remaining holes in the delivered module: none.
The private vanishing helper is proved. This is a proof, not a decomposition.
Single-file compilation succeeded with no warnings. The delivery dry run also checks
all declarations with the project's axiom probe.

## No longer needed

Removed imports: none. Pruned proof-dependency nodes and modules: none.
All original public imports remain necessary for the statement or its restriction
instances. No stalk comparison or stalkwise exactness module needs to be added.
The existing unit route is preserved; this node is not itself a realized unit statement
or proof step (`sk-thm-picard-duality.realized` contains no entries).

## Where the brief, the DAG or earlier work was wrong

The statement is correct, including the empty-cover case. The planned stalk argument
is unnecessary: vanishing of homology and the uniqueness part of the sheaf axiom give
a complete proof with the available interfaces. Restriction preserves left homology
through the already proved additive/finite-limit/finite-colimit instances in
`Sheaf.Paper.DerivedHomMayerVietoris`; no surjectivity of global sections is asserted.
The union proof uses only that an open mapping into U is covered by its intersections
with V_i, so it also works for arbitrary index universes and empty schemes.

## Second reading by A2

1. Compared the delivered module with the repository using `diff`. The only changes
   are a private proved helper, the main proof body, and a plain proof-only import.
   Independently compared the full existing theorem signature byte for byte: identical.
   Its universes, arbitrary index type, union equality, degree and local exactness
   hypothesis are all preserved. No definition, visibility or public import changed.
   Read [Stacks Tag 01AG](https://stacks.math.columbia.edu/tag/01AG): its stalkwise
   criterion implies precisely this local exactness assertion, without a finiteness
   hypothesis on the cover. Verdict: pass.
2. Compiled the module through `lcompile.py`, with no errors or warnings. Compiled
   a scratch copy with `#print axioms` for both the private helper and
   `AlgebraicGeometry.exactAt_over_of_open_cover`: both use only `propext`,
   `Classical.choice`, and `Quot.sound`. There is no remaining `sorry`, prohibited
   declaration, hollow definition or choice of arbitrary data. Verdict: pass.
3. No statement was split off and no new public declaration or hole was added.
   Read the private helper: evaluation of each zero restriction makes the sections
   on W intersect V_i subsingleton; sheaf separation identifies any section with
   zero. The cover proof uses W contained in U and hU, with no nonempty-index
   assumption. Empty covers, empty opens and the zero sheaf cause no exception.
   Verdict: pass; no split-off nodes to search or repair.
4. Checked Mathlib `LeftHomologyData.exact_map_iff` and `eq_of_locally_eq'` against
   their actual statements, and the proved restriction additivity and finite-limit
   and finite-colimit instances in `DerivedHomMayerVietoris`. The mapped short
   complex agrees definitionally with the restriction of K at degree n. Searched
   with msearch grep for zero restrictions and local exactness, and rg in both Lean
   roots for local vanishing and exactness. The existing Scheme.Modules cover-zero
   lemma uses scheme restriction rather than the over-site functor and only covers
   the whole scheme; the coherent-formal-modules result has a different category.
   Neither shortens this direct over-site proof. Each import supplies statement
   types, definitions/instances, or sheaf separation. Both old proof dependencies
   remain; none was pruned. Read sk-thm-picard-duality.realized: its statement and
   step entries are empty, and this auxiliary node realizes neither. Verdict: pass.
5. Compared both node JSON records: only proof and proof_origin changed. Read all
   three new proof steps against the Lean helper and main theorem; they accurately
   describe preservation of homology, separation on intersections, and the final
   application. proof_deps still contains the two original definition nodes, and
   the statement and Lean signature record are unchanged. No new node is needed
   for an unfinished statement. Verdict: pass.

Second reading changed only this report; the proof, imports and node need no repair.
