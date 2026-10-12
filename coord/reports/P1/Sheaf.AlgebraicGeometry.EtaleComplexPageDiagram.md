## What changed

Replaced the sorry in `AlgebraicGeometry.Etale.exists_etaleComplex_page_diagram`
with a complete Lean proof from the new `etale_page_map_coherence` theorem.
Constructed the coordinate-swap embedding, restriction homology isomorphism,
its naturality, and the swap functor with fully proved private helpers. Constructed
the unswapped diagram explicitly from T₀ and M, then applied the swap functor.
The first-page dictionaries and equations use the supplied presentation and hfirst;
negative-degree vanishing uses the presentation's negative field. All page
isomorphisms are identity isomorphisms after definitional coordinate swapping.
No data is selected from an unproved existence statement.

The sole new module is `Sheaf.AlgebraicGeometry.EtalePageMapCoherence`, which states
only the identity, composition and cocone equations for the explicit unswapped M maps.
Its statement is strictly part of the argument: it has no swapped sequences, first-page
dictionaries, vanishing assertions, or page comparison isomorphisms. Both new and
original signatures compile, and the original public theorem signature is unchanged.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.Etale.exists_etaleComplex_page_diagram`
(node `lem-weil-pbc-etale-complex-page-diagram`) by decomposition.
Added one hole: `AlgebraicGeometry.Etale.etale_page_map_coherence`
(node `lem-weil-pbc-etale-page-map-coherence`). There are no sorries in the item module,
no sorries in definitions or private helpers, and no other added holes. This is one
upper hole closed and one lower hole added, net zero; it is a decomposition, not a
complete axiom-free proof of the upper theorem.

Edge-case checks: r=1 swaps (1,0) with (0,1) correctly; negative first coordinate maps
to the original negative resolution degree. The embedding is defined for every integer
page r, with no exceptional zero vector. Identity and composition equations are pure
coherence statements and do not need any first-page assumptions; cocone compatibility
uses only hG and L.w. No uniform boundedness or limit/affineness hypothesis is added.

## No longer needed

Removed redundant direct public imports:
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`,
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`,
`Mathlib.Algebra.Homology.SpectralSequence.Basic`,
`Mathlib.Algebra.Category.Grp.Abelian`, and `Mathlib.Algebra.Category.Grp.Colimits`.
Their required declarations remain publicly available through
`Sheaf.Paper.EtaleTermwiseHypercohomology`; compilation verifies this.
Added only proof imports for restriction homology and the new coherence lemma.
No formerly stated proof-dependency nodes were removed (the original node had none).
No whole module is claimed to leave the targets' transitive import closure merely
because these redundant direct imports were removed. Pruned modules: none.
The import adaptation is recorded in
`coord/changes/EtaleComplexPageDiagram-imports.md`.

## Where the brief, the DAG or earlier work was wrong

The node's single elementary step concealed the inverse-image coherence glue and
coordinate-restriction homology naturality. Its updated proof separates that glue
from the fully implemented coordinate-swap construction. The blueprint unit record
`sk-prop-h2` has no realized statement or step for this helper, and its route is retained.
No statement is disputed, no public signature or definition is changed, and there
are no forced adaptations.

Search found no ready-made arbitrary spectral-sequence swap. Mathlib's
`restrictionHomologyIso`, cycle inclusion and homology projection naturality provide
the needed construction. LeanSearch returned Internal Server Error; LeanFinder and
local searches ran successfully and are recorded in searches.jsonl.

Attempts to finish the coherence theorem exposed expensive definitional comparisons
of identity-complex maps on etale sheaves and exceeded the single-file limit.
The delivery leaves that coherence argument as the named, sourced lower theorem;
its docstring specifies equality induction for scheme-map transports and the exact
identity, composition and cocone argument. The final delivered files compile with
no warnings. The attempted full-coherence proof is retained outside the delivered
Lean files in coherence-working.txt for the next worker's reference.

The required deliver3.py --no-push run failed before delivery validation with:
`ImportError: cannot import name refuse_missing from import_cycles`
(the module resolved to the repository tools/import_cycles.py). No tool was edited
and no git command was run manually. This is a launcher/repository tool mismatch.

## New nodes

`lem-weil-pbc-etale-page-map-coherence`: the explicit unswapped spectral-map laws,
in `Sheaf.AlgebraicGeometry.EtalePageMapCoherence`. Its source is Stacks Tags
015J, 015K and 0EZM, specifically the diagram-assembly step of the existing parent
proof. It depends on no new existence statement and introduces no construction.
No change records are needed.

## Earlier second reading (a previous round; superseded)

Pending independent reading: the item module compiles and the public theorem keeps
its original signature. The added coherence statement is a strict lower-level
factorization of the diagram and cocone equations, and the unit route is retained.


## Second reading by P1

1. **Statements and interfaces.** Compared the delivered page-diagram module with the repository copy. The public theorem signature is byte-for-byte unchanged; the coherence helper is a new, strictly lower-level theorem and its node records the exact Lean statement. No target or existing public declaration was weakened.

2. **Proof and axioms.** Compiled both delivered modules with `lcompile.py` after warming the sandbox build. The page-diagram file and coherence file compile without errors or warnings. The page-diagram theorem has no `sorry`; the only remaining `sorry` is the named coherence theorem, and no definition contains `sorry`. The split theorem is documented with its source and a complete proof plan.

3. **Truth and strength of split statement.** Checked identity, composition, and cocone equations against the supplied `hid`, `hcomp`, `hidentity`, `hcomposition`, `hG`, cone equation, and cocone equation. The helper asserts exactly those three map equalities and introduces no page, swap, first-page, vanishing, or stabilization claim. Small edge cases (identity arrow and a one-object diagram) reduce to the stated equations.

4. **Pruning and imports.** The coordinate-swap construction uses `restrictionHomologyIso` and its naturality; the retained public termwise-hypercohomology import supplies the page API. Removed direct public imports are redundant and are recorded in `coord/changes/EtaleComplexPageDiagram-imports.md`; no proof-dependency node used by the new proof was dropped. The unit route and `sk-prop-h2` realization are retained.

5. **DAG agreement and delivery hygiene.** The parent node proof steps and `proof_deps` match the Lean proof, and the new coherence node points to its module and declaration. No statement change, forced adaptation, hollow definition, forbidden declaration, or accidental extra module remains. The only change made during this reading was this section of the report and removal of a temporary helper file.
