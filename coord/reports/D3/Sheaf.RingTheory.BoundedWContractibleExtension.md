## What changed

Proved `RingHom.exists_bounded_wContractible_extension` in
`Sheaf.RingTheory.BoundedWContractibleExtension`, preserving its signature, universes,
public imports, and existing docstring.

The proof constructs the strict w-local stage using the existing `StrictWCoverProperties`
and `StrictWCoverSize` theorems, applies `BoundedExtremallyDisconnectedCover` and
`ProfiniteComponentRingPullback`, transfers strictly henselian local rings, and invokes
`WContractibleGeometricCriterion`. It proves the cardinal estimate directly using the
injective diagonal into maximal localizations. It verifies the covering clause with
Mathlib's `Scheme.Hom.singleton_mem_propQCPrecoverage`.

Retained proof-only imports of those five statement modules and added Mathlib's
`RingTheory.Localization.Cardinality`. The second reader removed the redundant
`Mathlib.RingTheory.LocalProperties.Basic` import after checking compilation without it.
Updated the existing DAG node's proof, proof dependencies, and proof origin to match.
No new modules, definitions, statements, nodes, or interface changes.

Validation: the complete file compiles through `lcompile.py` in about three seconds with
no errors or warnings. The proof treats the zero ring without any nontriviality assumption;
the localization product may have an empty index set. The retraction clause retains arbitrary
`B : Type (max u v)` and follows from the universe-polymorphic geometric criterion.
The construction and counting argument follow
[Stacks 0983](https://stacks.math.columbia.edu/tag/0983) and
[Stacks 0984](https://stacks.math.columbia.edu/tag/0984).

## Proved and sorry left

Closed one hole: `RingHom.exists_bounded_wContractible_extension`
(node `lem-weil-pbc-wcontractible-ring-extension`).

No `sorry` remains in the item module. No holes added and none split off.
This is a complete proof from existing statements, not a decomposition.

The existing imported theorem obligations remain unchanged:

- `PrincipalWLocalization.StrictWCover.properties`
  (`lem-weil-pbc-strict-w-cover`).
- `PrincipalWLocalization.StrictWCover.cardinalMk_le`
  (`lem-weil-pbc-strict-w-cover-size`).
- `Algebra.exists_profinite_component_ring_pullback`
  (`lem-weil-pbc-profinite-component-ring-pullback`).
- `Profinite.exists_bounded_extremallyDisconnected_cover`
  (`lem-weil-pbc-bounded-extremally-disconnected-cover`).
- `RingHom.exists_retraction_of_wlocal_geometric_criterion`
  (`lem-weil-pbc-wcontractible-geometric-criterion`).

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.RingTheory.IndEtaleStability`: the existing library's
  `Algebra.IndEtale.trans` and weakly-etale instance suffice.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`: its needed API is already exposed by
  the retained imports.
- `Mathlib.AlgebraicGeometry.Pullbacks`: no tensor-product/pullback calculation is needed.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: the affine/quasi-compact instances are
  already available through the retained imports.
- `Sheaf.RingTheory.StrictWCover`: its construction remains available through the public
  imports of `StrictWCoverProperties` and `StrictWCoverSize`. The dependency node
  `def-weil-pbc-strict-w-cover` is still used and retained.

The second reading also removed the newly proposed proof import
`Mathlib.RingTheory.LocalProperties.Basic`: `eq_zero_of_localization` is already exposed
by the retained imports. A scratch compile without `Localization.Cardinality` failed at
`IsLocalization.cardinalMk_le`, confirming that the other new proof import is necessary.

Removed proof-dependency edges to `lem-weil-pbc-ind-etale-stability`,
`lem-weil-pbc-faithfully-flat-base-change`, and
`lem-weil-pbc-fibre-product-affine-spectra`.
The corresponding large Sheaf stability theorem and the latter two planned arguments are
not needed by this proof. Mathlib's singleton quasi-compact covering lemma replaces the
explicit base-change calculation. No claim is made that these nodes become globally
unreachable: other parents or the imported theorems may still use them.

The closed-point homeomorphism for the strict cover C is also unused: quotient
surjectivity bounds its component space directly by the power set of C.
The final D closed-point homeomorphism is still needed to count maximal localizations.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The planned affine-cover verification was longer than needed:
Mathlib already proves the singleton result for surjective quasi-compact morphisms satisfying
an arbitrary morphism property. Its use preserves the unit route. No target or intermediate
statement was changed.

## Second reading by D3

1. **Interfaces: pass.** Compared the delivered module against the repository with `diff`.
   The existing theorem signature, universe parameters, public imports, and docstring are
   byte for byte unchanged. Only its proof and private import list change; no definition,
   statement, module, or node is added, so no change record is required.
2. **Proof and axioms: pass.** Independently compiled the complete file using `lcompile.py`
   without errors or warnings. No `sorry` or forbidden declaration mechanism occurs in the
   delivered source. A scratch copy with
   `#print axioms RingHom.exists_bounded_wContractible_extension` reported exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; the latter remains in the
   five existing imported obligations listed above. The proof constructs no public data
   definition from an arbitrary unproved existence statement. The canonical local-ring
   maps transfer strict henselianity, and equality in every maximal localization proves
   injectivity of the diagonal map. All counts allow empty spectra and the zero ring;
   the retraction retains the original larger universe for B.
3. **Split statements and search: pass.** No statements were split off and no holes added.
   Independently searched LeanFinder for localization cardinality and the diagonal into
   maximal localizations, and searched `lean/Sheaf` and `lean/WeilConjectures` by concept.
   The relevant Mathlib cardinality and local equality lemmas are already used. Inspected
   upstream `exists_isWContractibleRing` and `exists_forall_exists_retraction`: neither
   supplies the required cardinal bound, and the latter only splits same-universe
   ind-etale extensions. No shorter replacement for the present proof was found.
4. **Route and pruning: pass after repair.** Read the five imported statement modules and
   Mathlib's singleton quasi-compact covering lemma. The strict-cover, profinite-cover,
   component-pullback and geometric-criterion route is preserved. The node is below the
   unit level and is not a replacement for any statement or step recorded in
   `dag/units/sk-thm-properbasechange.json` under `realized`. Every removed old proof
   dependency is listed in `No longer needed`; the strict-cover definition remains a
   dependency despite removal of its redundant direct import. Checked the two proposed
   Mathlib imports separately and removed the redundant local-properties import.
5. **DAG: pass.** Parsed both node versions: only `proof`, `proof_deps`, and `proof_origin`
   differ. Read all six new proof steps against the Lean proof; the union of their `uses`
   equals `proof_deps`, with precisely the three obsolete edges listed above removed.
   The node statement, Lean record, chapter, and unit are unchanged. No new-node fields
   or change records are needed.

Second-reading changes: removed one redundant proof import; corrected the report's claim
that the five already-present statement-module imports were newly added; documented the
previously omitted removal of the direct `StrictWCover` import; added this review.
