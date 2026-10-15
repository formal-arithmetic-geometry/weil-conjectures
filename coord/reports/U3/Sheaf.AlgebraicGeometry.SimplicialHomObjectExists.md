## What changed

Replaced the proof of
`AlgebraicGeometry.Scheme.exists_simplicial_hom_object` in
`lean/Sheaf/AlgebraicGeometry/SimplicialHomObjectExists.lean`.
The statement, visibility, imports and existing docstrings are unchanged.

The proof follows the existing node's three steps. Mathlib's
`SSet.hasDimensionLT_of_finite` supplies a degree bound. The existing
`SSet.simplicialIndex_finite_initial` gives finiteness of the bounded full
subcategory and the limit-existence comparison. Its `AsSmall` model is a finite
small category, so the existing `semiRepresentableHasFiniteLimits` instance
provides the restricted limit in every universe in the original signature.
The diagram is `CategoryOfElements.π S ⋙ K`. Its limit projections form the
universal family. A compatible family defines a cone explicitly; `limit.lift`,
`limit.lift_π` and `limit.hom_ext` prove existence, its equations and uniqueness.
No auxiliary declarations or interfaces were added.

Read the item node, its four dependency nodes and their Lean signatures, and
`dag/units/sk-prop-h2.json`; the unit's `realized` lists do not assign any unit
step to this node. The route is unchanged. The literature checkout does not
contain `literature/stacks-project/simplicial.tex` on this machine, so the source
was read at the official Stacks pages:
[017J](https://stacks.math.columbia.edu/tag/017J) and
[017K](https://stacks.math.columbia.edu/tag/017K).
The category-of-elements cone construction and finite restriction match those
proofs. The bounded category and the functor remain local constructions in the
proof; no arbitrary object is extracted from an unproved existence theorem.

Searches through `msearch.py` (LeanFinder, Loogle and grep) are recorded in
`searches.jsonl`; direct searches of both library roots found no existing theorem
with this universal property. LeanFinder found general simplicial functor
category limit instances, which do not supply this limit from finite limits.
Loogle reported an unknown unqualified identifier for `HasFiniteLimits`.
Mathlib's finite-limit and category-of-elements APIs give the required glue.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.exists_simplicial_hom_object`
(node `lem-weil-pbc-simplicial-hom-object-exists`).

No `sorry` remains in this module. No holes or modules were added. This is a
proof from the existing stated dependency, not a new decomposition.
`SSet.simplicialIndex_finite_initial` remains an existing upstream obligation
(node `lem-weil-pbc-simplicial-index-finite-initial`); its proof was not changed.

Local single-file compilation passed with no warnings in approximately five
seconds. The required delivery dry run supplies the final compile and axiom
probe. Import direction check passed.

## No longer needed

None. All three existing imports remain needed: the semi-representable category
and finite-limit instance, finite simplicial sets and their dimension bound,
and the finite-initial truncation theorem. No planned node or module was
bypassed, and no imports were added or removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The existing plan can be made into Lean
without new intermediate statements. The finite category has object universe
`t` and hom universe zero, so it requires the routine `AsSmall` equivalence
before applying Mathlib's `FinCategory` finite-limit instance; this does not
change the route or any statement.

## Second reading by U3

1. **Signatures and accidental changes — PASS.** I compared the delivered module with the repository version. The theorem signature, declaration visibility, imports, definitions, and docstrings are byte-for-byte unchanged; only the proof body is new.
2. **Proof and axioms — PASS.** The module compiles with the prescribed launcher without warnings and contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or `debug.skipKernelTC`. The axiom probe reports only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`, as expected from the still-open dependency `SSet.simplicialIndex_finite_initial`.
3. **Statements and split nodes — PASS.** No statements were split off and no nodes were added. The existing theorem is proved at exactly its recorded strength, with no hollow definition or arbitrary witness extracted from a mere existence theorem. Searches recorded in `searches.jsonl` found no stronger existing Mathlib or library theorem that would replace this proof.
4. **Route and pruning — PASS.** The proof uses the recorded finite simplicial-index theorem, semi-representable finite-limit instance, and simplicial finite-set infrastructure. The unit record `sk-prop-h2` has no realized step assigned to this node, and no import or proof dependency can be removed.
5. **DAG agreement — PASS.** The implementation follows the node's three proof steps: category-of-elements diagram, finite initial restriction, and finite-limit universal property. The node's `proof`, `proof_deps`, and `proof_origin` therefore remain consistent with the Lean proof.

I independently read the dependency's finite-object, finite-hom, and limit-comparison clauses and the finite-limit instance. The diagram's arrows go from an `n`-simplex to its image in degree `m`, so the cone equations have the required direction. For constant simplicial sets on one or two points, the construction gives respectively one copy or a product of the corresponding limits, with the stated universal property. The degree bound and bounded full subcategory also match the source argument in [Stacks 017J](https://stacks.math.columbia.edu/tag/017J) and [017K](https://stacks.math.columbia.edu/tag/017K), which I read independently.

I changed only this report by adding this second-reading record; no Lean source, DAG node, import, or declaration was otherwise changed.
