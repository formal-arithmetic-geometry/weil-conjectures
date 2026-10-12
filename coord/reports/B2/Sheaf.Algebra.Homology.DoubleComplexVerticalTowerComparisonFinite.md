## What changed

Replaced the sole sorry in `Sheaf.Algebra.Homology.DoubleComplexVerticalTowerComparisonFinite`.
The theorem's signature and public imports are unchanged. All added imports are proof imports.
Private, proved helpers construct the cutoff natural transformation from the canonical truncation
inclusions. Monicity identifies its extended total map with the existing tower map.

The proof forms the canonical cokernel short exact sequence, totalizes it, uses Mathlib's
`CochainComplex.mappingCone.quasiIso_descShortComplex`, then composes homology isomorphisms.
For the map from the total quotient to the total window, it uses a cone filtration and the existing
`CategoryTheory.degreewiseFiltered_acyclic`, rather than leaving total comparison as a new sorry.
No definition chooses data from an unproved existence theorem: the existential comparison and
filtration are eliminated only inside the theorem proof.

Added three statement modules, each with its own node. `FirstQuadrantExtendedTotalExact` is fully
proved using finite discrete colimit exactness and degreewise detection. The other two modules
state the two remaining construction steps. Updated the item's proof and proof dependencies.

Validation: all four delivered modules compile together without errors or warnings using
`lcompile.py --all`. The original theorem has no interface or statement diff.
`#print axioms HomologicalComplex₂.shortExact_extended_total` returned exactly
`propext`, `Classical.choice`, and `Quot.sound`. The delivery dry run printed OK (the second reading
is pending); nothing was pushed.

## Proved and sorry left

Closed the hole in `HomologicalComplex₂.verticalTower_interval_homology_iso_finite`
(node `lem-sp-double-complex-vertical-tower-comparison-finite`). This is a decomposition, not a
complete axiom-free proof: one item hole closed, two lower holes added.

Fully proved `HomologicalComplex₂.shortExact_extended_total`
(node `lem-sp-first-quadrant-extended-total-exact`), including its private helper
`HomologicalComplex₂.shortExact_total_aux`. Its proof uses only Mathlib and the already-proved
nonnegative totalization sign instance.

Every sorry left in the delivery:

- `HomologicalComplex₂.firstQuadrant_vertical_cone_filtration`
  (`lem-sp-first-quadrant-vertical-cone-filtration`, module
  `Sheaf.Algebra.Homology.FirstQuadrantVerticalConeFiltration`). This constructs a finite filtration
  and graded-column-cone comparisons for an arbitrary bicomplex map, with no quasi-isomorphism
  hypothesis. It does not assert a total comparison.
- `HomologicalComplex₂.verticalCutoff_cokernel_column_comparison`
  (`lem-sp-vertical-cutoff-quotient-comparison`, module
  `Sheaf.Algebra.Homology.VerticalCutoffQuotientComparison`). This concerns only the bicomplex
  cokernel and its vertical columns, with no totalization or homology-of-total conclusion.

There are no remaining sorries in the item's module and no sorries inside definitions or private
helpers. Existing imported theorems may themselves depend on sorries; they are not newly added
holes of this delivery.

## No longer needed

No original imports, nodes, or modules were pruned. The second reading removed the redundant
added proof import `Mathlib.Algebra.Homology.Embedding.ExtendHomology`; its extension
quasi-isomorphism instance is already available through the retained imports. The original cutoff-tower and smart-window
interfaces remain needed. The route through totalization commuting with columnwise cones is
replaced by the proved exactness of totalization and Mathlib's cone-to-cokernel comparison.

`Sheaf.Algebra.Homology.FirstQuadrantTotalComparison` is not imported: it reaches this item through
`WeilConjectures.Mathlib.Algebra.Homology.TotalComplex`, so importing it would create a cycle.
Its comparison theorem is not duplicated as a new sorry. Instead the delivery uses the existing
finite filtered acyclicity theorem and leaves the independent cone-filtration construction.
No shared module is claimed to become unreachable as a result.

## Where the brief, the DAG or earlier work was wrong

The item's original single "elementary" proof step hid both the natural window comparison and
finite-diagonal totalization theory. The delivered reduction separates these constructions and
fully proves totalization exactness.

The source checkout here does not populate the blueprint document named by the node.
WANTED: the blueprint file at the node's source path, proof steps 1 and 2, for the two construction
nodes. I read the published [Stacks section 012X](https://stacks.math.columbia.edu/tag/012X) and
[tag 0133](https://stacks.math.columbia.edu/tag/0133). Tag 0133 is the augmentation lemma, not a
literal theorem on arbitrary columnwise quasi-isomorphisms; the cone-filtration refinement is
marked as an agent proof and explicitly describes its signs. The natural smart-truncation
argument is the agent refinement of the existing node's plan, supported by Mathlib's
complementary-truncation API, not a claim that 012X states it verbatim.

Edge cases checked mathematically: equal endpoints give a zero quotient and window; negative
endpoints and a=0 do not remove one nonzero half of the comparison's contractible kernel.
The cone filtration keeps the column-cone degree -1 term. At total degrees below -1 the entire
cone is zero, so the filtration bounds still hold even when n+2<=0. Zero complexes and empty
diagonals are included. No target statement, definition, or other group's module was adapted.

`blueprint_refs.py ancestor` returned None for this item, whose `created.item` is a module name.
The new-node ancestry was therefore read from the existing comparison node's blueprint record:
`thm-sp-double-complex-spectral-sequences`, via the finite comparison, comparison, and vertical
spectral-object nodes. The unit's realized statement and steps are untouched.

LeanSearch returned HTTP 500 for all relevant queries; those records say unavailable, not no
match. LeanFinder and source grep were run and their real records copied into each new node.

## New nodes

`lem-sp-first-quadrant-extended-total-exact`:
`lean/Sheaf/Algebra/Homology/FirstQuadrantExtendedTotalExact.lean`, declaration
`HomologicalComplex₂.shortExact_extended_total`. Fully proved generic exactness of finite-diagonal
totalization followed by extension by zero. It also covers negative degrees by zero objects.

`lem-sp-first-quadrant-vertical-cone-filtration`:
`lean/Sheaf/Algebra/Homology/FirstQuadrantVerticalConeFiltration.lean`, declaration
`HomologicalComplex₂.firstQuadrant_vertical_cone_filtration`. Builds only the filtration and its
graded comparisons. Its proof sketch gives the source and target sign scalars explicitly.

`lem-sp-vertical-cutoff-quotient-comparison`:
`lean/Sheaf/Algebra/Homology/VerticalCutoffQuotientComparison.lean`, declaration
`HomologicalComplex₂.verticalCutoff_cokernel_column_comparison`. A column-level truncation
comparison; its remaining kernel is a two-term image complex with isomorphism differential.

No change records are needed: all existing signatures, definitions, visibility, and public
imports are unchanged. No forced adaptations.

## Second reading by B2

1. **Interfaces: pass.** Compared every delivered module with the repository. Only the
   item existed there; its declaration signature, surrounding variables, visibility,
   original docstring, and both public imports are byte for byte unchanged. Its added
   declarations are private, proved construction helpers. The other three modules are new.
   The existing node changes only `proof`, `proof_deps`, and `proof_origin`. No change record
   or forced adaptation is required.
2. **Proof and axioms: pass as a decomposition.** Independently compiled all four modules
   using `lcompile.py --all`, without errors or warnings. Scratch copies with `#print axioms`
   show exactly `propext`, `Classical.choice`, and `Quot.sound` for
   `HomologicalComplex₂.shortExact_extended_total`; the item and the two named open
   construction lemmas additionally use `sorryAx`. The only two textual holes are the
   reported public named theorems. No forbidden declaration or hollow definition occurs.
   The cutoff lift is constructed using the inverse of an actual isomorphism. The quotient
   map and filtration witnesses are eliminated inside a proposition proof, never chosen
   as public data. One original hole is closed and two lower holes are added; no complete
   axiom-free proof of the original item is claimed.
3. **Split statements: pass.** Read both statements, docstrings, and nodes. The quotient
   comparison is confined to individual vertical columns; the filtration lemma applies to
   arbitrary maps, without a quasi-isomorphism premise. Neither restates the item's total
   homology conclusion. Checked equal endpoints, `b<=0`, `a<0`, `a=0`, adjacent endpoints,
   zero complexes, the cone's degree -1 source term, and degrees below -1. The two-term
   image kernel and the graded-cone sign rescaling give valid mathematical arguments.
   Independent LeanFinder searches used new wording for both statements, and Mathlib
   source grep found the complementary-truncation comparison but no exact duplicate.
   Also searched `lean/Sheaf` and `lean/WeilConjectures`: the Cartan--Eilenberg cone lemma
   concerns a special augmentation with additional hypotheses, not an arbitrary map.
4. **Route and pruning: pass after one import removal.** Read the proof from its target
   down through the canonical cokernel sequence, proved totalization exactness, Mathlib
   cone comparison, column quotient map, cone filtration, and existing filtered acyclicity.
   Checked the actual import path from `FirstQuadrantTotalComparison` through
   `WeilConjectures.Mathlib.Algebra.Homology.TotalComplex`, the vertical spectral object,
   and tower comparison back to this item: using it here would create a cycle. The upstream
   `BicomplexColumns` comparison requires integer complexes bounded above in both indices,
   so does not directly replace this first-quadrant construction. Tested removal of each
   added proof import, sequentially; only `Mathlib.Algebra.Homology.Embedding.ExtendHomology`
   was redundant, and removed it. Both original proof dependencies remain in the proof;
   no old node or module is pruned. Read `dag/units/sk-prop-av-pqf-finite.json`: its statement,
   steps, and `realized` fields are untouched; this reduction bypasses no realized unit node.
5. **DAG: pass.** Checked all four node records against the Lean statements, construction
   steps, and actual dependency use. Each new node has its source, search records, complete
   proof sketch, origin, creation record, blueprint ancestry, chapter/unit, and verbatim
   normalized Lean signature. The original node's dependency list contains both original
   dependencies and the four new proof inputs, matching the proof. No old dependency is
   omitted from `## No longer needed`.

Changes by the second reader: removed the redundant extension-homology proof import;
corrected the new cone-filtration docstring's vanishing claim to degrees below -1 and
explicitly retained the possible degree -1 source summand; expanded the pruning report
and recorded this independent review. No theorem statement or proof body was changed.
The remaining construction holes require substantial formalization, rather than a
few-minute application of a matching existing theorem.
