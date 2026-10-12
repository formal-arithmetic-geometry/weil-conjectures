## What changed

Repaired reviewer X-09b43 D1. Replaced the returned clause split by the full geometric
proof in `lean/Sheaf/AlgebraicGeometry/EtaleAffineCoverStratification.lean`.
The original signature and all original public imports are preserved. Restored the
four original proof imports and added the proof-only import
`WeilConjectures.Mathlib.AlgebraicGeometry.Restrict` for section-restriction compatibility.

The proof stratifies the finite family of all overlaps by the separated case, including
charts as diagonal overlaps. A finite-family induction takes actual fibre-product common
refinements, and pullback pasting transports finiteness along the projection morphisms.
Affine refinement applies the existing affine-piece theorem and proves the disjointness
and coverage of its flattened sigma family. Pullback restriction isomorphisms then give
an affine cover of each base change. Each overlap inclusion is proper over a separated
chart, hence closed; its section restriction is surjective. The canonical tensor map is
surjective because every overlap section is the image of `x tensor 1`. Finally the existing
affine-cover criterion gives separatedness. No mathematical obligation is relocated.

Updated the item's `proof`, `proof_deps` and `proof_origin` to this implemented route;
the `lean` record still has the unchanged declaration and signature.
Updated `coord/changes/etale-affine-cover-stratification-imports.md`.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_etale_affine_cover_stratification`
(node `lem-weil-pbc-etale-affine-cover-gluing`): 1 of 1 original holes closed.
Added zero holes and split off zero statements. There is no `sorry` in the delivered module.

Six private helpers are proved completely: `finite_snd_comp`, `common_finite_strata`,
`affine_refine_strata`, `chart_pullback_finite`, `closed_overlap_tensor`, and
`separated_of_finite_charts`. These implement portions of the existing node's seven
steps and introduce no public statements or definitions.

Removed both holes added by the rejected delivery:
`AlgebraicGeometry.exists_etale_affine_cover_partition`
(`new-etale-affine-cover-partition`) and
`AlgebraicGeometry.separated_of_etale_affine_cover_data`
(`new-etale-affine-cover-separated`). Their modules and node files are absent from
this repaired sandbox. This is a proof from existing declarations, not a decomposition.

Local compilation passes without errors or warnings. The finite-family induction treats
the empty family by the identity stratum. The open-cover criterion also handles an empty
cover, which forces the covered scheme empty; self-overlaps supply charts via `inf_idem`.
All constructions retain universe `u` and permit empty strata and empty piece families.

## No longer needed

Removed the returned proof imports and deleted their rejected modules and nodes:

- `Sheaf.AlgebraicGeometry.EtaleAffineCoverPartition`,
  `new-etale-affine-cover-partition`.
- `Sheaf.AlgebraicGeometry.EtaleAffineCoverSeparated`,
  `new-etale-affine-cover-separated`.

No original library import is removed: all four original proof imports are used.
The edge `lem-weil-pbc-separated-cancellation` is no longer needed: the overlap morphism
is directly expressed as an open immersion into an affine chart followed by its affine
structure morphism, and Mathlib composition instances prove separatedness. No other
original proof dependency is claimed pruned; the remaining geometric nodes are used.
Whether other targets still reach a removed dependency is for the global closure ledger.

## Where the brief, the DAG or earlier work was wrong

D1 is repaired: the previous delivery moved the first five conjuncts to one sorry theorem
and the final conjunct to another. This repair deletes both restatements and implements
the requested geometric route, including real factorization morphisms from fibre products,
the finite affine refinement, and the closed-overlap surjection argument.

No statement correction, definition change, target change or new node was required.

## Second reading by T1

1. **Interface preservation — pass.** Compared the delivered module with the repository
   using `diff`; also checked the existing theorem signature byte for byte with Python.
   The signature and original docstring are unchanged. There are no changed definitions
   or public declarations. The six added helpers are private proved theorems. All four
   original public imports occur in the statement's vocabulary; the additional restriction
   compatibility import is proof-only. The change record accurately describes the imports.
2. **Proof and compilation — pass.** Independently compiled the delivered module with
   `lcompile.py --all`, without errors or warnings. A scratch copy printed the axioms of
   all six private helpers and the public theorem: only `propext`, `Classical.choice`,
   `Quot.sound`, and (for the common-stratification helper, affine refinement, and final
   theorem) `sorryAx` from existing open upstream obligations occur. The other four helpers
   use only the three permitted standard axioms. No delivered declaration contains `sorry`,
   and the forbidden-declaration scan is empty. Thus this closes the item's local hole;
   it does not claim that all upstream obligations have been closed.
3. **Split statements and edge cases — pass.** No new sorry statements, modules or nodes
   are delivered. Read each private helper and the original imported theorem statements.
   The induction's zero-family case uses the identity stratum; diagonal overlaps recover
   charts without assuming distinct indices. The sigma-family flattening allows empty
   pieces and empty strata. For an empty chart cover, the cover hypothesis forces the
   source empty and the affine-cover criterion remains applicable. The overlap inclusion
   is genuinely proper over a separated chart, and the tensor surjection uses the actual
   restriction map, with preimages `x tensor 1`.
4. **Route and pruning — pass.** Rechecked the proof from the target through separated
   stratification, actual fibre-product common refinements, affine refinement, and the
   closed-overlap affine-cover criterion. Read the implementation of
   `Scheme.Stratification.inter`. Independent Lean Finder search for finite constructible
   partitions of etale chart/overlap families and `rg` searches of the library found no
   existing combined theorem to replace this argument; Loogle confirmed the exact
   separated-target hypothesis of `IsProper.of_comp`. Each original proof import is used.
   Compared the old and new dependency lists: their only removed node is
   `lem-weil-pbc-separated-cancellation`, already listed above. Read the unit
   `dag/units/sk-thm-p1.json`: this below-unit argument bypasses none of its realized steps.
5. **DAG agreement — pass with citation repair.** The seven proof steps describe the
   actual Lean helper calls and constructions, and `proof_deps` is exactly the union of
   their `uses`. The original node statement, Lean signature record and unit are unchanged.
   The updated origin identifies the implemented route. Corrected the stale `03S9` tags
   in the proof-step source records to `03S0`, consistent with the node's existing
   `lead_note` and main source citation.

Second reading changed only the proof-step citation tags and this review report; no
Lean repair was needed. Holes closed: `AlgebraicGeometry.exists_etale_affine_cover_stratification`.
Holes added: none. Split off: none.
