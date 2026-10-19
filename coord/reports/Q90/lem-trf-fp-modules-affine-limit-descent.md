# Worker report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-fp-modules-affine-limit-descent.json`: repaired nine-step statement split; no new non-Mathlib nodes.
- `dag/nodes/sec-trace-formula/lem-trf-affine-open-limit-descent.json`: retained the Mathlib leaf `AlgebraicGeometry.exists_isAffineOpen_preimage_eq`.
- `citations.json`: regenerated verbatim citations for every node used by every repaired step.

Attachments: none. WANTED: none.

The item statement is unchanged. No exact finished declaration exists in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`. I reused the existing affine-open Mathlib leaf and the existing module-map and fpqc-descent nodes. The stale `created.item` field on the item, which pointed to another item, was removed; the retained affine-open leaf already has `created.item` equal to this item.

## Returned issue repaired

The return identified C4/E3 and D5: the earlier split asserted transition isomorphisms without descending inverse maps or proving the two inverse identities, and its chart and map arguments were too long. I divided the proof into chart descent (Step 1), incidence and covering stabilization (Step 2), local finite-presentation module/map descent (Step 3), inverse-map descent and identity equations (Step 4), pair-overlap compatibility (Step 5), triple cocycle and identity equations (Step 6), effective fpqc gluing (Step 7), morphism lifting (Step 8), and equality detection (Step 9).

In Step 4, each canonical pair comparison is known to be an isomorphism on the limit. I explicitly descend its inverse with the map clause of `lem-pc-fp-module-map-descent-affine`, then use that node's equality clause on both composites with the inverse and the identities. Thus every stage comparison is an isomorphism before it is used as fpqc transition data. Steps 5 and 6 then force overlap agreement and the cocycle at one common later stage using the finite refinement and triple-chart covers established in Step 2. No step exceeds 2000 characters.

## Review by Q90

I reread `literature/stacks-project/limits.tex`, Tag 01ZR, including the affine module argument and its Zariski-gluing route, and checked all three item clauses against that statement. I also reread the retained Mathlib declaration for affine-open descent and the statements of every cited DAG node; `citations.json` copies those statements verbatim.

Step 1 uses the affine-open Mathlib leaf for each chosen affine chart and `lem-weil-pbc-limit-cone-affine-projections-opens` for restricted affine-transition limit systems. Step 2 uses `pqf-lem-limit-qc-open-descends` for eventual equality of quasi-compact opens and `lem-weil-pbc-limit-global-sections-colimit` for every chart ring. I checked that quasi-separatedness makes the finite intersections quasi-compact and directedness supplies one common stage for the finite list, so the covers and incidences hold on the actual stage opens.

Step 3 uses `lem-weil-pbc-quasi-coherent-finite-type-affine` for finite-presentation section modules, `lem-weil-pbc-module-pullback-affine-sections-bijective` and `lem-weil-pbc-affine-tilde-gamma-adjunction` for the restriction/tensor comparisons, the global-sections colimit node for the ring systems, and `lem-pc-fp-module-map-descent-affine` for descending local modules and maps. Step 4 uses the same module-map node twice: first to descend the inverse of each canonical comparison, then to force both composites to be identities after a later enlargement. This directly repairs the returned omission.

Step 5 applies the equality clause of the module-map node on every pair-chart overlap refinement; because Step 2 makes those refinements cover the full intersection, the maps and their inverses glue there. Step 6 applies the same equality clause to both composite-versus-transition and identity equations on the explicitly refined triple charts; the resulting equations hold on full triple intersections. Step 7 uses `lem-pc-fpqc-descent` only after these isomorphism, overlap, and cocycle checks, and invokes its preservation/reflection clause for finite presentation. Steps 8 and 9 use the module-map node's map/equality clauses on the finite cover and `lem-pc-fpqc-descent` for global gluing and faithfulness.

I checked the hypotheses at each use: all stage schemes are qcqs, transitions are affine, the index is directed, all local modules are finitely presented, and every later enlargement is chosen above the finite list already constructed. Edge cases (singleton systems, identity transitions, one affine chart, and empty pair/triple intersections) reduce by deleting empty finite families. The item statement and its dependencies remain unchanged apart from removing the stale provenance field; the repair adds only the missing inverse and cocycle arguments.
