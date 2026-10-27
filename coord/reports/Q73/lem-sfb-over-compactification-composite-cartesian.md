# Q73 — lem-sfb-over-compactification-composite-cartesian

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-over-compactification-composite-cartesian.json`: existing statement item, now split in nine steps. Mathlib searches found no statement of the whole item. No new nodes and no new Mathlib leaves.
- `citations.json`: one entry for each of the 31 step/node citations, quoting the complete verbatim statement of the cited existing node.
- `report.md`: this report. `searches.jsonl` is the unedited search-command log.

## Attachments

None. The live project source `lean/WeilConjectures/Compactification/Refinement.lean` has `AlgebraicGeometry.Compactification.exists_isPullback_overG_overI` at line 136 with its entire proof `sorry` at line 140. Its docstring (lines 131–135) supplies the intended closure argument. The sorry-free definition `AlgebraicGeometry.Compactification.overComp` at line 77 assembles a supplied third compactification; it does not construct the required cartesian one and is not an attachment for the whole item. No attachment is claimed. The previous rejection of nonexistent declarations is respected.

## WANTED

None. All sources used are available locally. The existence theorem is Stacks Tag 0F41 (`flat.tex`, `theorem-nagata`); the closure factorization is Tag 01RG (`morphisms.tex`, `lemma-quasi-compact-immersion`). The other source passages are specified below and in each step.

## Corrections and source comparison

The statement is retained, including its arbitrary-compactification closure construction and the composite consequence. Its JSON text had literal doubled TeX backslashes; these were normalized to single TeX backslashes without changing its meaning. There is no STATEMENT-DISPUTED assertion: the statement is true with its supplied hypotheses.

The imported `sk-def-sfb-dc-setting` dependency imposes a field/characteristic/coefficient setting that this general qcqs-base geometric lemma does not use. It was removed and replaced by the actual general-base definitions: schemes over a base, finite type, proper/separated maps, quasi-separatedness, fibre products, and scheme-theoretic closure. The compactification definition was retained. I checked the actual Lean signature and docstring rather than the absent declarations named in the previous proposed attachment. The Lean theorem assumes only qc and separatedness for the structure map of T; the DAG additionally assumes locally finite type for T. This delivery preserves the existing DAG statement. Its proof uses T finite type in the middle-over-base lemma for c'; a future Lean proof of the more general signature can instead obtain the required relative finiteness over Y and the qcqs target directly. The DAG's cartesian and composite clauses are both established here; no claim is made that the node exactly captures the weaker Lean hypotheses.

The blueprint source `main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-comp-composition/_section.md` states the lower-shriek composition clause. The geometric tower is the one in the live Refinement.lean docstring. The item's recorded ancestor is an import-closure bookkeeping ancestor in the affine-space induction unit; I retained that ancestor and clarified `from.place`, rather than changing any unit or chapter route. The split is an agent expansion of that docstring, explicitly marked `proof_origin.by = agent`, using existing source-backed geometric tools. The chapter and unit records were read and are untouched.

## Searches and reuse

Read the current live item and searched the project source for its id, `exists_isPullback_overG_overI`, `overComp`, and compactification notions. Read Refinement.lean and the relevant middle-over-base definitions in Over.lean. The cartesian-existence theorem remains sorry; only the assembly clause is already defined.

Ran the authorized msearch command for two LeanFinder phrasings (proper morphism over an open, and Nagata over a qcqs base), Loogle patterns `AlgebraicGeometry.Compactification, CategoryTheory.IsPullback` and `"compactif"`, LeanSearch for the proper-over-open compactification, and grep `Compactification|compactification` in AlgebraicGeometry. The exact queries, returned names and verdicts were appended to the item's inherited searches and remain in searches.jsonl. Loogle reported an unknown Compactification identifier for the first pattern, and no substring matches for the second; Mathlib grep found no scheme compactification declarations. Semantic hits concerned liftCoborder/open lifts, normalization, properness restriction, and quasi-compactness. None states this compactification existence result or supplies it by one-line specialization. No outage was converted into an absence result.

Before contemplating new nodes I searched the whole DAG by closure, proper/open/dense, separatedness, finite-type, compactification and Stacks tags, and ran blueprint_refs.py searches for `compactification`, `scheme-theoretic closure`, `proper open`, `proper dense open`, `cartesian compactification`, `composite`, and `compactification of`. I read the actual statements of the 21 proof dependencies. All necessary facts were already represented; no new nodes are warranted. The elementary restriction of an injective sheaf map, the open-subscheme pullback identification, and composition of open immersions are written as arguments within the item.

## Not duplicates

No new nodes. The existing `lem-weil-pbc-compatible-compactification-triangle` constructs a compatible tower by replacing the intermediate compactification of f; it does not promise to preserve the prescribed proper map p in this item. The existing `det-nagata-refinement-common-dense` and `lem-nagata-dense-refinement-cartesian` compare compactifications of one fixed map; they do not state the proper/open tower here. They were read but not invoked for a conclusion their statements do not provide. `lemma-nagata-proper-open-dense-iso`, `lemma-nagata-immersion-open-in-scheme-image`, and the generic cancellation/permanence nodes are reused directly. The imported blueprint has no other node equivalent to the entire item, so `same_as` remains empty.

## Review by Q73

I read the live Refinement.lean statement and its closure docstring, the current composition-unit statement, the recorded affine-space unit and chapter, Stacks 0F41 and 0A9Z in flat.tex, 01R8/01RG/01W3/01W4/01W5/01W6 in morphisms.tex, the separatedness permanence/cancellation passages 01KU/01KV in schemes.tex, and the current blueprint's proper-open-dense statement and proof. There are no new nodes needing separate source reviews.

Step 1 uses finite type = locally finite type plus quasi-compact from `def-weil-finite-type-morphism`, the actual two triangles from `def-weil-compactifications-refinements`, and the proper/separated definition. I verified that `lemma-nagata-finite-type-to-separated-target` really includes clause (b), not merely local-finite-type cancellation. The source structures on X,Y,T are finite type and the intermediate maps p,q are separated, exactly its hypotheses. This proves that the supplied open maps i,j are qc and allows the `sk-def-nagata-sketch-data` convention without silently assuming more of the supplied compactifications.

Step 2 uses `lem-sfb-compactification-middle-over-base` only for its stated S-structure, separated finite type and absolute quasi-compactness conclusions. Its assumptions on the two base structures Y and T and on qc open maps are supplied by the item and step 1. It does not state absolute quasi-separatedness, so I did not take that from it: the proof explicitly uses the closed diagonal, closed-immersion properness, finite-type definition, the definition of quasi-separatedness and clause (2) of `lem-weil-pbc-qcqs-morphism-permanence` to obtain quasi-separatedness of Z'. All the statements used say precisely those facts, and the qcqs hypothesis on S is retained.

Step 3 applies separated cancellation to a_Z = a_Z' h, finite-type cancellation to the same triangle, and `sk-thm-nagata-compactification` only after verifying Z' qcqs. The theorem's statement gives a dense compactification and therefore the initial compactification needed here. Its proof is not being mined for an extra construction. The stronger density conclusion is not assumed for an arbitrary later compactification.

Step 4 uses the schematic closure definition for the closed image object, `lemma-nagata-immersion-open-in-scheme-image` for a qc open factor with schematic density, and `lem-weil-pbc-closed-immersion-proper` clause (b) for properness of the new structure map. The factor a is qc even under the supplied open/proper compactification convention, by the finite-type cancellation statement and properness of b. The immersion definition includes an open immersion by taking the identity closed factor; it is not an unproved stability assertion. All closure hypotheses are checked. This proves the closure construction for any initial compactification, rather than just choosing an already dense one.

Step 5 is elementary from the actual fibre-product universal property in `def-pc-fibre-product` and the open-subscheme and sheaf identification in `def-weil-open-immersion`. I wrote the factorization and its uniqueness and explained why r is the open immersion onto the same open image. This avoids the invalid inference that a set-theoretic image inclusion generally gives factorization through an arbitrary closed subscheme.

Step 6 invokes `lem-weil-pbc-proper-base-change` with p' and j, then uses `lemma-nagata-proper-to-separated-target` with the triangle Z -> V -> Y. The composite is the original proper p and the second arrow is proper, hence separated by its definition. The cited proper-to-separated statement has no finite-type-base or Noetherian restriction. It says that the first arrow is proper, exactly what is used.

Step 7 is an elementary restriction argument using the statement of `def-nagata-scheme-theoretically-dense-open`. The maps on every open A in V are written out, and equal the maps on that same open in W. Properness from step 6 supplies qc for r if using the qc-open formulation of the density definition. No assertion about arbitrary base change of schematic density is used; only restriction to an open is used.

Step 8 applies the exact statement of `lemma-nagata-proper-open-dense-iso`: r is proper and open, and its own image is the dense open it contains. Every assumption was proved before the application. The resulting isomorphism is the particular map r=(i',p), so its two projections certify the cartesian square via `def-pc-fibre-product`, rather than just an unrelated isomorphism of schemes. The source proof explains that proper makes the open image closed and density removes its complement; there is no reducedness assumption.

Step 9 uses `lem-weil-pbc-proper-composition` for qp', and gives the argument for composition of the two open immersions directly from their definitions, including the structure sheaf. The displayed compactification equality is expanded and all S-structures agree by construction. It proves the additional composite clause, which by itself would not have proved the cartesian existence clause.

For B1–B10 there are no new nodes; definitions and references needed by the item are explicit, TeX is normalized, searches are actual logged calls, and no attachment is invented. For C1–C8 I checked every uses-list against the cited statement and supplied citations.json with literal quotes; uses-union equals proof_deps. Three non-Mathlib generic tool uses are declared in split_report with reasons for maintainer review, and no top-level tool_uses field is written. For D1–D5 no item clause has been repackaged as a new lemma: the closure, properness, density restriction, cartesian identification and composition arguments are in the steps themselves. For E1–E7 I checked the hypotheses, source objects, sheaf maps and scheme structures at each application. No step exceeds 2000 characters.

Small cases checked: if Z is empty, its schematic closure and the inverse-image V are empty, so the criterion still applies. If j is the identity, the argument forces W = Z over Y. If p is the identity, W can be the closure of Y in Z' and its inverse image of Y is Y. Extra components in an arbitrary initial E are discarded by schematic closure. Nonreduced schemes are allowed throughout: no equality of closed subschemes is inferred merely from equality of point sets, and density is the structure-sheaf injection. The general qcqs base is never replaced by a Noetherian or field hypothesis. No SGA source is used.

## Unfinished work

None for this stage-1 item. This is a split, not a Lean proof: the existing underlying theorem is still sorried in the read-only library. No Lean was written, no compiler/Lake/build tool was run, and the repository and launcher were not edited. Server checks and delivery status are recorded after they complete.
