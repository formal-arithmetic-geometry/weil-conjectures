## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-maximal-point-blowup-generated-cohomology.json`: item, statement, split into five proof steps. Mathlib verdict: no match after semantic, Loogle and source searches, including a second semantic phrasing.
- No new nodes and no new Mathlib leaves.
- `citations.json`: one verbatim statement quote for every step/node citation.
- `searches.jsonl`: actual logged searches from msearch.py. The item's earlier NU searches are retained verbatim; all Q132 searches are appended to the item.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the blueprint tag, blowup cohomology, regular-local blowups and global generation. The existing globally generated invertible-sheaf declarations concern ample sections, not H1 on this point blowup. No exact finished project declaration was found.

## WANTED

None. All mathematical sources used are in the local Stacks source.

## Corrections and scope

The item was statement-only and remains exactly the same statement. Stacks 0AGS(3) proves the larger alternative that F or F(1) is globally generated; this item asks only the F case. I do not add the F(1) clause. The proof remains on the quadratic-transformation route of 0AGS. It writes out the two-chart calculation instead of introducing additional nodes for all twists, Serre vanishing, sums of cohomology and the long exact sequence. This is a node-level proof choice, not a change to a unit or chapter.

The ancestry command returns `blueprint.from.node = None`. The inherited created.item chain is broken before a blueprint node, although its detailed from.place and via chain name the ctf-stability direct-image prerequisite. I retained that null ancestor and chain, filled same_as by searching the whole imported blueprint, and explained the latest blueprint proof (3) connection in split_report. No unrelated node was edited to manufacture ancestry. Read the latest blueprint's six-functors-basics chapter, ctf-stability unit and direct-image proof, along with the stored chapter and unit records. The current and stored unit records differ, but this local prerequisite is not the unit's key node and requires no realized-field change.

## Not duplicates

No new nodes. Searched the whole DAG for 0AGS, cohomology-of-blowup, affine covers, and global generation, and searched the imported blueprint using `blueprint_refs.py search` for blowup, globally generated, and cohomology of blowup. Reused the existing point-blowup local chart package, affine tilde tools and Cech theorem. The related `lem-per-regular-point-blowup-acyclic` states R1 b_* O=0, not the arbitrary globally generated sheaf assertion; it is not used as a surrogate for that assertion. The existing binary direct-sum quasi-coherence node states only TWO summands; I deliberately do not cite it for the possibly infinite evaluation coproduct.

## Review by Q132

I read resolve.tex Tag 0AGS (lemma-cohomology-of-blowup), especially the first paragraph and the globally generated paragraph of clause (3), with 0AGQ's chart explanation. I also read coherent.tex Tag 01XD's full statement and proof and schemes.tex Tags 01IB, 01IC and 01ID, which explain the affine coefficient calculation. This is an agent-written explicit calculation supported by these sources; proof_origin says agent. There are no new nodes whose sources require separate checking.

For step 1 I opened `lem-sfb-point-blowup-local-chart-package` and checked its actual hypotheses, rather than citing its proof: it is for a regular scheme of dimension at most two and gives affine charts and the BASIC-OPEN description of their overlap. `lem-weil-pbc-regular-local-localization` explicitly says a regular local ring is a regular ring, and `def-weil-regular-scheme` then makes Spec A regular. `lem-weil-pbc-spec-topological-krull-dimension-ring` identifies its topological dimension with 2. The chart package is therefore applicable to Spec A. Its potentially smaller affine neighbourhood of the closed point must be all of Spec A (a principal open through the closed point is defined by a unit); A localized at its maximal ideal is A for the same reason. Thus its Z really is this Y. The package itself supplies the global/affine blowup comparison and nonzero parameters, so neither comparison is silently inferred from a definition.

For step 2 I checked `def-nagata-blowup-chart-ring`: its generators are exactly x/s for x in m. Writing x=as+bt proves C_s=A[t/s], and similarly for C_t. `lem-weil-pbc-spec-module-tilde-sections` explicitly gives basic-open sections by localization. Applied to the structure module and the package's basic-open W, this gives C_s[(t/s)^(-1)]. Every element is a polynomial divided by a power of t/s, hence a finite Laurent expression; separating exponents is an elementary argument, not a hidden geometric lemma. Relations among Laurent expressions do not cause a problem because existence, not uniqueness, is required.

For step 3 I opened `lem-weil-pbc-module-restriction-open-immersion-colimits`, which states preservation of ALL small colimits as well as restriction of quasi-coherence. `lem-weil-pbc-affine-tilde-gamma-adjunction` states preservation of all small colimits by tilde and the isomorphism on sections, and `lem-weil-pbc-spec-module-tilde-sections` states that tilde is quasi-coherent. Their combination identifies an arbitrary restricted free sheaf with the tilde of the actual free module, with its canonical coprojections. It is not an assumption that a sheaf coproduct has sectionwise values on arbitrary opens: the identification is only on affine opens, after the cited tilde result. Restriction preserves the evaluation epimorphism because an epimorphism is the cokernel of its kernel and restriction preserves that colimit. All generator sets are sets in a universe containing the sections; no unindexed proper-class colimit is used.

For step 4 I opened the full `lem-weil-pbc-quasi-coherent-module-cokernel-image` statement. Clause (3) explicitly identifies the sections of the image sheaf on an affine open with the sectionwise image of the map. Both its input sheaves are quasi-coherent by step 3, and W is affine by step 1. Since the restricted evaluation map is epi, its image sheaf is F|W; this is precisely why every section on W has a FINITE expression in the global generators. Each coefficient is decomposed using step 2. I checked the sign: u is the negative sum of the C_s coefficients and v the positive sum of C_t coefficients, so v-u equals w. Global generators have the same restrictions from both charts, which justifies the multiplication identity. No finite-type or coherence hypothesis on F is used or added.

For step 5 I opened `lem-pc-cech-computes`: it applies to any scheme with an affine cover ALL of whose finite repeated intersections are affine, and says exactly that its Cech cohomology equals sheaf cohomology for quasi-coherent modules. Here those intersections are U, V and W. I read `def-weil-pbc-site-cech-complex` for its alternating differential and kernel/image cohomology definition. The cocycle calculation is written for the full ordered-pair complex, so no unquoted normalization or alternating-complex equivalence is needed: triple indices force the diagonal entries zero and the reverse entry to be the negative. The onto difference map from step 4 then supplies a boundary with every component correct. This gives the full H1 conclusion, not only structure-sheaf cohomology.

All off-unit citations are generic affine algebra/sheaf tools, recorded in split_report.tool_uses with their purpose; no replacement of the ctf-stability unit route is asserted. No SGA source is cited. Each of the five steps is below 2000 characters (882, 668, 728, 667, 579 when written). I checked B--E: no new restatement leaf or elementary node, no unsplit proof sketch masquerading as a statement, no uncited twist vanishing or cohomology-of-sums theorem, and every quote is copied from the cited statement. No statement dispute was found.

Small cases checked: F=0 gives the zero expression; F=O is the Laurent coefficient decomposition itself; an arbitrarily large free direct sum still has finite support for each overlap section; a quotient with torsion coefficients uses no division on F; no assumption on the residue field or on A being complete/excellent is needed. Dimension zero and one are excluded by the item's dimension-two hypothesis; the package's other cases are not used. An open W cannot require a third chart: it is the basic open already given by the package. These checks specifically rule out replacing arbitrary global generation by finite global generation or accidentally proving only a proper-coherent special case.

## Unfinished work

None at the natural-language split level. No Lean was written or compiled. Delivery validation is recorded by the required remote dry run and final push.
