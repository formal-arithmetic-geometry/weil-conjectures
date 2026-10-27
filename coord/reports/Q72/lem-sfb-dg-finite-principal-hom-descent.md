# Stage-1 report: lem-sfb-dg-finite-principal-hom-descent

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-dg-finite-principal-hom-descent.json: statement item, split into nine proof steps using existing nodes; not a Mathlib leaf.
- citations.json: ten verbatim excerpts, one for each proof-step citation.
- report.md: this report.

There are zero new nodes and zero new Mathlib leaves. searches.jsonl records the actual search-command output and is retained. The original item statement, statement dependencies, source, blueprint fields and inherited searches were retained.

## Attachments

None. I searched lean/WeilConjectures for the item tag and for homotopical projectivity, semi-free dg modules, dg adjunctions and localization/Cech combinations. The Cech results in the ordinary scheme and module-complex files do not assert the arbitrary-dg-algebra derived Hom statement. A project declaration proving the whole item was not found.

## WANTED

None. The needed Stacks sources are present. I read perfect.tex Tag 08D2 (lemma-alternating-cech-complex-complex-computes-cohomology), dga.tex Tags 09KP (lemma-resolve), 09KM (lemma-property-P-K-projective), and 09KY (lemma-hom-derived), algebra.tex Tag 00CS (proposition-localization-exact), and homology.tex Tag 0133 (lemma-double-complex-gives-resolution). The scalar-adjunction citation is the existing sdga-based node, not a claim that 08D2 states a dg-Hom theorem.

## Audit of the imported item and blueprint

There was no prior sandbox split or report to preserve. The item has no imported proof and no project Lean attachment. Its statement is true as written. The finite principal-cover comparison is assembled from a Cech resolution of the target N; it does not require localization of Hom(P,N) to equal Hom(P_f,N_f). That latter assertion could require finiteness, and is never used here. Instead Hom(P,N_f) is identified directly with Hom(P_f,N_f) by extension--restriction.

I read the chapter record, unit record, SETUP's three-level rule, and the current blueprint at literature/blueprint/latest, main-20261024. The live unit record still references an older location and statement; the current unit lives in sec-six-functors-basics/sk-thm-sf-ctf-stability. Its direct-image proof paragraph (3) supplies the inherited route. This item's long blueprint.from.place describes the successive prerequisites of the earlier affine dg comparison split. No unit, chapter, or target statement is changed. blueprint_refs.py ancestor reports a null ancestor for the existing item, so its inherited null from.node and via chain were retained. The whole-blueprint searches for Cech, derived Hom, projective dg and localization found ordinary sheaf/module descent and tensor-Hom statements, not this dg derived Hom statement. I did not create a duplicate of those.

Mathlib searches ran through msearch.py: LeanFinder in two phrasings, LeanSearch, Loogle and two grep queries, with their actual output appended to mathlib_searches. The hits were ordinary derived-category fractions, ordinary cochain Hom, differential objects, scheme flat descent, and cotangent finiteness. I read Mathlib/Algebra/Homology/DifferentialObject.lean and the introduction and definitions of Algebra/Homology/HomotopyCategory/HomComplex.lean: differential objects there are ordinary complexes, and the Hom complex uses a fixed preadditive category, not modules with a nonzero dg algebra differential. They do not supply the item's descent assertion. No unavailable service was recorded as absence.

## Not duplicates

No new nodes. The project already has both the property-(P) resolution and its homotopical-projectivity theorem; making new left-module versions would duplicate them. The proof instead writes the graded-opposite conversion explicitly. Existing affine Cech exactness and finite-strip augmentation are cited directly.

## Tool uses

lem-weil-pbc-localization-module-exact is used as the ordinary algebra tool proving that termwise localization preserves quasi-isomorphisms. lem-sc-finite-strip-row-augmentation is the generic finite-width double-complex tool that permits an unbounded vertical direction. Both uses are declared in split_report.tool_uses. The ordinary affine Cech node is already Lean-closed and is used as a tool. None replaces a unit-level geometric argument.

## Review by Q72

I checked delivery-errors.md B through E against the actual proof, not just its dependency list. There are no new statement-only nodes to check for missing objects or source tags, no new node hiding a clause of the item, and no inline subargument over 2000 characters. Every proof step has a source and a Boolean elementary judgment. All non-elementary inputs are existing cited statements. I opened every cited node, copied the exact statement fragments to citations.json, and checked that the fragment occurs verbatim in that node. The two off-unit nonclosed inputs are generic algebra/homology tools as explained above. I also traversed the existing statement and proof dependencies of each cited node; none reaches this item.

In step 1, the property-(P) resolution node gives a quasi-isomorphism from P without boundedness, and the property-(P) homotopical-projectivity node gives precisely acyclicity of Hom(P,L) for acyclic L. Their right-module formulation was not silently substituted for the item's left formulation: the opposite multiplication, right action and degree-q map signs are written down. The signed left shifts correspond to unchanged right action. Central S in degree zero makes all comparison maps S-linear even though those two nodes are formulated over Z.

Step 2 uses the actual homotopically-projective-to-derived-Hom bijection, not a definition of the derived category. Applied to every shifted target it gives all H^q clauses. Applying its bijection to the identity-derived comparisons between two projective resolutions supplies inverse maps up to chain homotopy, so the claimed canonical independence is in D(S), not merely an equality of cohomology groups. It also supplies lifts needed for source naturality in the final step.

Step 3 uses the localization exactness statement on the short sequences defining cycles, boundaries and cohomology; restriction leaves these groups unchanged. The balanced-tensor fraction maps prove that ordinary dg extension is exact here. The ringed dg scalar adjunction node explicitly states existence, exactness, the action counit and the left-module version, so it really gives the required derived extension--restriction adjunction on a point. Its statement does not require the underlying dg algebra to be K-flat. I intentionally did not cite the flat ringed dg pushpull node, which does require K-flatness and would not apply to this item.

Step 4 is the elementary complex-level fraction calculation: a map P -> L with L already localized extends as x/s -> h(x)/s. It proves P_f is homotopically projective from acyclicity after restriction, rather than assuming that arbitrary Hom commutes with localization. The identity with successive localization is written as h(x)/(st). This is crucial for the diagram's transition maps and uses no compactness. Its earlier steps already established the derived meaning of the complexes used here.

Step 5 verifies that the finite total itself is a left dg C-module. The action on column p must be twisted by (-1)^(p|c|); the untwisted action would fail for an algebra with odd-degree elements. The displayed equality checks the horizontal Leibniz signs, and the vertical signs follow from the original Leibniz rule. The cited definition gives exactly those signed shifts and dg module conventions. I checked D squared and the singleton augmentation as chain maps, so the argument never applies Hom_C to an object that is only an S-complex.

Step 6 applies the affine Cech node to every S-module N^t under exactly the given unit-ideal hypothesis. Its statement gives exactness of the augmented alternating complex, including injectivity at the augmentation and the last term. That is the quasi-isomorphism of each horizontal row required verbatim by the finite-strip node. The strip has 0 <= p < r, all totals have finitely many summands on every diagonal, and its augmentation is the same singleton map. No lower or upper bound on t is used. The newest blueprint also states positive exactness of the nonalternating complex; its proof explicitly retains the stronger augmented alternating exactness, and the existing DAG node has exactly that statement. I did not edit this already closed node.

Step 7 uses the dg cone criterion node for both C and the ordinary dg algebra S concentrated in degree zero. This avoids borrowing an unrecorded general cone theorem. The cone of u is acyclic; homotopical projectivity makes its Hom complex acyclic. The component calculation (da + ub, -db) identifies that Hom complex with the cone of Hom(P,u), so the cone criterion proves the needed quasi-isomorphism. No claim of exactness of ordinary Hom on arbitrary short exact sequences appears.

Step 8 is finite regrouping with a written inverse and differential calculation. The degree-q map's column-p component has degree q-p. Its dg linearity sign is unchanged because q+p and q-p have equal parity. Its differential becomes delta + (-1)^p d_Hom, exactly the total required in the item. Finitely many p and J permit regrouping even though the Hom definition has a product across all source degrees. An infinite Cech cover would not permit the same argument; the finite-cover hypothesis is used here.

Step 9 assembles actual isomorphisms of complexes, then passes to D(S). Localizing the same P gives a coherent representative for every local derived Hom, so the total is specified on a strict model of the derived diagram. The transition maps agree by the fraction formula from step 4, and the comparison is the singleton augmentation, not an arbitrary inverse derived equivalence. Naturality is checked on module maps and on lifted maps of resolutions; homotopies give independence. The small cases tested were r=1 (f_1 a unit and the map an isomorphism), M=0, N=0, the zero ring, some f_i=0 (corresponding columns vanish), repeated generators, unbounded P,N, and a C with odd-degree elements. All constructions include those cases. No hypothesis or statement correction was necessary.

## What remains unfinished

No stage-1 argument is left unfinished. The split reuses existing nodes, some of whose own stage-1 proofs remain open, as permitted for one-level splitting. No Lean was written and no compiler, Lake or build command was run. The required server dry run and push determine the delivery disposition.
