# Stage-1 report: lem-coef-quasicategory-edge-triangle-presentation

## Files written

- `dag/nodes/sec-six-functors/lem-coef-quasicategory-edge-triangle-presentation.json`: split; no new node was needed.
- `citations.json`: citations for both proof steps.
- `report.md`: this report.

## Attachments

No Lean declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` carries this blueprint tag or states the item without `sorry`.

## WANTED

- Archived copy of Cisinski, *Higher Categories and Homotopical Algebra*, §1.6 (Lemmas 1.6.2 and 1.6.4, Theorem 1.6.6), for the edge presentation and triangle criterion.

## Not duplicates

No new node was created. The existing node `lem-coef-homotopy-category-triangle-calculus` is deliberately cited: it states the same theorem with the generated category presented explicitly as finite edge words modulo the degenerate-edge and 2-simplex relations. The current item uses the name `hQ` for that presentation, so step 1 identifies the two presentations by definition rather than introducing a second node.

## Review by Q122

I read the item source entry (Cisinski §1.6.1, Lemmas 1.6.2 and 1.6.4, and Theorem 1.6.6) and opened the statement of `lem-coef-homotopy-category-triangle-calculus`. Its statement explicitly supplies the vertices, finite composable edge words, degenerate-edge identity relations, 2-simplex relations, and concatenation composition used in step 1; this is exactly the presentation called `hQ` in the item. I also checked `def-cbc-enhanced-diagrams-cones`, whose statement defines quasicategories and the simplicial objects referenced by the item. Step 1 is therefore only a definitional identification and is marked elementary. Step 2 takes both required conclusions verbatim from the existing node: single-edge representatives and the iff between a composite equality and a 2-simplex with the three prescribed edges. The quasicategory hypothesis is passed unchanged as `D = Q`, and the vertices and edge orientations match the item's `u,v,w` convention. I ran the required Mathlib searches; they found the related `HomotopyCategory₂` and `Edge.CompStruct` declarations, but those are for Mathlib's separately constructed 2-truncated edge category and do not identify it with the generated `hQ`, so they are not a Mathlib leaf for this item. No statement was changed and no new duplicate node was introduced.

## Source error

None found.

## Second reading by Q122

- Item statement: checked the July 30, 2026 online Cisinski PDF, Remark 1.4.8 (printed p.17), §1.6.1, §1.6.5, Lemmas 1.6.2 and 1.6.4, and Theorem 1.6.6 (printed pp.21–25), against both clauses and every hypothesis; PASS. The generated category is the associated category from Remark 1.4.8, whereas §1.6.1 begins the coherence argument, not the presentation definition. The edge-class quotient of §1.6.5 gives representatives, and the theorem identifies it with the associated category. Its proof makes the triangle predicate invariant under the classes of all three prescribed edges; thus the converse gives the original edges, not merely homotopic replacements. No source tag in Stacks was substituted for this non-Stacks result.
- Step 1: opened the complete statements of `def-cbc-enhanced-diagrams-cones` and `lem-coef-homotopy-category-triangle-calculus`; checked vertices, composable words, empty words, degenerate identities, the [0,1]/[1,2]/[0,2] orientation, and concatenation; PASS after spelling out the two inverse identity assignments on words. Elementary: equal generating relations make both assignments well-defined; concatenation makes them functors; their composites fix words. The quasicategory hypothesis needed by the cited statement is already in force, with `D=Q` in the same input universe.
- Step 2: checked the two conclusion sentences of `lem-coef-homotopy-category-triangle-calculus` against Cisinski Theorem 1.6.6 and its class-invariance argument; PASS after writing the representative argument through the inverse functor and the exact substitution `(f,g,h)=(u,v,w)`. The same underlying simplicial set supplies the same triangle. Equality passes in both directions through the inverse functors preserving those particular classes. No proof-internal object of the cited node is used, and no uncited non-elementary assertion is needed.
- New nodes: NONE; checked the sandbox node set and the source/keyword search across the shared DAG, both full blueprint snapshots, and the Lean reference trees. The existing triangle-calculus node is an exact duplicate theorem in the same unit and is cited rather than created again. B1–B7 are vacuous for new nodes. The item retains its definition dependency and statement, uses single-escaped TeX, and gives named source places. No statement dispute was found.

Small-case checks: the empty quasicategory has no objects, arrows, or triples, so both clauses are vacuous. For `Q=Δ⁰`, all words reduce to the single degenerate identity and the unique degenerate triangle witnesses its equation. In the nerves `Δ¹=N([1])` and `Δ²=N([2])`, edge words represent the ordinary arrows and the triangles are exactly their composition equations, including repeated vertices. More generally an ordinary category nerve checks the orientations and both identity cases. An empty word at any vertex is represented by that vertex's degenerate edge. No dimension-zero horn or nonemptiness hypothesis was added. Ring, field, and scheme edge cases do not occur in this statement.

Independent searches: ran `msearch.py` with the new semantic phrasing “For a simplicial set satisfying inner horn filling, compare categorification by the nerve left adjoint with the category of homotopy classes of edges”, Loogle `"homotopyCategory₂_fac"`, and grep `hoFunctor₂|homotopyCategory₂_fac|TODO`, first unrestricted and then restricted to `AlgebraicTopology/Quasicategory`. The unrestricted grep was truncated by unrelated TODO hits and gives no absence evidence; the restricted one identifies the comparison TODO. Opened Mathlib `TwoTruncated.lean:21–28,223–297` and `HomotopyCat.lean:19–36,275–315`: `homMk_surjective` and `CompStruct.nonempty_iff` apply to `HomotopyCategory₂`; the generated category is the different `HomotopyCategory`, with comparison explicitly TODO at line 28. Nerve-adjunction hits provide no full theorem. Results are preserved in `searches.jsonl` and recorded verbatim in the item's search records; zero Mathlib leaves. Independent id, name, and concept searches in slopmaster2 and the exact upstream master found only unrelated complex homotopy categories, so no finished project declaration was attached. These read-only searches did not compile anything.

Changes and reasons:

- Corrected the source and step-1/proof-origin places to include Remark 1.4.8, because §1.6.1 does not define the generated presentation.
- Replaced the implicit presentation identification with explicit inverse functors on words, and replaced “Transporting” with the representative and equality arguments, satisfying E5 without changing either statement or route.
- Consolidated the two step-2 citation records into one verbatim contiguous quote containing both conclusions, so each citation has one complete supporting quote.
- Added the independently executed search records and this second reading. No new node, statement correction, Lean edit, or maintainer field change was needed; the original `## Review by Q122` remains intact.
