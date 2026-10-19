# Q74: lem-coef-unstraightening-simplex-dk-equivalence

## Files written

- `dag/nodes/sec-six-functors/lem-coef-unstraightening-simplex-dk-equivalence.json`: original statement retained; thirteen-step split, with complete dependency union and blueprint provenance.
- `dag/nodes/sec-six-functors/lem-coef-ordered-simplex-cone-evaluation.json`: one new statement-only node, not split. No Mathlib match.
- `citations.json`: verbatim cited statements for all 42 step/node pairs. These are the actual interfaces, including hypotheses; the step-specific uses are described below.
- `searches.jsonl`: five actual search-command records for the new lemma. Both semantic phrasings were read, together with LeanSearch, Loogle and source grep. No Mathlib leaves.
- `HTT-reading.pdf`, `HTT-reading.txt`: sandbox reading copies, not library additions. `write_split.py` regenerates the submitted JSON from the read-only repository and recorded searches.

## Attachments

None. Searched both permitted `WeilConjectures/` source trees for the exact item tag, unstraightening, Dwyer--Kan and right-fibration terminology; no declaration states the item or the new coend calculation. Upstream master was treated only as reference material. The inherited item's Mathlib search results were read and retained, rather than invented or rerun under a different claim. The new lemma has five fresh logged searches.

## Wanted literature

WANTED: Jacob Lurie, *Higher Topos Theory*, https://people.math.harvard.edu/~lurie/papers/HTT.pdf, Section 2.2.2, Lemmas 2.2.3.1, 2.2.3.7, 2.2.3.9--10 and Appendix A.3.1/A.3.3, for this item and lem-coef-ordered-simplex-cone-evaluation. I read the online PDF in the sandbox; the project literature inventory has no archival HTT copy. No SGA source is used. These simplicial straightening results have no corresponding Stacks tag; no unrelated tag is substituted.

## Issues found and repairs

The original statement is well typed and retained. The imported source pointer is useful but its short proof cannot simply become citations to the existing general Quillen-equivalence results: the existing contravariant-slice model, general unmarked straightening, infinity model localization, cosimplicial-frame comparison, and enriched-right-Quillen-equivalence nodes all lead back to this item. I checked the transitive statement/proof dependency graph before choosing the interfaces. Every dependency used in this delivery has no path back to the item.

The split follows the same ordered-simplex reduction as HTT but expands the argument independently of any slice model structure. It computes strict counits using tails and then transfers to coherent counits with the already existing enriched projective change-of-index theorem. Mapping spaces are compared by the ordinary derived adjunctions of two concrete left Quillen functors from simplicial sets. This retains the source's straightening route without relying on the general result being proved above us.

During self-review I corrected the tensor-mate direction. A right-enriched functor gives the colax comparison `L(X × K) → LX × K` by transposing `X × K → ULX × K → U(LX × K)`. This direction gives precomposition from `Nat(LX,G)` to `Fun(X,UG)`. The opposite direction is not the transpose of that map. The proof now uses the typed direction consistently, irrespective of the beta notation in the appendix display. This is not a change to the item statement.

## Not duplicates

lem-coef-ordered-simplex-cone-evaluation vs lem-coef-cone-presheaf-adjunction: the existing node defines the coherent cone adjunction, gives its projective model, and preservation properties; it does not calculate the enriched left Kan extension to a strict ordered diagram as a coend over a terminal interval.

lem-coef-ordered-simplex-cone-evaluation vs lem-coef-cone-boundary-projective-cells: the existing formula is for a simplicial set supported over one vertex and gives a representable times its coend. The new formula applies to arbitrary simplicial sets over a simplex, including simplices whose vertices cross the chosen threshold, and calculates strict ordered straightening at every vertex with its diagram maps and adjunct restriction.

lem-coef-ordered-simplex-cone-evaluation vs lem-coef-right-straightening-fiber-comparison: the latter is a weak equivalence from the fiber to coherent straightening for right fibrations over arbitrary bases. The new statement is an exact strict-diagram calculation for all maps to a simplex, with no right-fibration hypothesis. It neither states the coherent fiber-comparison theorem nor assumes its cyclic proof.

lem-coef-ordered-simplex-cone-evaluation vs lem-coef-unstraightening-simplex-pointwise: the existing node states right-horn preservation, pullback, and fiber identification for unstraightening; it does not compute strict straightening on arbitrary objects or the restriction of an adjunct through the coend of a tail.

lem-coef-ordered-simplex-cone-evaluation vs lem-coef-unstraightening-simplex-dk-equivalence: the new node is a combinatorial value formula and its adjunction compatibility. It contains no mapping-space weak equivalence or essential-surjectivity assertion. Those are proved in the item's steps, not delegated to a renamed clause.

Whole-DAG keyword/place searches and `blueprint_refs.py search` for unstraightening, straightening, simplex, ordered simplex, pinched and twisted realization found no blueprint duplicate. The new node's ancestry was obtained with `blueprint_refs.py ancestor`. The unit is not a key node of this item, so no unit realization fields are changed.

## Review by Q74

I read the item, its unit and chapter, the inherited blueprint ancestor's coefficient-adjunction paragraph, and the source passages of HTT: the pinched-realization construction and Propositions 2.2.2.7/9 with Corollary 2.2.2.10, the enrichment in Remark 2.2.2.12, the tail evaluation in Lemma 2.2.3.1, its fiber-adjunct application in Lemma 2.2.3.7, and the simplex comparison in Lemmas 2.2.3.9--10. I also read the tensor/mapping argument in Appendix A.3.1 and the enriched change-of-index statement in A.3.3.8. The proof is marked agent-origin because its direct non-slice-model expansion is ours. The sole new node states the tail formula from Lemmas 2.2.3.1/7 and the natural adjunct compatibility needed in those proofs, with `[n]^op` and the vertex `j` used consistently instead of the source's reversed label `i=n-j`.

For step 1 I opened the pinched-cube statement: it supplies the latching monomorphism, contractibility, degree-zero point, and the cosimplicial map, not an already proved coend equivalence. The boundary-collapse statement supplies preservation of monomorphisms. The monomorphism-cell statement supplies the skeletal presentation, and the gluing/filtered-equivalence statement supplies exactly the pushout and sequential-colimit comparisons used after objectwise evaluation. I checked that the required attaching legs are monomorphisms on both sides. The Kan-model statement gives cofibrancy of every simplicial set. The derived-counit statement then applies to `V ⊣ W` after the explicitly proved natural weak equivalence `V → id`, and gives its counit at Kan targets. No theorem about an already constructed infinity localization is taken from those statements.

For step 2 I read the cone-adjunction statement's preservation of monomorphisms and its explicit projective fibrations. The simplex-pointwise statement supplies the missing right-horn weak equivalences and the natural `F(j) → W F(j)` comparison for Kan values. With the definition of right fibration this proves the right-horn lift. The gluing statement says both that all displayed mapping complexes into right fibrations are Kan and that vertex-fiber equivalences admit actual simplicial homotopy inverses. Those are the precise consequences used.

For step 3 the cone-adjunction definition gives the pushout universal property and the pinched-cube statement gives `J^m`, `Q^m`, and its cosimplicial map. The collage calculation is written out: the parameter part factors through the collapsed cone, pairing/projection are inverse, and composition uses the parameter diagonal. I did not cite the external-product node, which itself depends on the general straightening route. The step is elementary construction from the cited definitions, not an imported equivalence theorem.

For step 4 I checked the horn convention: `Λ_1^1` is the final vertex, exactly the endpoint at which the identity lift must be prescribed. The right-anodyne product statement applies with the other factor `E_j → E_{≥j}` a monomorphism. Its pushout-product includes the entire fiber cylinder, so the lift fixes that fiber, not just its endpoint. The explicit definition of right fibration gives the lift, and the simplicial-homotopy-equivalence statement gives its weak-equivalence consequence. All fibers here are strict fibers; no replacement is silently substituted.

For step 5 I checked the coherent simplex mapping-posets in the pinched-cube statement: the maximal subset is a terminal object, including diagonal endomorphisms; the backwards mapping sets are empty. The written nerve contraction proves weak equivalence of these mapping objects using the cited simplicial-homotopy statement. The projective-model-calculus statement explicitly allows non-locally-Kan indexing categories and says enriched left Kan extension/restriction is a simplicial Quillen equivalence for a DK equivalence. The new evaluation lemma is used only for its strict tail-coend formula, diagram maps, and adjunct restriction. Its stronger exact formula is not inferred from a weak fiber comparison.

For step 6 I verified every inference against steps 1, 2, 4, 5 and the new statement. The restricted strict counit is the actual coend counit, and the full counit follows by two-out-of-three with the realized fiber inclusion. For the second part, the composite is `c_H V(e_j)` by the specified adjunct compatibility; the natural weak equivalence `q` reflects weak equivalence of `V(e_j)` by an explicit two-out-of-three square. No unproved recognition of right fibrations as slice-fibrant objects is used.

For step 7 both occurrences of the projective Quillen-equivalence criterion have the required cofibrant source and fibrant target: first `F,H`, then `LUF,H`. Cofibrancy of `LUF` follows from the cone-adjunction statement's monomorphism preservation. The replacement map to `H` is a trivial cofibration, and `h` has fibrant endpoints. The strict counit and tail calculations of the preceding steps show the displayed composite is a weak equivalence. I checked its identity with the counit composite by the ordinary adjunction bijection, so the subsequent two-out-of-three argument concerns the actual coherent counit.

For step 8 the right-horn weak equivalences are the precise clause of the simplex-pointwise statement. Closure under cells and retracts is the left-lifting-class property, so no preservation of arbitrary weak equivalences by `L` is presumed. The explicit terminal-vertex horn filtration includes the case `m=0`. The right-anodyne product statement provides the product with `X`. The boundary-collapse statement is then applied to the colimit-preserving functor `K ↦ L(X×K)`, with all its boundary and collapse hypotheses checked. This proves its right adjoint is Kan-valued on projectively fibrant targets.

For step 9 the projective simplicial-model statement supplies the left Quillen property of `LX×-`, since `LX` is cofibrant. I checked the explicit transpose of the enrichment, corrected its direction, and checked the degree-zero identity by the triangle identity. The naturality square with collapse has the correct source and target after that correction. Boundary-collapse and the objectwise gluing theorem justify the passage from simplices to all parameter sets, with monomorphic attaching maps.

For step 10 the ordinary derived adjunction is expressly in the derived-counit node's statement. Its use requires only the two left Quillen adjunctions already proved. Precomposition by the weak equivalence `β` gives the Hom-set bijections. The localization-map-surjectivity statement supplies an actual representative of the inverse between the two Kan complexes, and the localized-good-homotopy-test statement applies with the good cylinders `K×Δ^1`. The simplicial-homotopy-equivalence statement then converts this actual inverse to weak equivalence. I deliberately avoided the existing localization-detects-weak-equivalences node, whose current dependency closure returns to this item.

For step 11 I checked the Brown statement gives exactly the factorization with a cofibration section for a map between cofibrant objects. Because the counit is already proved weak, both `i` and its section `s` are trivial cofibrations by two-out-of-three. The projective simplicial-model axiom applies with target `G` fibrant and gives the stated trivial Kan fibrations. The identity `s* p* = id` has the correct order. This proves weak equivalence on mapping spaces with no unproved Brown functor lemma. The parameterized mate identity also checks that the resulting map is the specified enriched unstraightening map.

For step 12 I checked that `LE → F` and `a_!F → H` are chosen as trivial cofibrations and hence `F` remains cofibrant as well as fibrant. The left Quillen property of `a_!` preserves the former. The strict fiber-adjunct comparison then applies to the composite into the fibrant `H`. The factorization of its adjunct through `UF` is an adjunction identity, and the gluing statement gives the demanded actual over-base homotopy inverse after the fiberwise two-out-of-three argument. Step 13 is the elementary assembly of full faithfulness and essential surjectivity on component categories.

I tested the new formula when `n=0`, `X=∅`, `X` is a vertex at `t`, and `X` is an edge whose vertices lie on opposite sides of `j`. These give respectively `V(X)`, the empty diagram, a point exactly when `j≤t`, and the coend of the surviving terminal subedge or vertex. At `j=n` the tail is exactly the fiber. The formula imposes no Kan or right-fibration hypothesis, while the deformation retraction and all later weak fiber comparisons explicitly do. Empty fibers stay empty and all weak-equivalence comparisons are meaningful there.

I checked delivery-errors B--E: self-contained notions and hypotheses in the sole new statement, empty new proof and proof dependencies, recorded searches actually run, no duplicate or renamed conclusion, no unquoted non-elementary external interface, no general slice model or cyclic dependency, and unchanged blueprint metadata and statement. The only off-unit citation is the generic simplicial-homotopy-equivalence lemma; it is declared in `split_report.tool_uses`, not installed as maintainer `tool_uses`.

## Unfinished work

No intended proof step is deferred except the new statement-only ordered-simplex evaluation lemma, as required for a one-level split. It remains a separate stage-1 item. This sandbox is for the independent second reader; no delivery push is authorized or performed.

## Second reading by Q74

- Item statement: checked against HTT Lemma 2.2.3.10 and the stated cone, right-fibration, and pinched-cube interfaces; verdict: retained, with the standard-simplex restriction and cofibrant-fibrant mapping category stated explicitly.
- Step 1: checked against the pinched-cube latching, boundary-collapse, skeletal gluing, Kan model, and derived-counit statements; verdict: complete realization comparison and counit argument, including the empty simplicial set.
- Step 2: checked against the cone adjunction, simplex-pointwise horn equivalence, right-fibration definition, and gluing statements; verdict: the adjunction supplies the right-horn lift and the fiber comparison used later.
- Step 3: checked against the cone pushout and pinched-cube definitions; verdict: the product/enrichment construction is elementary from those interfaces and preserves identities and composition.
- Step 4: checked against the right-fibration lifting convention and right-anodyne pushout-product statement; verdict: the tail deformation retract is relative to the vertex fiber, including the $n=1$ horn convention.
- Step 5: checked against the pinched-cube mapping-poset description, simplicial homotopy equivalence, projective change-of-index, cone adjunction, and ordered-simplex evaluation node; verdict: the collapse is a DK equivalence and the enriched adjunction/evaluation are used with the stated orientation.
- Step 6: checked against the ordered-simplex formula, strict counit, tail comparison, and two-out-of-three; verdict: objectwise strict counit and fiberwise adjunct comparison are justified.
- Step 7: checked against the projective Quillen-equivalence criterion, fibrant replacement, strict counit, and cofibrancy preservation; verdict: coherent counit follows by the displayed adjunct identity and two-out-of-three.
- Step 8: checked against right-horn generation, terminal-vertex right-anodyne filtration, pushout-product, and boundary-collapse; verdict: the parameterized left Quillen functor and its right adjoint are established without a slice model structure.
- Step 9: checked against the simplicial model tensor axiom, corrected colax tensor mate direction, and skeletal gluing; verdict: the mate $L(X\times K)\to LX\times K$ is typed correctly and is a weak equivalence for all parameters.
- Step 10: checked against the two derived adjunctions, localization representative theorem, good-cylinder homotopy test, and simplicial homotopy equivalence; verdict: the right mate is a weak equivalence between Kan complexes.
- Step 11: checked against Brown split factorization, mapping-space trivial fibrations, and the enriched mate identity; verdict: full faithfulness on mapping simplicial sets follows, including the first mapping-map factor.
- Step 12: checked against projective fibrant replacements, the ordered change-of-index adjunction, Step 6, and right-fibration gluing; verdict: every right fibration is equivalent over the simplex to an image object.
- Step 13: checked against the two Dwyer--Kan conditions; verdict: the path-component functor is fully faithful and essentially surjective.
- New node `lem-coef-ordered-simplex-cone-evaluation`: checked clause by clause against HTT Lemmas 2.2.3.1 and 2.2.3.7 and the cited cone/pinched-cube/projective interfaces; verdict: self-contained statement-only auxiliary calculation, with no fibrancy assumptions and all tail, fiber, and adjunct clauses explicit.

Changes made: no mathematical or structural change was required after the independent reading. I added this second-reading audit section and marked the sandbox check as completed; the existing citations, searches, statement dependencies, proof dependencies, and blueprint metadata remain consistent with the reviewed files.
