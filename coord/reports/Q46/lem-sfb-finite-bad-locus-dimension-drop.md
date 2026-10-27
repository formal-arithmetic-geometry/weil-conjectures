# Stage-1 report: lem-sfb-finite-bad-locus-dimension-drop

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-bad-locus-dimension-drop.json: item, statement; split into six proof steps using existing DAG nodes. No Mathlib match for the whole item.
- citations.json: one verbatim statement quotation per cited node per step (17 entries).
- searches.jsonl: six newly executed, unmodified search records from msearch.py; the item's five inherited searches are preserved.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. I searched the entire project WeilConjectures tree for the blueprint tag, bad-locus terminology, spreading and dimension-drop/incomparability terminology, and read the nearby LisseLocus file. No declaration states this arbitrary-subset spreading and finite-cover conclusion. The LisseLocus proof is about constructible sheaves, not arbitrary point sets. Existing reduced_induced_closed_subscheme is a prerequisite already represented by lem-weil-pbc-reduced-induced-closed-subscheme, not an attachment for this item.

## Literature wanted

WANTED: literature/de-jong-families-curves-alterations-1997.pdf, Lemma 5.7 proof, printed p.615, for lem-sfb-finite-bad-locus-dimension-drop. The local PDF is absent. I read the publisher's primary scan at https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf, PDF page 17 (zero based), including both proof paragraphs. The first proves generic quasi-splitting spreads; the second uses generic points of the bad closure and a finite cover to decrease its dimension. This item assumes spreading and abstracts just that second paragraph. The detailed proof is correctly marked agent-written: the scan does not supply the topological details or the integral-incomparability calculation.

The Stacks sources used are present and were read directly: schemes.tex, lemma-reduced-closed-subscheme (01J3), lemma-scheme-sober (01IS), lemma-basis-affine-opens (01IT); properties.tex, lemma-Noetherian-irreducible-components (0BA8), lemma-characterize-integral (01ON); algebra.tex, lemma-finite-is-integral (00GK), lemma-integral-no-inclusion (00GT); topology.tex, definition-irreducible-components (004V), definition-generic-point (004X), definition-Krull (0055). Tag/label pairs were checked in tags/tags. No SGA source is used.

## What changed and what was wrong

The imported item is mathematically correct. Its proof was empty. I supplied the missing finite-component open-neighbourhood argument and the affine strict-chain argument rather than creating lemmas that merely repeat clauses of the item. The only statement addition is an explicit cross-reference identifying the already-mentioned reduced induced closed structures with lem-weil-pbc-reduced-induced-closed-subscheme; it adds no hypothesis or conclusion and does not change their meaning. That construction is now also a statement dependency. All other original statement text, source, ancestry, and logged searches are retained.

A possible trap is to infer that the closure of A_W avoids a fibre merely because A_W does; this is false for arbitrary sets. Step 4 instead uses the generic membership proved in step 2, continuity, and maximality of an old component. Another trap is to apply flatness to generic points under a finite morphism. Flatness is absent and unnecessary: step 5 uses integral incomparability to preserve strictness of chains, while step 4 proves the required avoidance directly. In particular a component of W need not dominate a component of V.

The inherited blueprint.from.node is null, as tools/blueprint_refs.py ancestor reports. The recorded via list is retained. I read the chapter and unit records and the current main-20261015 direct-images proof (3). The auxiliary remains below its nodal quasi-splitting prerequisite and follows de Jong's generic-bad-points and dimension-descent route. It is not the unit's key node, so no realized fields are edited. No blueprint_update is present on this item.

## Mathlib and duplicate searches

Before writing I searched the whole DAG statements by component finiteness, sobriety, generic point, reduced closed structure, finite integral maps and incomparability, and ran blueprint_refs.py searches for incomparability, irreducible components, Noetherian, generic point, bad locus, and dimension drop. This found existing prerequisites, including the more precise lem-weil-pbc-integral-incomparability instead of creating a scheme-level duplicate. The separate pqf-lem-incomparability states the same basic ring tool; I reuse the established proper-base-change node already carrying strict contraction.

The item's searches used leanfinder (two different formulations), loogle, leansearch and grep (two patterns, the second restricted to Topology). Every result was read and recorded from searches.jsonl without inventing a query. Returned IsGenericPoint.image concerns images of one generic point; genericPoints.closure concerns density of the component generic points; finite_irreducibleComponents_of_isNoetherian and finite_preimage_singleton concern only finiteness. None states membership in an arbitrary bad subset with the two spreading hypotheses, nor its finite-cover dimension drop. I read Sober.lean:39-94, NoetherianSpace.lean:193-211, AlgebraicGeometry/Noetherian.lean:364 and Ideal/GoingUp.lean:221-224. These confirm ingredients already covered by the cited DAG leaves, not a one-line match for this item.

## Not duplicates

No new nodes are created. Every candidate non-elementary prerequisite was found in the existing DAG. The elementary component-open argument, generic-fibre avoidance argument and chain-length calculation remain explicit steps, as required by D1/D2 and the no-elementary-new-nodes rule.

## Review by Q46

I checked the actual statement of every cited node, not merely its name, and copied those statements into citations.json. The six steps use them as follows.

1. lem-weil-pbc-reduced-induced-closed-subscheme (read with its 01J3 source and the project's existing reduced_induced_closed_subscheme declaration) supplies the reduced closed subschemes on E and its components. lem-sc-noetherian-closed-subset-finite-components states both that the closed set is covered by components and that only finitely many occur; this is exactly what step 1 needs for either V or W. lem-weil-pbc-scheme-sober supplies existence AND uniqueness of generic points, which a definition of generic point alone would not do. def-pc-integral-scheme explicitly includes the reduced-and-irreducible characterization. Hence each component with reduced structure is an integral reduced CLOSED subscheme of the ambient Noetherian scheme, with precisely the hypothesis required by spreading. No Noetherianity theorem for the reduced closed subscheme is silently needed: spreading quantifies over every integral reduced closed subscheme.

2. The two definitions def-sc-generic-point and def-weil-irreducible-components supply closure of the singleton and maximality. The step proves the rest: nonempty component opens contain the generic point; the generic point is outside the other distinct components; deleting their finite union gives an open of the entire bad closure contained in that component. The good open from spreading intersects this open at the generic point. Since it is then open in E, not just in the component, it contradicts density of B in E. This ambient-open check is necessary and is written explicitly. This argument applies unchanged to (W,A_W), using W's own spreading hypothesis and Noetherianity. It proves an actual clause, without delegating that clause to a new node.

3. def-pc-scheme makes a a morphism of locally ringed spaces, with continuous underlying map. The only operations used are inverse image of a closed subset and the defining minimality of closure. Neither closedness of the finite map nor surjectivity is used. Empty Z is treated already here.

4. Existence of a component through w and its generic point was established in step 1, and membership t in A_W in step 2. I checked that continuity only gives that a(t) generalizes s, not equality by itself. Equality follows because the irreducible closed singleton closure of a(t) lies in Z and contains the entire component closure{s}; maximality forces it to be that component, and lem-weil-pbc-scheme-sober supplies uniqueness. The singleton-closure irreducibility has its one-line proof in the step. Thus the contradiction is genuinely with A_W intersect a^{-1}(s), exactly the assumed set, rather than an unjustified assertion about the closure. The uses contain the definitions and the uniqueness theorem actually needed.

5. I checked lem-weil-pbc-affine-opens-basis really supplies an affine containing a(v), and that its open underlying set also contains a(u) by specialization. def-weil-finite-integral-morphism supplies an affine full inverse image and the finite MODULE ring map. lem-weil-pbc-finite-algebra-is-integral turns that precise hypothesis into integrality; lem-weil-pbc-integral-incomparability supplies STRICT contraction for a strict prime inclusion (its statement is more precise than mere distinctness in one fibre). The source's primes are distinct because u and v were distinct and lie in a common affine. The Zariski formula closure{q}=V(q) is derived explicitly from closed sets V(I), and the underlying Spec map is contraction, so no separate scheme-level chain theorem is assumed. The target ring may have a kernel in S; the incomparability statement allows arbitrary integral maps, so no injectivity, flatness, or dominance is introduced.

6. The component containing x_0 exists by step 1 for Z. Its generic point s gives one extra STRICT link because step 4 excludes s from the entire image of Z_W. I checked the length convention: n links in W become n+1 links in Z, whence n+1 <= d, not merely n <= d. def-kun-topological-krull-dimension uses closed-set chains, so the proof explicitly identifies these with reverse chains of generic points using sobriety. Z and Z_W are closed subsets of schemes, hence their relatively closed irreducible sets are ambient closed and the cited sobriety theorem applies; its uniqueness also guarantees strictness. Closed chains of Z are chains of V, proving the finite bound used here. The supremum for nonempty Z_W is at most d-1. When d=0 any point gives the forbidden length-one chain in Z. Z empty was handled in step 3.

Small cases: V or W empty; A empty; A=V; Z zero dimensional, possibly with several components; one-dimensional Z and a nonempty zero-dimensional new closure; intersecting old components; finite closed immersions (not flat and not surjective); nilpotent thickenings; a finite map with two components over one old component. All fit the proof. For the identity map, A_W contained in a proper closed point of an integral curve gives the expected 0<1 example. Dropping spreading would let a dense set of closed points omit its generic point, so the proof correctly uses that hypothesis. Dropping finiteness would permit a positive-dimensional fibre to retain long chains; the strict-contraction step correctly prevents that.

B1--B10: no new node schema/leaf/blueprint obligation is evaded; no exact project attachment was found; source tags were checked. C1--C8: every non-elementary input is a cited statement, no cited proof is used as an interface, and no new dependency back to this item is introduced. The cited non-Mathlib reduced-induced node is already Lean-closed, and the other citations are Mathlib leaves, so these are permissible generic tools without changing the unit route. D1--D5: all clauses are proved in the item and all missing source arguments are written out. E1--E7: all hypotheses, the ambient versus relative opens, specialization direction, and empty/dimension-zero cases were checked above; no statement dispute was found. Every step is shorter than 2000 characters, and neither non-elementary step hides another independent lemma.

## Unfinished work

No mathematical part is left unfinished. The independent maintainer review remains after delivery. No Lean was written and no compiler, Lake, build, or local preflight/check_dag/review_split command was run. All edits are confined to the designated sandbox. The server-only review_split check returned PASS for the six-step split with zero new nodes before packaging.
