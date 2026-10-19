# Stage-1 report: lem-sf-proper-open-tensor-compatibility

## Files written

- `dag/nodes/sec-six-functors/lem-sf-proper-open-tensor-compatibility.json`: statement; split using existing DAG nodes; no Mathlib match for the full geometric identity.
- `citations.json`: nine verbatim statement quotations, one for each cited node in each proof step.
- `report.md`: this report. The actual search log is `searches.jsonl`.

New nodes: 0. New Mathlib leaves: 0. No Lean files, builds, live-project writes or direct git commands.

## Attachments

None. Searches by the blueprint id and by proper/open, tensor and refinement concepts in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found no declaration of the full item. I read `SixFunctors/Etale/Derived/RefinementLowerShriekProjection.lean`, including `AlgebraicGeometry.Etale.refinementLowerShriekProjectionMap_baseChange` and its inverse form, and the statements of `refinement_projection_key` and `projectionMapOfCompactification_comparison` in `LowerShriekProjectionRefinement.lean`. They concern etale coefficients and cartesian refinement squares. They do not cover arbitrary commutative squares of the pro-etale sites, or strict semilinear systems. These partial existing results do not justify ATTACH. The exact master checkout was checked by item id as reference only; no sorry declaration was counted as completed work.

## WANTED

None. The proof is marked agent-written: the blueprint supplies the normalization route, and the existing DAG projection-mate lemma supplies the tensor calculation. Stacks supplies the ringed-site and proper/open foundations, not a quotation of a strict semilinear system theorem.

## Corrections and reuse

The imported item had no proof. Its statement and statement dependencies are preserved. In particular the two unbounded coefficient categories, the absence of a Cartesian hypothesis, and the absence of a claim that either projection morphism or Gamma is invertible are preserved.

A whole-DAG statement/title search for proper/open, projection morphisms, counit normalization and open restriction found the existing `lem-sf-proper-open-projection-mate`. I opened its full JSON. Its tensor equation is this item's equation, including the unbounded strict semilinear-system clause. The finite part uses a proper-adjunction normalization, whereas this item specifies the map by open adjunction; Step 2 explicitly identifies those maps. Reusing that node avoids inventing a second tensor-compatibility lemma. Whole-blueprint searches (`blueprint_refs.py search` with tensor, proper/open, projection, and proper.*open.*projection) found no blueprint node that states the complete item. `blueprint_refs.py ancestor` gives `lem-fix-weil-operations`, and the existing from.place and via are retained. The exact ancestor proof and the source proof of `prop-sf-pf-coherence` were read.

The remark unit `sk-rem-sf-pf-done` has no proof steps and is not this item's key statement. No unit record was edited. The generic off-unit tools for open normalization and simultaneous system operations are declared in split_report.tool_uses. Two other off-unit tools used for Noetherian geometry and the mate-pasting tool are already Mathlib leaves. A read-only traversal found no dependency path from the reused projection-mate node back to this item.

## Not duplicates

No new nodes are proposed. The item versus `lem-sf-proper-open-projection-mate`: the latter already states the desired tensor equation in both coefficient settings, normalized by the clopen-projection proper mate. This delivery cites it, and proves that the finite proper mate is the open-adjunction-normalized map specified by the item. The system clause of that node already names the intrinsic Gamma_Q. This is reuse of an existing lemma, not a newly created node restating an item clause.

## Mathlib searches

The inherited item searches remain intact. I ran the required logged LeanFinder, Loogle, grep and LeanSearch searches for the current item, including a second phrasing about the mate of the clopen component projection. All services answered. I read their hits: they concern generic monoidal adjunctions and mates, cartesian tensor projections, coalgebra counits, condensed modules and ordinary tensor constructions. The Loogle/LeanFinder candidates `CategoryTheory.Adjunction.map_μ_comp_counit_app_tensor` and `unit_app_tensor_comp_map_δ` were checked at Mathlib/CategoryTheory/Monoidal/Functor.lean:1024 and :1036. They assume a monoidal adjunction and concern its lax/oplax structure maps; neither is the geometric proper/open identity on the categories in the item. The mate-pasting source was read in Mathlib/CategoryTheory/Adjunction/Mates.lean:170 and :209 and is used through the existing leaf. Every added search record is copied from the actual sandbox log with its exact query text. The repeated grep has the same zero-hit result; no unsuccessful service was recorded as absence.

## Review by Q89

I checked delivery-errors B through E against the JSON, the existing node statements, and the sources, rather than treating imported dependencies as certified proofs. There are no new unsplit nodes, duplicate definitions or Mathlib leaves needing an invented declaration or line reference. The statement has not been weakened, and no STATEMENT-DISPUTED correction is needed.

For the item, I read the compactification-independence sentence and subsequent open restriction and counit-transpose paragraphs of `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-prop-sf-pf-coherence/prop-sf-pf-coherence.proof.md`, and the ancestor `lem-fix-weil-operations.proof.md`. These use the prescribed open-normalization and mate route. I also read Stacks Tag 0F7B, `more-etale.tex`, label `lemma-shriek-proper-and-open`: its construction is a canonical map on unbounded etale complexes, and its torsion hypothesis concerns invertibility. Our argument claims only an equality of normalized maps and never applies its invertibility result on arbitrary pro-etale/system inputs. I read Tag 07A7, `sites-cohomology.tex`, `remark-base-change`, for the counit-transpose normalization; Tag 0GL1, `lemma-j-shriek-and-tensor`, and Tag 0E8I, `sites-modules.tex`, the identically named label, for open tensor comparisons. The latter tags do not themselves state all the system refinements: those are cited as existing agent-formulated obligations, without attributing them to Stacks. No SGA source is used.

Step 1 uses exactly the statements of `lem-weil-pbc-finite-type-over-noetherian` and `lem-weil-pbc-noetherian-open-subscheme-noetherian`. I read both nodes, Stacks 01T6 (`morphisms.tex`, `lemma-finite-type-noetherian`), and the Noetherian definition/open-local statements in `properties.tex`. The former node applies because Spec(k) is Noetherian and V,Z are finite type over k; the latter asserts local Noetherianity AND quasi-compactness of every open subscheme, so it really gives the quasi-compactness of the inverse image of an affine open. No separatedness of V or Z over k is smuggled into the argument. The field assertion is elementary because a field has only two ideals and its spectrum is one point.

Step 2 uses the full statement of `lem-sf-proper-open-projection-mate` to specify alpha and its proper mate, `def-weil-pbc-adjunction-mate` for the explicit transpose, `lem-weil-pbc-mate-pasting` for the pasted adjunction/counit, and `lem-sf-open-tensor-normalization` for the base-change comparison whose open restriction is identity. I read all four statements. The last node states identity normalization for beta as well as gamma, so it actually supplies what the step needs. On the clopen component, projection is identity and restriction of its extension is the identity; the transposed remaining arrow is epsilon_r. The two adjunction bijections then prove lambda P_i(g)=1 and g=Gamma. This uses neither full faithfulness of evaluation nor an inverse of Gamma. It is a routine comparison of the two definitions in the item and the reused node, with the two transposes and their counits written explicitly, not a hidden new tensor lemma. Its text has 1,381 characters.

Step 3 uses `lem-sf-proper-open-projection-mate` for the entire displayed equation and its explicit final system clause, not its proof. Its finite coefficient hypothesis holds for A_n, and Step 1 verifies quasi-compactness. `lem-sf-open-tensor-normalization` identifies the two names for the open tensor comparison. `lem-coef-semilinear-derived-sections` explicitly supplies simultaneous system models, derived tensor and the adjunction transposes for unbounded complexes without flat quotient-transition assumptions. I checked its restriction on fiberwise internal Hom: we use no internal Hom here, so the cartesian-first-input qualification is irrelevant. The projection-mate node explicitly states the system equation before evaluation and for arbitrary unbounded inputs; consequently no conclusion is inferred from equality of evaluated arrows. I do not apply the bounded-constructible realization conclusion of `lem-sf-integral-compactification-system-realization` to arbitrary objects. Its role in the item's unchanged statement is to identify the intrinsic normalization; the actual unbounded tensor equality is the explicit system clause of the reused node.

I tested identity horizontal maps (the direct-image projection equation), identity proper maps (the open tensor equation), empty U, zero M or N, and a noncartesian clopen component s with nonempty complementary component. The normalization calculation uses identity on s(U) and zero on the other component, so it does not silently replace s by an isomorphism. The argument imposes no boundedness, Tor amplitude, normalization or etale-origin restriction. All proof steps have fewer than 2,000 characters; none hides a long uncited comparison. Every cited node has a verbatim statement quotation in citations.json; the complete projection-mate statement is quoted because its two coefficient clauses are both used. No new node needs a source/edge-case audit beyond the item.

## Unfinished work

None for the stage-1 split. Descendant nodes remain the existing DAG obligations. Delivery validation is performed by the required server dry run, followed by the normal delivery command.

The first dry run rejected one citation excerpt as shorter than its 40-character minimum. I replaced that excerpt with the full existing finite-type-over-Noetherian statement; the proof and its dependency remain unchanged.
