# Worker report — Q30

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-etale-chart-finite-fibre-transfer.json`: statement, split; statement unchanged. Four proof steps and twelve verbatim citation entries. Mathlib verdict: no exact match or one-line specialization.
- `citations.json`: one entry for every step/node citation, each quote checked against the live statement.
- No new nodes; no new Mathlib leaves. The sandbox initially contained no item, split, report, or search log; copied the live item and preserved all its inherited metadata and earlier searches.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact item tag, its id and finite-fibre/etale-chart notions. The geometric-fibre and finite-etale-sheaf results do not state this result for arbitrary algebraic spaces and non-quasi-compact covering schemes. Nothing is claimed finished on the basis of a sorry declaration.

## WANTED

None. All source inputs are in the local Stacks checkout. No restricted-source route is used.

## Corrections and source agreement

The live item was unsplit and had no proof. Its statement is exactly implication (1) to (2) of Stacks Tag 03JS (`decent-spaces.tex`, `lemma-U-finite-above-x`, lines 268–329), including the absence of quasi-compactness hypotheses on the covering schemes. No statement dispute or correction is needed.

The subtle input is Tag 03JA: it assumes a quasi-compact **source**, not a quasi-compact morphism. Thus the selected affine opens can map to arbitrary non-quasi-separated, non-quasi-compact covering schemes. The proof applies this existing bounded-fibre node directly, then makes explicit why its finite scheme fibres give finite point fibres. It never asserts that a map with quasi-compact source and arbitrary target is quasi-compact.

The source's last finite-set argument is expanded: for each selected open use the finite inverse image of the finite given fibre, and take its image in V. Joint surjectivity makes the union of those finite images equal to the fibre in V. One must not confuse the surjection from points of the sheaf fibre product with an equality of topological fibre products.

## Not duplicates

No new node was created, so there are no new/existing-node pairs to justify. Whole-DAG tag and concept searches found the exact existing inputs at Tags 03JA, 03H4, 03WT, 01IT, and 00E8. In particular the already split `lem-weil-pbc-lqf-qc-source-bounded-fibres` states the required generality and is reused. The space fibre-bound node with quasi-separated target is not used: that hypothesis is unavailable here. `tools/blueprint_refs.py search` was run for `finite above`, `etale finite`, `03JA`, `03JS`, `03H4`, `chart fibre`, and `finite fibres etale`; no blueprint declaration gives the item. Tag 03H4 was read as part of the source audit but is not a separate proof dependency, because the stronger jointly-surjective-base-change clause already supplies all point lifting needed.

## Route and blueprint

Read the chapter record `sec-six-functors-basics` and unit record `sk-thm-sf-ctf-stability`, the three levels in SETUP.md, and the current `literature/blueprint/latest/blueprint/sec-six-functors/_section.md` and `sk-thm-sf-kunneth-verdier/thm-sf-ctf-stability` statement/proof. The latest tree reorganized the old unit file, so read the current theorem's clause (iii), not an older snapshot. This item is a small scheme/space-topology prerequisite below the direct-image route; no unit or chapter route is replaced. The inherited ancestry chain has `from.node=null`; `tools/blueprint_refs.py ancestor` independently returns None. Retained that maintainer metadata and its detailed non-unspecified place rather than inventing an ancestor. Filled the split report and searched `same_as` (empty).

The split declares four generic tool uses: space-cover base change; unramified implies locally quasi-finite; open restriction of local quasi-finiteness; and quasi-compact-source bounded fibres. Each is a precise geometric input in the given Stacks proof; none replaces a higher unit step. Other imported inputs are Mathlib leaves or definitions.

## Mathlib searches

Ran the required msearch wrapper, recorded in `searches.jsonl`: LeanFinder with two distinct phrasings of chartwise point-fibre finiteness, LeanSearch for independence from the etale presentation, Loogle for `AlgebraicGeometry.LocallyQuasiFinite, AlgebraicGeometry.QuasiCompact`, and grep for `finite_preimage|finite_fiber|finite_fibre` in AlgebraicGeometry. All services answered successfully. Read the results and `Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean`, especially lines 163–184 (`finite_preimage_singleton` at 174), and the class and permanence discussion above. These give scheme morphism results, with quasi-compactness of the morphism for the finite-preimage declaration. They do not state presentation-independent point-fibre finiteness for algebraic spaces. Every newly appended search record uses the exact query logged by the wrapper. The five inherited searches remain untouched, as historical searches of the node's creator.

## Review by Q30

I read delivery-errors B–E in full (including the repeated historical B–E block) and checked the source and cited node statements, rather than inferring the cited content from titles.

For step 1 I opened `def-trf-algebraic-space` and `lem-trf-space-fibre-products-etale-covers`. The former explicitly says that representable etale means every scheme pullback is etale; applied to V -> X this proves P_i -> U_i is etale. The latter explicitly says that base change of a jointly surjective etale family is again such a family, so P_i -> V is jointly surjective, and its scheme clause applies. I read Spaces Tags 02X2 and 04T9 and Topologies on Spaces Tag 041F(3). No identification of point-set fibre products with scheme fibre products is assumed.

For step 2 I opened the three cited statements. The affine-opens-basis node gives an affine open at every point of every P_i. The open-map node says the image of **every** open is open, not just the total image, so it applies directly to these affines. The spectrum node explicitly states quasi-compactness of Spec R, hence of V and each W_j. I read their sources at Schemes 01IT (line 1952), Morphisms 03WT (line 8274), and Algebra 00E8 (line 3252). Finite subcover selection is the meaning of quasi-compactness; no separate finite-refinement node is needed. Repeated indices are allowed; no intersections of affine opens are taken.

For step 3 I opened all seven cited statements. The etale definition explicitly includes unramified, the 02V5 node concludes locally quasi-finite for an unramified scheme map, and the restriction node permits an arbitrary open of the source and the whole target. The 03JA node states finite scheme fibres for a locally quasi-finite map with quasi-compact source; all these hypotheses have been established for W_j -> U_i. I reread 03JA, including its finite-affine-cover proof (morphisms.tex line 15495), and 01TH(4)/02V5. The finite-morphism finite-fibres node supplies finiteness of the point set of the finite scheme over kappa(u), because Spec kappa(u) has one point by the affine-spectrum node. The scheme-fibre definition explicitly includes the homeomorphism onto the set-theoretic fibre. I also read the finite implies quasi-finite and finite-fibres source statements (02NU/02NH), and Schemes 01K1. Thus this step uses the actual clauses quoted in citations.json, rather than treating the finiteness of a fibre scheme as a set-theoretic assertion without justification.

Step 4 uses only steps 1–3 and finite-set operations: it writes the finite union, verifies both containments using the commuting square, and proves the desired equality. It is elementary and introduces no hidden geometric lemma. Empty original fibres contribute nothing; empty V allows n = 0. For nonempty V the chosen affine opens exist even when the original atlas members are non-quasi-compact or not separated. X has the point x, so no impossible empty-X case is invoked. Identity charts over Spec k and a cover consisting of many repeated charts give the expected finite singleton; removing affine/quasi-compactness of V would permit an infinite disjoint union over Spec k and is precisely why compactness is used. No control on U_i x_X U_i is required anywhere.

All proof steps are shorter than 600 characters. Every non-elementary input is a cited existing statement. No unsplit new statement, elementary duplicate node, relabelled item clause, axiom, Lean edit or compiler run is present. The source and target hypotheses were checked without adding quasi-separatedness. Verbatim citation substrings were checked when writing citations.json.

## Unfinished work

None in this one-level split. Dependencies remain the existing nodes; the required server dry run and delivery validate the assembled record.
