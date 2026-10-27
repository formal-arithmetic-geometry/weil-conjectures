# Stage-1 report: Q49

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-dm-field-etale-chart-quasifinite.json`: item, statement, split; not a Mathlib leaf.
- `dag/nodes/sec-six-functors-basics/lem-sfb-field-nonquasifinite-specialization.json`: new statement-only lemma, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-field-specialization-trdeg-drop.json`: new statement-only lemma, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-quasifinite-trdeg-comparison.json`: new statement-only lemma, unsplit; no Mathlib match.
- `citations.json`: an exact statement excerpt for each step/node citation.
- `searches.jsonl`: search-command output digests, retained verbatim.

## Attachments

None. Read-only searches of `lean/WeilConjectures/` by the item's blueprint tag, DeligneMumford/AlgebraicStack, etale charts, specialization and transcendence degrees did not find a declaration proving the item. Results about schemes and ring maps do not state these stack assertions. No sorry declaration was treated as a proof. No Lean was written or compiled.

## Literature requested

None; no WANTED document. The Stacks sources needed for all three new lemmas and the item are present.

## Corrections and scope

The item's statement, statement dependencies and source are unchanged. Its imported proof was empty. The hypothesis in the statement is discreteness of the point space of Z, rather than the stronger full intrinsic stack local-quasi-finiteness used in the statement of 06UC. Reading the actual proof shows that it uses only local finite type of the chart over k, discreteness of |Z|, and local quasi-finiteness of the two relation projections. The split supplies exactly those inputs without claiming an equivalence with the full intrinsic condition and without citing the parent atlas-test node (which would be circular).

The current blueprint read was `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3). It still follows constructibility for open direct images. The much longer inherited alteration/moduli creation chain is recorded in the original node. `blueprint_refs.py ancestor` returns None; new nodes preserve that explicit null ancestor and extend the actual inherited via chain. Whole-blueprint searches for discrete, quasi-finite over a field, locally quasi-finite, specialization, transcendence degree, 01TH, 06RU and 06RX found no duplicate of a new statement. No chapter or unit route was changed.

## Unfinished work

The three new nodes are deliberately statement-only and join the stage-1 queue. The item has a complete assembly proof. No supporting lemma is presented as already proved in Lean or Mathlib.

## Review by Q49

I read the proof of Stacks 06UC (`stacks-morphisms.tex`, lemma-locally-quasi-finite-over-field), rather than using its conclusion as a black box. I also read all of 01TH (`morphisms.tex`, lemma-quasi-finite-at-point-characterize), 06RU (`morphisms.tex`, lemma-dimension-fibre-specialization), 06RX and its chart interpretation (`spaces-morphisms.tex`, lemma-compare-tr-deg and definition-dimension-fibre), and the explicit common-field construction of 04XH (`stacks-properties.tex`, lemma-points-cartesian). The new 01TH consequence applies (3) => (1): in the absence of any nontrivial specialization every point is closed and has no distinct generization, so every point is quasi-finite. Its contrapositive is the new statement. The 06RU node is exactly assertion (3) over Spec k. The 06RX node specializes the comparison to a scheme target locally of finite type over k and quantifies over a chosen etale scheme chart of the source; this avoids an undefined residue field of an arbitrary algebraic-space point.

Step 1 uses the current statements of the chartwise smooth/etale calculus, stack finite-type calculus and DM etale-atlas calculus. The first explicitly says etale => smooth => locally finitely presented => locally finite type, the second explicitly gives composition of locally finite type DM-stack maps, and the third gives arbitrary etale base change. The relation is the algebraic space A x_Z A by representability of the given chart itself, so this requires no surjectivity. The base Spec k is a scheme, hence a DM stack, and the composite is a scheme morphism. The finite-type calculus explicitly identifies the stack and algebraic-space notions; on schemes it is the usual local finite type notion.

Step 2 cites the two new scheme statements under the local finite type hypothesis just established and the existing stack point-topology statement for continuity. Strict transcendence-degree drop applies because v and v' are distinct points in the same field fibre. In a discrete point space every singleton is closed, so continuity makes their images equal. No assertion that an etale map of stacks has discrete ordinary set fibres is used.

Step 3 is elementary from the item's definition of equality of point classes and the triples in the cited moduli-groupoid definition. I wrote the field extension and the isomorphism explicitly. The definition's statement really supplies the 2-fibre-product objects; I do not take the much stronger general point-surjectivity theorem from a definition. The elementary construction is exactly the proof of 04XH. This also avoids a duplicate new point-lifting node and the unrelated closed-substack assertions in lem-sfb-smooth-presentation-closed-subsets.

Step 4 uses the existing affine-etale-cover node, whose statement explicitly gives point-surjectivity, to choose W,w above r. It uses the existing etale-space-to-lqf statement on each projection R -> A; the target A is a scheme, as that node requires. The new comparison node is applied twice with the SAME W,w. Its only target finiteness hypothesis is A locally of finite type over k, established in step 1. Thus both residue transcendence degrees equal that of kappa(w). I checked that none of these cited statements depends on the item; in particular the parent lem-sfb-dm-lqf-atlas-test is not a dependency. Step 5 is only contradiction between an equality and a strict inequality. All cited statements were opened and every quoted substring checked against the actual current statement in citations.json. There is no non-elementary step over 2000 characters.

The two algebraic-space facts from the A1 unit are declared in split_report.tool_uses as generic chart tools, not as a replacement of the six-functor unit route. This is the report of the permitted tool uses, not an edit of the maintainer-owned top-level tool_uses.

I checked B through E of delivery-errors.md: new nodes have standalone hypotheses, definitions, correct Stacks tags/labels, statement-only payloads and logged searches. None repeats the item's clause: two concern only schemes over fields and one compares residues for a map of algebraic spaces without a discrete stack. No new source is SGA. Mathlib's locallyQuasiFinite_iff_isDiscrete_preimage_singleton concerns a scheme map with discrete scheme fibres, so it cannot prove that this chart has that property. The source lines were read; the search hits about Artinian schemes, Jacobson closed points and field tower identities do not give any of the three statements in one specialization. Search records contain only queries actually logged by msearch.py; old item searches from Q74 are retained unchanged as inherited evidence.

Small cases: the empty scheme makes both specialization statements vacuous (the failure hypothesis is false); a disjoint union of Artinian finite-type k-schemes has no nontrivial specialization and is locally quasi-finite, even without quasi-compactness. A^1_k exhibits the strict drop 1 > 0 from its generic point to a closed point. Nilpotents change neither of these facts. The comparison node holds for the identity, open etale charts, finite inseparable field extensions (both relative transcendence degrees zero) and non-surjective or empty charts. It does not claim that an arbitrary field-valued representative has the correct transcendence degree; that would be false after a transcendental extension. For the item, schemes Spec k and classifying stacks of finite etale groups satisfy the hypotheses, and the argument permits nonreduced dimension-zero charts. A^1_k as Z fails discreteness; B G_m is excluded by the DM/etale-chart conditions, so the familiar Artin-stack counterexample does not enter.

## Future proof notes for the new nodes

For the non-quasifinite specialization node, use 01TH (3) => (1) contrapositively globally as explained above. For strict drop use 06RU(3); its proof reduces to the finite-type algebra strict prime-specialization transcendence-degree theorem. For the chart comparison, apply the proof of 06RX to g composed with a chart W -> E: its residue-field extension over the image point is finite by quasi-finiteness, and transcendence-degree additivity gives equality over k. These are notes in this report, not proof payloads inside the unsplit nodes.

## Not duplicates

lem-sfb-field-nonquasifinite-specialization vs lem-a1-etale-affine-finite-fibre-refinement: requires a surjective etale morphism to an affine scheme and produces finite affine refinements; it does not infer a specialization from failure of local quasi-finiteness.

lem-sfb-field-nonquasifinite-specialization vs lem-weil-pbc-quasi-finite-at-point-isolated: only gives quasi-finite => isolated at a specified fibre point, not absence of a nontrivial specialization => quasi-finite.

lem-sfb-field-nonquasifinite-specialization vs lem-weil-pbc-isolated-fibre-point-base-change: preserves an already isolated point under base change, and asserts nothing about producing specializations.

lem-sfb-field-nonquasifinite-specialization vs lem-weil-pbc-isolated-fibre-point-quasi-finite-affine-pairs: requires an isolated point as input; it does not derive isolation or a specialization from closure/generization conditions.

lem-sfb-field-nonquasifinite-specialization vs lem-weil-pbc-proper-smooth-connected-fibre-dimension-loci: assumes proper smooth families with bounded connected geometric fibres and describes dimension loci; the new node concerns arbitrary locally finite type schemes over any field.

lem-sfb-field-nonquasifinite-specialization vs lem-weil-pbc-lft-over-field-isolated-point-residue-finite: assumes an isolated point and concludes its residue field is finite; it neither produces specializations nor says that all points are isolated.

lem-sfb-field-nonquasifinite-specialization vs lem-weil-pbc-isolated-fibre-point-residue-finite: concludes finiteness of the residue extension at an already isolated fibre point; the new conclusion is existence of a nontrivial specialization.

lem-sfb-field-nonquasifinite-specialization vs lem-weil-pbc-lqf-restriction-to-opens: assumes local quasi-finiteness and restricts it to opens; the new node assumes its failure.

lem-sfb-field-nonquasifinite-specialization vs lem-pur-parameter-chart-germ-criterion: requires a closed point on a Cohen-Macaulay finite-type scheme over an algebraically closed field and a prescribed parameter map; none of those additional hypotheses are available here.

lem-sfb-field-specialization-trdeg-drop vs lem-per-finite-type-dimension-function: the existing statement concerns dimension functions and immediate specializations under a universally catenary base; the new statement gives a strict residue transcendence-degree inequality for every nontrivial scheme specialization over a field.

lem-sfb-space-quasifinite-trdeg-comparison vs lem-per-regular-lci-geometric-calculus: that statement only treats Noetherian regular schemes and quasi-finite maps, whereas the new statement allows arbitrary algebraic spaces locally quasi-finite over a locally finite type k-scheme and arbitrary source charts.
