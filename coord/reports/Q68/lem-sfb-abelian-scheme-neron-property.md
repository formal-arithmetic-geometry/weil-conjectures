# Q68 — lem-sfb-abelian-scheme-neron-property

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-abelian-scheme-neron-property.json: unchanged statement; four-step split, source and Mathlib search records retained, five additional searches recorded.
- dag/nodes/sec-six-functors-basics/lem-sfb-proper-generic-map-big-open.json: new statement, unsplit; no full Mathlib match. A generic morphism into any proper target extends to an open containing the full generic fibre and all codimension-one points; the source is affine and smooth over the Dedekind open.
- dag/nodes/sec-six-functors-basics/lem-sfb-relative-weil-codimension-extension.json: new statement, unsplit; no full Mathlib match. Relative Weil extension for an already supplied fibrewise dense domain containing all codimension-one points, with a smooth separated group target that need not be proper or commutative.
- citations.json: full verbatim statements for every step/node citation.
- searches.jsonl and research/: actual msearch logs and unabridged returned hits, plus sandbox-only preparation scripts.

There are two new nodes and zero new Mathlib leaves. The existing Mathlib leaf lem-sfb-relative-separated-dominant-ext is reused.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint id and for Neron, Néron, abelian schemes and Weil extension found no declaration stating this item. The existing field-base Weil extension node does not state the relative theorem. No Lean file was written and no compiler or build tool was run.

## Wanted literature

WANTED: Bosch–Lütkebohmert–Raynaud, Néron Models, 1.2 Proposition 8 and Lemma 5, printed pp.13–15, and 4.4 Theorem 1, printed p.109, for lem-sfb-abelian-scheme-neron-property, lem-sfb-proper-generic-map-big-open and lem-sfb-relative-weil-codimension-extension. The named project PDF is absent. I read the primary-source scan at https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf, PDF pp.20–21 and 115, using text and page screenshots. I did not download it or write into literature/. Because the local source is absent, proof_origin.by is agent as the brief requires. No SGA source is used.

## What needed correction

The item had no proof. Its mathematical statement is correct and is retained verbatim. I removed the unused direct statement dependency def-weil-finite-type-morphism; properness already has its own definition dependency. In particular, no hypothesis on quasi-compactness or separatedness of X has been inserted.

The field-base lem-sfb-weil-extension-to-abelian-variety and lem-sfb-group-rational-divisorial-indeterminacy do not justify extension over a Dedekind base. Their hypotheses explicitly start with a field k, so using them at a closed fibre without a relative argument would leave the essential step unproved. The source's relative 4.4 Theorem 1 is the missing input. Its fibrewise-density hypothesis is stated explicitly, not silently inferred just from ordinary density.

The inherited blueprint ancestor chain returns null from tools/blueprint_refs.py ancestor. I retained the chain rather than inventing a blueprint ancestor. The places now identify BLR's actual proof and the auxiliary Néron-model branch underneath the current sk-thm-sf-ctf-stability-direct-images.proof.md paragraph (3). I read the current latest blueprint unit and direct-image proof and the DAG chapter/unit records. No unit or chapter record is changed.

## Not duplicates

lem-sfb-relative-weil-codimension-extension vs lem-sfb-weil-extension-to-abelian-variety: the existing node has a field base, integral separated finite-type smooth source, and an abelian-variety target; the new node has a relative Dedekind base and assumes a supplied fibrewise dense domain containing codimension-one points, allowing nonproper, noncommutative groups.

lem-sfb-relative-weil-codimension-extension vs lem-sfb-group-rational-divisorial-indeterminacy: the existing divisorial-indeterminacy theorem is over a field, not a Dedekind scheme. It cannot be specialized to the relative result; the target in the new node is also not required connected.

lem-sfb-proper-generic-map-big-open vs lem-sfb-rational-map-extension-valuation-point: the latter starts with an actual dense open and one valuation stalk on an integral Noetherian source. The new node starts with the whole generic fibre (which need not be open), permits a disconnected affine smooth source, and supplies one open with the complete generic fibre, every codimension-one point, and fibrewise density. Spreading and smooth Dedekind local geometry are additional assertions, not a one-line specialization.

lem-sfb-proper-generic-map-big-open vs lem-sfb-valuation-stalk-proper-target-extension: the latter assumes every stalk is a valuation ring and has a field base. Smooth affine schemes here can have arbitrarily large dimension and need not satisfy either hypothesis.

lem-sfb-proper-generic-map-big-open vs cor-nagata-conrad-proper-target-extension: that theorem changes the source by an admissible blow-up. The new statement keeps the source and extends only to a big open, including a specified whole generic fibre.

Neither new statement is a clause or restatement of the item. The proper-target input concludes only an open-domain extension and makes no group assumption; the relative Weil input starts with an open-domain map and makes no properness assumption. Their composition is the substantive proof in BLR. For example [x:pi] on A^1 over a DVR maps generically to P^1 and has an unresolved closed indeterminacy at (x,pi); the proper-target lemma does not claim to remove this codimension-two point. The group theorem supplies the additional mechanism needed for B.

## Mathlib and blueprint searches

Each new node and the item was searched by leanfinder twice with distinct phrasings, leansearch, loogle and grep through the required msearch.py command. The exact queries and complete output are in the JSON records and research/. All services answered. Returned hits describe rational-map representatives, spreading from a function field or stalk, smoothness and properness; none is a full match. In particular RationalMap.ofFunctionField supplies an initial rational map, not the relative group extension theorem or the full proper-target big-open statement. I read the relevant relative dominant equality theorem in Mathlib/AlgebraicGeometry/Morphisms/Separated.lean:295–313 and reused its existing DAG leaf instead of creating a new one.

Before creating the nodes I searched the whole DAG by titles, statements, Néron/Weil/rational-map/codimension/valuation terminology and read the candidate statements. I ran tools/blueprint_refs.py search for Néron, Weil extension, rational group, codimension group, proper rational, dominant separated, Weil codimension and proper generic open. Broad hits concern different coefficient or geometric assertions; none states the new facts. Direct searches of literature/blueprint/latest/blueprint found no relative Néron/Weil extension node. The new nodes have same_as=[] and the inherited null ancestor with their precise source places.

## Review by Q68

I read coord/delivery-errors.md B–E, including the duplicated retired-run copy, and checked the split against its mathematical requirements. Both new nodes introduce all objects and give definitions or definition-node citations for their notions: Dedekind means Noetherian integrally closed domain of dimension one; the relative group diagrams are written inline because def-sc-group-scheme is only over a field. Krull dimension, smoothness, separated/proper morphisms, affine spectrum, base change and residue fields point to their actual definitions. Both new nodes carry statements only, with empty proof/dependency lists, and actual Mathlib searches. They are non-elementary inputs, not elementary observations extracted as extra nodes.

For the item I read BLR 1.2 Proposition 8 (PDF p.21), including its proof: extend at generic points of closed fibres using DVR stalks and properness, spread the local maps, then invoke relative Weil extension, and use separatedness for uniqueness. For the first new node I read exactly this properness/spreading part, as well as Lemma 5 (PDF p.20); its use of smooth Dedekind local rings is the geometric reason both codimension-one and fibrewise-density conclusions hold. This part uses no group structure of the target, so the proper-target formulation is faithful. One can see the argument on a finite disjoint union of normal integral components of the affine smooth source: spread near the generic fibre, use the proper-target valuation extension at each remaining height-one point, and glue by uniqueness. Each closed-fibre generic point has a DVR stalk, so the resulting open meets every fibre component generically. This argument is recorded here, not hidden as a proof inside the new unsplit node's statement.

For the relative Weil node I read BLR 4.4 Theorem 1 (PDF p.115): the base is normal Noetherian, the source smooth, the target smooth separated, the map S-rational, and its domain contains codimension at most one. A Dedekind open meets those base hypotheses. The statement spells out S-rational as fibrewise density. It imposes neither properness nor commutativity and does not invent either hypothesis. Its specialization to Dedekind bases is enough for this split. I did not use the source's later applications or any SGA references.

Step 1 cites lem-sbc-finite-etale-generic-fibre-cover-density for exactly the reducedness and dominant generic-fibre projection it states, specialized with the identity étale map. T is integral by the hypothesis that it is a nonempty open of the spectrum of a domain. The relative separated dominant equality leaf says precisely that agreement after a dense-image map into a reduced source implies equality of morphisms with the same composite to the base. Properness supplies separatedness by def-weil-proper-morphism. Thus no absolute separatedness assumption on X or a target over a field is used.

Step 2 uses def-pc-scheme for an affine open cover and the local definition of smoothness to restrict to its members. It cites the proper-target new node for every conclusion it takes: the full generic fibre is retained, the local maps agree with the original f_E, the domain meets each fibre densely, and all local dimension at most one points are included. The target B satisfies its properness hypothesis. The affine cover may be infinite; no finite-type property of all X is used.

Step 3 cites the relative Weil node with exactly its hypotheses: same D and T, source U_i smooth, group B smooth and separated, the supplied domain fibrewise dense and containing every codimension-one point. Its extension equals the supplied map on V_i, and V_i contains the entire generic fibre, so the new map has generic restriction f_E on all of (U_i)_E. This last equality is an immediate restriction identity, not another unproved comparison.

Step 4 repeats Step 1 on each overlap, without assuming intersections of affine opens are affine. Smoothness is local on the source by its stated definition. The cited gluing node permits an arbitrary index set and gives existence and uniqueness of the glued scheme morphism; being over T and having generic restriction f_E are checked on the cover. These equalities are exactly the uniqueness part of that gluing node. Thus the argument includes non-quasi-compact and non-separated X and the empty source.

I checked edge cases: X empty; X entirely over the generic point; disconnected X; relative dimension zero; zero-dimensional B; and a generic automorphism of P^1 over a DVR. The last example confirms why properness alone is insufficient for global extension and why the group theorem is indispensable. No residue characteristic, completeness, excellence, geometric connectedness of X, or common finite cover of X is assumed. The two new nodes remain valid when some fibres are empty; fibrewise density is then vacuous.

For C4 I opened every cited node and copied its actual statement verbatim to citations.json, including all hypotheses. For C1 I checked that the only remaining elementary arguments are restricting local defining conditions, substituting the identity étale map, restricting equal morphisms, and using the locality clause of gluing; the extension results and equality principle are cited statements. All four steps are below 2000 characters (514, 615, 497, 777). There is no lemma hidden in a long step. The off-unit density and gluing statements are declared generic tools in split_report.tool_uses; neither changes the unit's proof route. No dependency points back to the item or a descendant that uses it.

## Unfinished work

No stage-1 assembly step is left unfinished. Proofs of the two new unsplit input nodes are future stage-1 items; this delivery intentionally does not split them. The missing local BLR copy is explicitly requested above.
