# Worker report

## Files written

- `dag/nodes/sec-smooth-base-change/lem-sbc-flat-composite-fibre-dimension-at-point.json`: item split, statement unchanged, four proof steps.
- `dag/nodes/sec-smooth-base-change/lem-sbc-composite-fibre-local-models.json`: new statement-only unsplit geometric lemma; no Mathlib match.
- `dag/nodes/sec-smooth-base-change/lem-sbc-transcendence-degree-tower.json`: new Mathlib leaf, `trdeg_add_eq`, TranscendenceBasis.lean:546, with universe-lifted version at 537.
- `citations.json`: entire verbatim statements of all cited nodes, indexed by step.

## Attachments

None. Searches in WeilConjectures for the item id and pointwise/composite fibre dimension found no project declaration giving the item. The source audit of the imported item is `none`. The master reference is not used as evidence of a finished proof.

## WANTED

None. All sources used are in the local Stacks checkout.

## Errors and changes

The imported statement agrees with Morphisms Tag 02JS's flat equality case. No statement correction is needed. Its empty proof is expanded along the source's route: local fibre rings, the flat local dimension formula, the dimension-at-a-point formula, and transcendence-degree additivity. In self-review I removed two draft dimension children because the existing `lem-kun-dimension-formula` and `lem-weil-pbc-flat-height-formula` already provide the required tools. New unsplit nodes have statements only, no proof sketches. The new geometric node contains no dimension equality, so it does not restate a clause of the item.

The finite-type-over-field formula and dimension finiteness are generic tools from the Kunneth unit; open-subspace dimension invariance is a generic topological tool from the proper-base-change unit. These are declared in split_report.tool_uses and do not change the universal curve test route.

## Not duplicates

lem-sbc-composite-fibre-local-models vs lem-weil-pbc-proper-fp-permanence: that node gives composition permanence, including local finite type, but no induced fibre stalk map, quotient or residue-field identifications.

lem-sbc-composite-fibre-local-models vs lem-weil-pbc-finite-over-separated-finite-type: that node composes a finite map with a separated finite-type map; the new lemma assumes neither finiteness nor separatedness and identifies fibre stalks.

lem-sbc-composite-fibre-local-models vs lem-weil-pbc-lft-base-change: that node supplies local finite type after base change only; it does not give the closed fibre of a stalk map or pointwise flatness.

lem-sbc-composite-fibre-local-models vs lem-pod-separated-finite-type-base-change: that node gives separated finite-type permanence, with stronger hypotheses, and no fibre stalk identifications.

lem-sbc-composite-fibre-local-models vs pqf-def-locnoeth: that node defines locally Noetherian and notes its permanence; it supplies no stalk/closed-fibre comparison.

lem-sbc-composite-fibre-local-models vs pqf-lem-locnoeth-lft: that node gives locally Noetherian sources over locally Noetherian targets; it says nothing about the closed fibre of the induced local map.

lem-sbc-composite-fibre-local-models vs lem-weil-pbc-finite-type-over-noetherian: that node gives Noetherianity for finite-type morphisms over a Noetherian base; here the original base is arbitrary and the conclusion is a fibre-stalk description.

lem-sbc-composite-fibre-local-models vs lem-weil-pbc-finite-algebra-noetherian: that node assumes module finiteness and proves ring Noetherianity only; the new lemma is about locally finite type scheme fibres and their local maps.

lem-sbc-composite-fibre-local-models vs lem-weil-pbc-graded-finiteness-cohomology: that node concerns cohomological finite generation of graded modules under proper pushforward, not fibre stalks.

lem-sbc-composite-fibre-local-models vs lem-pc-flat-module-descent-preorder: that node descends module flatness along a directed inverse system of schemes; it has no composite-fibre closed-stalk description.

lem-sbc-composite-fibre-local-models vs lem-pc-tensor-pullback-flat-proper-support: that node treats globally flat finitely presented modules with proper support under pullback; the new node assumes flatness only at one point and identifies fibre stalks and their closed fibre.

lem-sbc-composite-fibre-local-models vs lem-sc-effective-cartier-affine-dimension-drop: that node gives a dimension drop for a nonzero Cartier equation in an integral finite-type algebra; the new node states no dimension equality and assumes neither integrality nor an equation.

lem-sbc-composite-fibre-local-models vs lem-weil-pbc-fibre-ring-local-ring-iso: the existing result identifies the local ring of an algebraic tensor-product fibre with a quotient. The new result identifies the actual scheme fibre stalk maps for a composite, pointwise flatness, compatible residue fields and finite-type neighbourhoods. Its scheme-to-ring identifications require work beyond a one-line specialization of the ring result.

lem-sbc-transcendence-degree-tower vs def-kun-transcendence-degree: the existing node defines the degree; its search record mentions trdeg_add_eq, but its statement does not assert the tower identity.

## Review by NU

I read Morphisms Tag 02JS (lemma-dimension-fibre-at-a-point-additive), including its reduction through 02FX and 00ON. Its hypotheses are exactly two locally finite type maps and flatness at the source point for the equality. I read the statement and proof of 02FX, Schemes 0HA1 (lemma-local-ring-fibre), Morphisms 01T3 and 01T4 (composition and base change of local finite type), 01T6 (locally Noetherian source), 01U8 (pointwise module flatness under base change), Algebra 00ON, and Fields 030H. The last source gives the exact tower equation, whose Mathlib source I read at TranscendenceBasis.lean:537–550.

The new local-model statement is verified as follows, recording the proof for the next worker without splitting that child. Set R=O_{S,s}, D=O_{X,x}, E=O_{U,u}. Tag 0HA1 gives A=D/m_sD, B=E/m_sE and C=E/m_xE. The induced A-to-B map is local; its closed fibre is (E/m_sE)/(m_x/m_sD)(E/m_sE)=E/m_xE. If D-to-E is flat, its quotient base change A-to-B is flat by 01U8. There is no use of flatness at other points. Local finite type for the composite follows from 01T3, and its fibres, and those of the two original maps, are locally finite type over their residue ground fields by 01T4. Taking finite-type affine neighbourhoods and 01T6 gives Noetherian local stalks. The quotient descriptions preserve the original residue fields, and functoriality preserves the field tower. This proves a structural lemma, not the additive dimension assertion.

Step 1 takes precisely these structural conclusions from the new local-model statement. Step 2 applies the existing flat-height statement to A and B, which are Noetherian; the chosen prime is m_B and its contraction is m_A by locality. The existing node states the needed equality dim B_q=dim A_p+dim(B_q/pB_q), so there is no appeal to its proof or to a definition of flatness for a dimension result. Step 3 takes the exact formula dim_z=dim O_z+trdeg from lem-kun-dimension-formula; its finite-type-over-a-field hypothesis holds on the supplied affine neighbourhoods, even though the whole fibre need not be quasi-compact. The open-subspace node states exactly equality of dimension at the point when passing to the whole fibre. The finite-type dimension-finiteness node ensures the arithmetic uses finite numbers. Step 4 cites the new tower leaf for the compatible residue-field maps. It merely substitutes the equalities already obtained and regroups sums, without subtraction. The citations file copies the actual statements of every node cited in these steps.

The statements of all same-tag nodes listed above were opened; none gives the new structural conclusion. Blueprint searches included 02JS, dimension formula, fibre local ring, fibre stalk, flat local, transcendence degree and 030H. Only lem-kun-dimension-formula was a relevant formula, and it is reused. Project Lean searches by id and dimension terminology supplied no attachment. Mathlib candidate readings show Flat.stalkMap and base-change instances concern global Flat, whereas the new structural lemma handles a pointwise-flat stalk map and the closed fibre comparison; fibre point declarations do not supply that comparison. Search records contain exactly the logged queries/results; unavailable LeanSearch calls are recorded as unavailable.

Small cases: identity a gives A=B and closed fibre C=kappa(x), of dimension zero; the final equality reduces to dim_x X_s=0+dim_x X_s. For projections between affine spaces the closed fibre quotient removes the intermediate coordinates as expected, and dimension adds. At generic nonclosed points the transcendence-degree terms cannot be omitted (e.g. the generic point of affine one-space has stalk dimension zero but topological dimension at the point one); the tower calculation retains them. Empty schemes cause no problem because the item first supplies u. No reducedness, algebraic closedness, smoothness, globally flat map, finite presentation, or Noetherianity of S was added.

## Unfinished work

Only the geometric child remains unsplit, as required for a one-level split. The tower child is a verified Mathlib leaf. A second reader must review and deliver; this worker does not push.

## Second reading by NU

- Item statement: read Morphisms 02JS, lemma-dimension-fibre-at-a-point-additive, lines 5396–5422; the two locally finite type hypotheses and pointwise stalk flatness give precisely the asserted equality. PASS; no statement dispute.
- Step 1: opened lem-sbc-composite-fibre-local-models and Schemes 0HA1, lemma-local-ring-fibre, plus Morphisms 01T3/01T4/01T6/01U8. It supplies exactly the local flat Noetherian map, closed fibre, affine neighbourhoods and compatible fields used. PASS; no globally flat or Noetherian-base hypothesis is smuggled in.
- Step 2: opened lem-weil-pbc-flat-height-formula and Algebra 00ON, lemma-dimension-base-fibre-equals-total. Its equivalent localized formula applies at the maximal ideal because the map in Step 1 is local. Localizing local rings at their maximal ideals and replacing the quotient by C are elementary identifications. PASS.
- Step 3: opened lem-kun-dimension-formula, lem-kun-dimension-finite-type and lem-weil-pbc-dimension-at-point-open-subspace. Their finite-type hypothesis holds on the affine fibre neighbourhoods; their statements give the three exact formulas and finiteness. No global quasi-compactness is assumed for a fibre. PASS.
- Step 4: opened lem-sbc-transcendence-degree-tower and Fields 030H, lemma-transcendence-degree-tower. Compatible field maps from Step 1 give the stated tower equation; substitution and associativity/commutativity prove the conclusion without cancellation of infinite quantities. PASS.
- New node lem-sbc-composite-fibre-local-models: checked every clause against 0HA1, 01T3 (lemma-composition-finite-type), 01T4 (lemma-base-change-finite-type), 01T6 (lemma-finite-type-noetherian), and 01U8 (lemma-base-change-module-flat). With D=O_{X,x}, E=O_{U,u}, the quotients are A=D/m_sD, B=E/m_sE, C=E/m_xE; the image of m_A generates m_xE/m_sE, so B/m_AB=C. The flat map is the base change of D→E along D→A. Quotients by ideals contained in the maximal ideals preserve residue fields. This is a genuine geometric preparation lemma, with no dimension assertion; its scheme-stalk and finiteness content is not a two-line consequence of the existing ring-only fibre lemma. B1–B7 PASS after defining local map inline and supplying all source labels.
- New node lem-sbc-transcendence-degree-tower: read Fields 030H and Mathlib/RingTheory/AlgebraicIndependent/TranscendenceBasis.lean:537–550. trdeg_add_eq states the sum in the reverse order and orientation; symmetry and commutativity give the node. Field injections provide both FaithfulSMul hypotheses; the composite algebra supplies IsScalarTower. lift_trdeg_add_eq handles differing universes. B1–B7 PASS, verified Mathlib leaf.

Independent duplication checks: searched the DAG for all source tags and fibre-local-ring/tower vocabulary, and searched the whole blueprint for “local ring fibre” and “transcendence degree tower” (zero matches). Opened the relevant existing ring-fibre lemma, local-dimension formula, polynomial-chart fibre-stalk lemma, flat closed-fibre generalization lemma, and composition/base-change/Noetherianity nodes; none states either new result in full. The geometric child is neither a clause nor a restatement of the additive dimension item. Independent Mathlib searches used quotient/fibre/maximal-ideal vocabulary and a direct trdeg_add_eq Loogle query; actual results are in searches.jsonl and copied into the new nodes. The former yields projection/residue-field constructions only; the latter confirms the leaf. Read-only searches of slopmaster2 and archived master gave no matching finished project declaration; master sorry declarations were not treated as proofs.

Edge cases checked: identity a gives B=A and C=kappa(x), making the equality tautological; a tower of fields gives all stalk dimensions zero and exactly the transcendence-degree identity; affine-space projections in relative dimensions 0 and 1 give the expected coordinate quotients and additive dimensions. At the generic point of affine one-space the stalk dimension is zero and point dimension one, so the retained transcendence-degree term is essential. Empty schemes admit no supplied u. The zero ring cannot occur as a stalk at a point. Nilpotents do not affect the quotient computation and no reducedness is required.

Changes: defined “local” inline in the new structural statement, added the precise labels beside its source tags, appended independent genuine search records, and regenerated affected verbatim citations. The first worker's Review by NU and other sections remain in place. No proof route or item statement was changed.

Dry-run correction: I initially removed split_report.tool_uses under C8, but the dry run rejected the resulting unrecognized cross-unit dependencies. Reading tools/review_split.py:99–100 showed the explicit later human decision permitting worker declarations in split_report.tool_uses for reviewer judgment; these are not maintainer approvals in the top-level tool_uses field. Restored the three justified requests. The finite-type dimension formula and finiteness are generic tools needed for 02JS's 02FX route; open-subspace invariance is already Lean-closed. No maintainer approval field was written.
