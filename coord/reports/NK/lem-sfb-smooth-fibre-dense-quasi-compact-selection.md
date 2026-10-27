# Stage-1 report: lem-sfb-smooth-fibre-dense-quasi-compact-selection

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-smooth-fibre-dense-quasi-compact-selection.json`: statement; split into five proof steps. Mathlib searches found no complete match. The original statement, statement dependencies, source, creation record and blueprint ancestry are retained.
- `citations.json`: one entry for every step/node citation, using the cited statement verbatim.
- `report.md`: this report. `prepare.py` is sandbox scratch work, not a delivery file.

New nodes: **0**. New Mathlib leaves: **0**. All geometric and topological inputs already have nodes.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and for fibrewise density, relative density, and quasi-compact selection. No declaration proves this item. In particular `Smooth.exists_etaleCover_factorization` in `WeilConjectures/AlgebraicGeometry/Morphisms/Slicing.lean` is the existing slicing input, not a declaration of the selection result.

## Wanted literature

WANTED: local copy of Bosch–Lütkebohmert–Raynaud, *Néron Models*, section 2.5 Lemma 3, printed pp.56–57, for lem-sfb-smooth-fibre-dense-quasi-compact-selection. The existing source record already requests it. I read the primary scan at https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf, PDF pp.62–63, through the web reader; no download or repository write was made.

The delivered proof is marked **agent-written**. It implements finite selection after the existing Stacks 0EY4 slicing theorem, rather than claiming that BLR itself contains this particular assembly. BLR's component-saturation argument motivated the selection, and the original statement agrees with its Lemma 3. All actual non-elementary ingredients are existing cited nodes with sources available locally.

## Problems found and changes

The item was unsplit, without a previous sandbox item or report. Its statement is correct, including the absence of quasi-compactness assumptions on S and U, and was not changed. The inherited blueprint ancestor is null: the ancestor command explicitly returns None, and the inherited via chain/place is retained. The current blueprint `latest/` slicing statement and the current unit statement/proof were read; the unit file in `dag/units/` is an older record, but this auxiliary geometric result changes neither version's six-functor route.

A naive finite-subcover argument inside U would assume exactly the compactness one is trying to obtain. Instead finitely many slicing charts cover X; inside each chart, finite selection takes place on its **affine base**, which is compact. The chart fibres are integral, so meeting each of them suffices for density. Images of the selected affine opens in X are compact and open, and their finite union is W.

I checked the complete DAG and imported blueprint for existing versions of the inputs, using whole-DAG statement searches, tags, names, and `tools/blueprint_refs.py search`. This found the slicing theorem, the smooth connected fibre integrality result, the étale fibre discreteness theorem, étale base-change and cover base-change, the affine basis, flat-lfp openness, spectrum compactness, and continuous-image compactness. None was duplicated. A graph traversal verified that the two substantial generic inputs do not depend on this item; the server checks remain authoritative.

The item has fresh logged Mathlib calls of all four kinds and two different semantic phrasings. Read the hits: dense domains and compact fibres do not select an open dense in every fibre, and the finite-affine-cover criterion assumes the open already compact. The inherited searches are retained. There are no new nodes whose searches need manufacturing or repeating.

## Not duplicates

No new nodes were created. The existing smooth section-component open and geometrically irreducible component nodes have stronger finiteness hypotheses than the original family; I did not apply them directly to that family or recreate them. The existing full slicing theorem already supplies the needed affine families without those extra global hypotheses.

## Review by NK

I read delivery-errors B–E whole and compared the source statements, the item and all five steps. I read BLR 2.5 Lemma 3 in the primary scan, and locally read Stacks `more-morphisms.tex` Tag 0EY4 (`lemma-cover-smooth-by-special`), the geometric-fibre argument of Tag 057J, `varieties.tex` Tag 056T, and `properties.tex` Tag 033M. These justify the chosen slicing/integrality inputs. I also read `morphisms.tex` Tags 02GL and 01UA, and checked the source places and statements of every other cited input. No SGA source is used.

Step 1 uses **sbc-lem-slicing** for every stated chart property: the two affine schemes, both étale maps, the smooth map with section and geometrically connected fibres. It uses **lem-weil-pbc-etale-morphism-open-map** for the open images, and the actual definition **def-weil-pbc-quasi-compact-scheme** to extract a finite subcover. No separatedness, compactness of S, or compactness of U is inferred. A finite subfamily with images covering X is still jointly surjective and étale.

Step 2 uses **lem-trf-smooth-connected-fibre-normal-integrality** only with the identity extension of the residue field and with the smooth geometrically connected chart map. Its nonemptiness convention is satisfied by the supplied section. **lem-weil-pbc-etale-scheme-base-change** makes the base-changed chart map étale, and **lem-weil-pbc-etale-fibre-discrete-separable-points** says that each point of the étale base fibre is an open copy of its residue-field spectrum. This supplies exactly the open inclusion of the individual chart fibre into the S-fibre. **def-pc-base-change** supplies the iterated fibre-product identification. The open-map theorem then applies to every nonempty open in that individual fibre. Its nonempty open image meets U_s by the item's hypothesis, so the inverse image of U is dense and nonempty in that chart fibre. This avoids assuming density is preserved by an arbitrary continuous map.

Step 3 uses **lem-weil-pbc-affine-opens-basis** to cover the inverse image of U by actual affine opens of the chart; **lem-pc-smooth-flat** supplies both hypotheses of **lem-weil-pbc-flat-lfp-open**. That theorem is about an open map, so restriction to each affine open does not require another smoothness theorem. Their images cover the affine base by step 2. Clause (iii) of **lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact** gives compactness of this base; no finiteness of the original affine cover is assumed. Selection makes B_i meet every fibre. The two-open intersection criterion of irreducibility proves density in each already integral fibre in one line, not as a new lemma.

Step 4 again uses the étale open-map statement, clause (iii) of spectrum compactness for each selected affine, and **lem-weil-pbc-continuous-image-quasi-compact** with the underlying continuous chart map. I wrote the finite-union compactness argument explicitly. **def-weil-open-immersion** supplies the open subscheme structure. Factoring B_i through W is restriction to an open containing its image: restrict its existing structure-sheaf map; there is no invalid factorization through a general locally closed or closed subscheme.

Step 5 uses **lem-weil-pbc-etale-covering-base-change**, whose statement explicitly supplies joint surjectivity after base change, and not just preservation of étaleness. A point over a test open gives a point t in the discrete base fibre. The open identification already established in step 2 and the density in step 3 give a point in the selected affine union mapping into the test open. The factorization of step 4 maps it into W_s. Thus the argument proves density on the ordinary S-fibre itself, rather than only on a chart or after an unspecified field extension.

Every step/node entry in `citations.json` quotes the actual statement in full, so it is possible to inspect each use without relying on the cited node's proof. Every non-elementary fact in this assembly is one of these inputs; finite subcover selection, finite-union compactness, restriction of morphisms to opens, and the open-set criterion for density are written explicitly. No step exceeds 2000 characters, and no independent unsupplied comparison lemma is hidden in a long step. The substantial off-unit inputs are declared as generic tools in `split_report.tool_uses`; they do not replace any six-functor step.

Edge cases checked: X empty (choose the empty open); an empty S; empty fibres at some points; disconnected and non-geometrically-connected original fibres (the slicing charts, not X, have connected fibres); arbitrary imperfect residue fields (étale fibre discreteness and the integral-fibre input apply); non-quasi-separated X; and a non-quasi-compact base or original open. Compactness is used only for X, each affine T_i, and each selected affine A. A section guarantees that every chart fibre whose base is nonempty is nonempty. No statement dispute was found.

## Unfinished work

No mathematical split obligation remains. Required dry run and push are performed after this report is written; the delivery command's final result determines the one-line answer.
