## Worker report

Item: lem-sfb-dominant-generic-differential-comparison. Group Q48. Stage 1 only; no Lean file, compiler, Lake command, repository write or direct git command.

### Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-dominant-generic-differential-comparison.json: preserved statement and statement dependencies; four complete proof steps; status split. Fresh Mathlib searches appended to the inherited searches. Blueprint placement clarified and same_as searched.
- citations.json: eleven entries, one per cited node per step; every quote was checked as a literal substring of the actual cited statement.
- report.md: this report. searches.jsonl is maintained by the required search command.

## New nodes

None: 0 new nodes and 0 new Mathlib leaves. The proof needs an existing general pullback-stalk theorem and routine arguments from existing definitions. There is no lemma restating a clause of the item.

## Attachments

None. Searching lean/WeilConjectures for the blueprint tag returned no declaration. Searches by generic/stalk differential terminology located AlgebraicGeometry/Curve/AdelicDifferentials.lean, notably genericValue_differentialsToGeneric_sectionsD, but that is a formula for one scheme's map into a generic sheaf, not a comparison for an arbitrary dominant morphism with both prescribed alpha isomorphisms. It does not supply every clause of this item under its hypotheses.

## WANTED

None. All the source passages used are available in literature/stacks-project/.

## Problems found and changes

The imported item was statement-only. Its statement is correct; no STATEMENT-DISPUTED correction is needed. In particular alpha_X and alpha_Y are hypotheses, not isomorphisms to be proved from smoothness. The source and target of beta must be related using the actual generic stalk homomorphism. I kept that map throughout, explicitly reversed the order of the tensor factors, and used arbitrary representatives of field germs rather than assuming every field element is a function on one fixed affine open.

The inherited blueprint.from.node is null. tools/blueprint_refs.py ancestor returns None for this item's existing created.item ancestry. I retained that provenance and clarified from.place, rather than inventing an imported ancestor. I read the latest blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3), and the DAG unit/chapter records. The comparison remains below the already recorded curve/alteration auxiliary route; it does not alter the unit or chapter route. The latest blueprint does not expand the auxiliary differential calculation itself.

## Searches and reuse

The sandbox initially contained only dispatcher markers, with no split, report or earlier search log. I read the item's four inherited Mathlib search records. I searched the whole DAG for 01UV, stalk-pullback-modules, module-stalk-pullback and dominant/generic terminology, and read the relevant statements. The general lemma lem-weil-pbc-module-stalk-pullback already states both the scalar extension isomorphism and the adjunction-unit germ formula. def-a1-relative-differentials-pullback-map already gives the required formula for df. lem-sfb-dominant-affine-germ-comparison includes an affine-preimage hypothesis not assumed here; it is unnecessary, since continuity proves the generic-point clause directly.

Blueprint searches with tools/blueprint_refs.py for stalk pullback, generic differential, 01UV, 0098 and differential pullback returned zero matching imported blueprint nodes. No duplicate was created.

All fresh Mathlib searches were run with batch2/msearch.py and are in searches.jsonl: LeanFinder with the dominant/function-field statement, Loogle with the KaehlerDifferential/stalk pair, grep with the generic differential pattern, LeanSearch with the naturality statement, then a second LeanFinder phrasing about pullback-module stalks and a second grep in RingTheory/Kaehler. All services returned results successfully. I read the hits; KaehlerDifferential.map and map_D (Mathlib/RingTheory/Kaehler/Basic.lean, definition around line 659 and theorem at line 668) describe the algebraic map, not this scheme/stalk comparison. The presheaf differential hits concern restriction maps, and ModuleCat.Tilde stalk hits concern affine associated sheaves. None is an exact match or one-line specialization giving the item with its beta and normalization formulas. The inherited records were retained and only actually run fresh queries appended.

## Not duplicates

No new nodes. Existing general tools and definitions are cited directly.

## Review by Q48

I read morphisms.tex Tag 01UV, lemma-functoriality-differentials, especially its final local-section characterization. It sends the pullback of da to the differential of the pulled-back function, exactly as used in Step 4. I also read sheaves.tex Tag 0098, lemma-stalk-pullback-modules and its proof: it identifies the module-pullback stalk with G_{f(x)} tensor O_{X,x}, using f-sharp_x, as needed in Step 2. I read morphisms.tex Tags 01RM and 0CC1, the generic-point image argument for dominance. For the elementary algebra I read the two cited DAG definitions of differential and tensor modules and the algebraic map/map_D source returned by the searches. There are no new-node sources to review.

Step 1 cites def-pc-integral-scheme for nonempty irreducibility, lem-sc-scheme-sober for existence and uniqueness of the generic points, def-sc-generic-point for closure of a singleton, def-weil-locally-ringed-space-morphism for continuity and the ring-sheaf map on germs, and def-weil-scheme-over-base for compatibility with k. The argument is explicitly by a closed inverse image: any closed set containing f(eta_X) contains the dense image, so f(eta_X) is generic. This uses no quasi-compactness, finite type or affine-preimage hypothesis. Integrality provides both unique generic points, and the stalks are the fields named in the statement.

Step 2 uses the statement of lem-weil-pbc-module-stalk-pullback, not a construction hidden in its proof. I opened that node and verified that it explicitly includes the unit-section germ formula s_y tensor 1 as well as the isomorphism. Its hypotheses allow any scheme morphism and any module sheaf, so G = Omega_{Y/k} and x = eta_X are legitimate. The remaining tensor flip and application of alpha_Y have an explicit inverse; the tensor definition supplies bilinearity and generation by pure tensors. No flatness or finite presentation is used. This node is an off-unit general tool and is declared in split_report.tool_uses, not in the maintainer-owned top-level tool_uses. The same declaration records the generic-point uniqueness tool.

Step 3 uses def-weil-pbc-kahler-differentials, whose statement gives both the derivation universal property and the quotient presentation by symbols da. It also uses def-weil-pbc-module-tensor-product, whose statement gives the bilinear universal property and pure-tensor generation. The k-linearity established in Step 1 makes d composed with phi a k-derivation; the balancing equality is written out. The generator conclusion follows from those presentations, so no unrecorded base-change or differential-localization theorem is being invoked.

Step 4 uses def-weil-pbc-module-stalk, which explicitly says every stalk element is a germ and that a module morphism acts on germs by its section map, and def-a1-relative-differentials-pullback-map, which explicitly gives df(f^* da) = d(f-sharp a). For every b in K I choose a representative on some neighbourhood of eta_Y; Step 1 ensures its inverse image contains eta_X. The two assumed alpha normalizations apply on exactly these nonempty opens. The displayed computation proves equality on 1 tensor db, and Step 3 supplies their L-span. It does not silently use a localization comparison or exchange the geometric stalk map with an unrelated field embedding.

I checked delivery-errors B–E: no new statement-only node hides a proof, no object or hypothesis is implicit in a new statement, no new duplicate or clause-node is introduced, and every cited fact is actually in the cited statement (C1/C4). The non-elementary stalk theorem is a node citation rather than an unexplained tag. The other steps are short explicit consequences of the displayed hypotheses and cited definitions; their elementary markings do not conceal a geometric or algebraic theorem. The four step texts are respectively 749, 821, 862 and 957 characters, so no step exceeds the long-step threshold. The only changes made during my reading were to expand the flip inverse, balancing relation, arbitrary-germ representation, and generator computation; the statement remained unchanged.

Small cases: for the identity, beta is the tensor unit comparison followed by alpha, and the formula gives the identity on differentials. An open immersion gives the same germ map on the shared function field. In characteristic p, the map t -> t^p on the affine line gives T(1 tensor dt) = 0; the statement permits this because no separability or nonvanishing assertion occurs. For Spec(k) both differential spaces vanish, and the zero-module isomorphism/formula is correct. For an imperfect ground field the derivations still vanish on k and the same Leibniz and balancing checks apply. There is no empty integral scheme to exclude and no dimension assumption has been introduced.

## Unfinished work

None in the one-level split. Dependencies remain existing nodes with their existing statuses. The required server dry run and delivery are recorded by the delivery command; independent mathematical review remains the maintainer's role.
