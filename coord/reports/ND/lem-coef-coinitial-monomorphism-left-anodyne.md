# Stage-1 report: lem-coef-coinitial-monomorphism-left-anodyne

## Files written

- dag/nodes/sec-six-functors/lem-coef-coinitial-monomorphism-left-anodyne.json: item, statement preserved, five proof steps, status split.
- dag/nodes/sec-six-functors/lem-coef-universal-cocone-restriction-right-anodyne.json: new statement-only prerequisite, status unsplit, no Mathlib match.
- citations.json: verbatim cited clauses indexed by step.
- searches.jsonl: actual msearch.py output records.

One new node, zero Mathlib leaves. No unit realization changed: this is not the unit's key statement.

## Attachments

None. I searched WeilConjectures/ of /home/ubuntu/weil-src-slopmaster2 for the exact blueprint tag, coinitial, cofinal and left/right-anodyne terminology. The hits concern ordinary scheme neighborhoods, not this quasicategorical assertion. No sorry-free project declaration states the item or the new recognition theorem. The upstream master is not evidence of completion.

## Wanted sources

WANTED: Jacob Lurie, Higher Topos Theory, Definition 4.1.1.1, Proposition 4.1.1.3(4), Proposition 4.1.1.8 and Theorem 4.1.3.1, printed pp.223-227 and 236-238, for both the item and lem-coef-universal-cocone-restriction-right-anodyne. The public HTT PDF at https://www.math.ias.edu/~lurie/papers/HTT.pdf was read through the web tool; no archive exists in the allowed literature tree. No download was made. The item proof_origin is agent: this is an explicit assembled reversal argument checked against those sources.

## Problems found and corrections

The item had a statement and searches but no proof. Its source route is correct. The existing lem-coef-infinity-cofinal-mono-right-anodyne requires the image to be full, so applying it would be unjustified. I instead used the existing comma criterion and added the independent universal cocone recognition theorem. That new node has a global diagram-restriction hypothesis, not the item's local contractible-comma hypothesis, and does not restate the item or an incoming-comma clause.

The shared DAG initially lacked the assigned file, but it appeared during the session's refresh. I used that record, retaining its statement, metadata and all historical searches. An initial delivery command entered the worktree queue before files existed; I interrupted that premature request and prepared the actual split before the final dry run. There was no push.

No statement dispute was found. No coefficient category, target, chapter, unit route or definition was changed. No forbidden source route is used.

## Unfinished work

The new recognition theorem is deliberately statement-only, as required for a one-level split. Its future split should connect the universal cocone characterization of HTT Proposition 4.1.1.8 to the right-fibration section test of Definition 4.1.1.1 and then the homotopy-lifting argument of Proposition 4.1.1.3(4). This is genuinely non-elementary infrastructure, not an omitted elementary calculation. The second reader must perform the independent reading and actual delivery.

## Not duplicates

lem-coef-universal-cocone-restriction-right-anodyne vs lem-coef-infinity-cofinal-mono-right-anodyne: the existing node assumes fullness and contractible arrow commas; the new node assumes universal cocone-category restriction equivalences and imposes no fullness.

lem-coef-universal-cocone-restriction-right-anodyne vs lem-coef-coinitial-monomorphism-left-anodyne: the item has local incoming join-comma hypotheses and concludes left anodyne; the new node has a universal cocone restriction hypothesis and characterizes right anodyne. The existing comma criterion is the separate nontrivial link between the hypotheses after reversal.

lem-coef-universal-cocone-restriction-right-anodyne vs lem-coef-infinity-cofinal-comma-criterion: the existing node derives universal cocone restriction from outgoing comma contractibility for arbitrary functors; it does not identify the right-anodyne class among monomorphisms. Neither statement subsumes the other in one line without the additional recognition theorem.

lem-coef-universal-cocone-restriction-right-anodyne vs lem-coef-infinity-cofinality-space-test: the existing node characterizes preservation of colimits by space-valued colimits and commas; it does not conclude membership in the horn-generated class. The new node has no space-colimit or comma clause.

lem-coef-universal-cocone-restriction-right-anodyne vs lem-coef-infinity-terminal-anodyne: the existing node tests the inclusion of a single terminal object by its mapping spaces; the new statement applies to all monomorphisms with a universal cocone restriction test.

Searches: whole DAG statements by cofinal/anodyne, cocone/restriction and the cited HTT numbers, plus blueprint_refs.py search cofinal, anodyne and cocone over all chapters; no blueprint duplicate was found. blueprint_refs.py ancestor confirmed prop-coef-integral-exceptional-adjoint. I read its current main-20261015 proof, paragraph 2, and the chapter and inherited biduality unit. The place and ancestry serve the existing operadic source-cell comparison below the derived coefficient adjunction; no upper route is replaced. No Stacks tag states this infinity-categorical theorem, so none is invented.

## Mathlib search review

For the new node I ran msearch.py with two LeanFinder phrasings, one LeanSearch phrasing, a Loogle conjunction and an AlgebraicTopology source grep. All five ran successfully. Their exact query text and returned records are in searches.jsonl and mathlib_searches. I read all returned signatures. They give ordinary categorical colimits/pushouts or Kan-Quillen cofibrations, generating horns and closure instances. Reading Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/Basic.lean:69-86 and CategoryWithFibrations.lean:35-106 confirms that J and anodyneExtensions use all horns. They do not give the right-horn or universal quasicategorical cocone recognition theorem. The item already carries equivalent genuine historical searches, which were read and retained rather than fabricated or repeated.

## Review by ND

I checked delivery-errors B through E with the records and HTT open. For the item I read HTT Theorem 4.1.3.1, its statement and proof, and Proposition 4.1.1.3(4); for the new node I read the exact universal cocone characterization in Proposition 4.1.1.8 and its relation to Definition 4.1.1.1 and Proposition 4.1.1.3(4). Crucially, the latter says inclusion of simplicial sets, not full inclusion. The new node introduces its universe, both quasicategories, the monomorphism, every target diagram, the actual restriction and its conclusion. It contains no proof sketch or hidden data definition.

Step 1 uses clause (4) of lem-coef-infinity-relative-cone-equivalence for opposites of quasicategories and reversal of slices, and def-cbc-enhanced-diagrams-cones for the realization quotient. I checked the join-block reversal, its projections, and the displayed barycentric-coordinate homeomorphism. This is an elementary explicit calculation from the cited definitions, not a homotopy-invariance assertion left unproved.

Step 2 uses lem-coef-infinity-slice-right-fibration for the slice projection. I checked that reversing the indices converts right horn lifting to left horn lifting and that both source and base are quasicategories. The definition in def-coef-infinity-fibrations says exactly what this assertion means. The statement of lem-cbc-left-fibration-equivalence-lift explicitly makes this left fibration an isofibration. Then lem-coef-infinity-isofibration-pullback-limit explicitly supplies the pullback in Cat_infinity for arbitrary g=i. Thus the strict comma in the hypothesis represents the homotopy comma in the existing criterion. This corrects the common gap of silently replacing strict pullbacks by homotopy pullbacks. The join model is the coherent category of arrows out of the fixed vertex, retaining all higher simplices, not a homotopy-category comma.

Step 3 first uses lem-cbc-simplicial-groupoid-localization with q:T->Delta^0. I read its full statement: a weak homotopy equivalence to a Kan complex universally presents diagrams inverting all edges, on their full mapping spaces. Since Delta^0 is Kan, it verifies that the commas are contractible also in the all-arrows-inverted convention. This explicit citation repairs a convention gap found in the final self-review. Step 3 then uses exactly the cocone-category conclusion of lem-coef-infinity-cofinal-comma-criterion, which I read in full. Its smallness and weak-contractibility hypotheses have been established in Steps 1 and 2. Its conclusion is explicitly the actual restriction over the target category, with no assumption that colimits exist. Step 4 uses the new recognition statement with A=K^op and B=L^op; all its hypotheses are now available. Step 5 uses precisely the weak-saturation definition in def-coef-infinity-right-anodyne. Reversal is an involutive automorphism, hence preserves each of the diagrams and retract equations in that definition, and the missing face index becomes m-r. This spells out the conclusion and its orientation.

Every step citation has a verbatim quote in citations.json. I read the statements themselves rather than relying on their proofs. The two off-unit citations are declared as generic tools in split_report.tool_uses: left-fibration equivalence-lifting supplies an isofibration property, and simplicial groupoid localization connects the two contractibility conventions. Neither replaces the unit's geometric route. The new node is not elementary: it contains the global recognition passage from diagram restriction to horn generation. I did not create nodes for order reversal, the realization homeomorphism, or closure transport because those calculations are written out in the item. No step exceeds 2000 characters.

Small cases checked: K=L and arbitrary identity j; L empty (then K is empty and j is an isomorphism); K empty and L nonempty (each comma is empty, so the hypothesis fails); {0} in Delta^1 (incoming commas are points, and it is Lambda_0^1); {1} in Delta^1 (the comma at 0 is empty, so the opposite orientation is excluded). For a nonfull example take K=Lambda_0^2, the nerve of the fork 0->1 and 0->2, inside L=Delta^2. This K is a quasicategory, each incoming comma is contractible (the last is the fork with initial vertex 0), and the inclusion is a left horn generator. Reversal gives Lambda_2^2, a right horn, testing the new theorem's lack of fullness. For the new right-anodyne recognition theorem, {0} in Delta^1 fails the universal cocone condition: a set-valued diagram with a nonbijective transition witnesses failure. Conversely {1} in Delta^1 satisfies that right-anodyne condition. Thus the incoming-comma test and the new right-anodyne recognition are correctly separated by opposites. Empty target cocone categories cause no issue: equivalence is required for the actual restriction, never by choosing a cocone from an empty category.

I also walked the full dependency graph from each proposed existing proof dependency to the item; none reaches the item. proof_deps is the union of step uses. B1-B10, C1-C8, D1-D5 and E1-E7 were checked: no unsourced non-elementary assertion remains in the item, no full-subcategory hypothesis was smuggled in, no ordinary cofinality theorem is substituted for quasicategorical cofinality, and no source tag is used as the meaning of a statement.

## Second reading by ND

I independently read the source PDF at HTT Theorem 4.1.3.1 (p. 236), Proposition 4.1.1.3(4) (pp. 223–224), Proposition 4.1.1.8 (pp. 226–227), Definition 4.1.1.1, and the cited local DAG statements. The item statement matches the source hypothesis by hypothesis: small quasicategories, degreewise injective map, the strict join slice, weak contractibility, and the left-horn saturation conclusion; the non-full-image clause is retained. The new node matches Proposition 4.1.1.8 together with Proposition 4.1.1.3(4): it states the universal coherent cocone restriction equivalence for every target quasicategory and diagram, with no fullness or colimit-existence hypothesis.

- Step 1: checked opposite quasicategories and the incoming-to-outgoing comma isomorphism against `lem-coef-infinity-relative-cone-equivalence` (4) and `def-cbc-enhanced-diagrams-cones`, including the realization reversal formula; the identity and empty cases agree. I repaired the wording so degreewise injectivity is obtained from the degreewise bijection of order reversal, rather than being attributed to an unstated clause of the cited node.
- Step 2: checked the slice right fibration, opposite left fibration, isofibration lift, and pullback-as-infinity-pullback against the four cited statements; the strict pullback is used only after the isofibration hypothesis is established.
- Step 3: checked the weak-equivalence-to-localization conversion against `lem-cbc-simplicial-groupoid-localization` and the cocone restriction conclusion against `lem-coef-infinity-cofinal-comma-criterion`; the conclusion is the actual coherent restriction functor and does not assume a colimit.
- Step 4: checked the reverse direction of the new recognition node against HTT Proposition 4.1.1.8 and the inclusion/right-anodyne equivalence; no fullness is introduced.
- Step 5: checked order reversal of horns and preservation of pushouts, transfinite compositions, and retracts directly from the right-anodyne definition; the index changes from `r` to `m-r`, giving precisely the stated left horns.
- New node: checked B1–B7, self-contained universes and objects, definition dependencies, exact HTT source place, statement-only form, blueprint ancestry, and all five recorded Mathlib searches. The returned Mathlib declarations concern ordinary or Kan–Quillen anodyne notions and do not state this quasicategorical recognition theorem; no duplicate DAG node or blueprint equivalent was found.
- Edge cases checked: identity inclusion; empty source and target; the two vertex inclusions in `Delta^1`; and the non-full horn inclusion `Lambda_0^2 -> Delta^2`, with the opposite right-horn orientation. No statement dispute or source error remains.

Changed only Step 1's attribution of degreewise injectivity and recorded that repair here. No statement, dependency, source, or citation quote was otherwise changed. I additionally ran LeanFinder with the fresh query "Cofinal simplicial inclusions characterized by restriction on categories of cones for every target"; all eight results concern ordinary categorical initiality/cofilteredness/cone constructions. The actual result is retained in searches.jsonl and the new node. Independent slopmaster2 keyword searches returned only scheme-neighborhood cofinality, and blueprint searches for cocone/anodyne found no duplicate. The final dry run is repeated after these search records were added.
