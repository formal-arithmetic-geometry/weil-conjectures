# Stage-1 delivery: lem-sfb-algebraic-setoid-space

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-algebraic-setoid-space.json`: statement, split into six steps, no Mathlib match. The statement and its five statement dependencies are unchanged.
- No new nodes; zero Mathlib leaves. `citations.json` contains an exact statement excerpt for each of the 13 step/node citations. `searches.jsonl` records the five additional actual Mathlib searches, whose entries are preserved in the item. `write_split.py` is sandbox-only working material.

## Attachments

None. Searched the actual read-only `lean/WeilConjectures/` library by the item tag, algebraic-stack/algebraic-space names, automorphism and stack-in-setoids concepts. There is no declaration for this theorem. The setoid hits concern torsors and unrelated categorical constructions. The existing Sheaf definitions of algebraic moduli stacks are vocabulary, not a proof of this item.

## WANTED

None. All sources needed here are present under `literature/stacks-project/`.

## Corrections and findings

There is no statement dispute: the assumption concerns every test scheme, including nonreduced schemes, exactly as required for a stack in setoids. The original empty proof is now a proof following Tag 04SZ. Its class-sheaf equivalence and atlas transfer are written out instead of hiding the omitted proofs of Tags 0432, 0458 and 04TC in new nodes. Existing `lem-sfb-etale-smooth-atlas-fppf-descent` supplies the necessary 076V bridge from the project's etale-stack definition to fppf descent, and existing `lem-sfb-fppf-space-atlas-bootstrap` supplies 04S6. Neither is restated as a new node. Scheme smoothness gives flatness and local finite presentation by the existing `lem-pc-smooth-flat`.

The inherited blueprint ancestor was null. `blueprint_refs.py ancestor` reports None because the ancestry terminates at the creation record naming the Lean module `Sheaf.SixFunctors.CtfStabilityDirectImages`, rather than a DAG id. I repaired `from.node` to the genuine imported node `det-thm-sf-ctf-stability-direct-images`, already explicitly named in `from.place`, and retained the full existing via chain and place. This is the same repair already made and reviewed on the shared definition `def-sfb-stable-pointed-moduli-groupoids`. I read the latest blueprint's direct-image statement and proof: paragraph (3), Rj_* preservation, is the ancestor of the inherited alteration/curve-moduli/Quot input. No unit or chapter route was changed. The item is not the unit's key node, so no unit record is changed.

## Unfinished work

None for this one-level stage-1 split. Existing cited nodes retain their independent status; no Lean was written or compiled. Delivery checks and push are performed by the required delivery tool after this report is written.

## Not duplicates

No new nodes. Whole-DAG searches by the relevant source labels, Tags 0432, 0458, 04TC, 04S6 and the isomorphism-class/sheaf/atlas concepts found the existing fppf-atlas bootstrap and etale-to-fppf descent nodes. Whole-blueprint searches for setoid, algebraic stack, sheaf of isomorphism classes, representable diagonal, smooth cover and 04SZ found no blueprint node stating this item. These searches avoided creating duplicate prerequisites.

## Mathlib search assessment

The inherited Q85 search records are preserved. Five actual additional searches were run through msearch.py for Q17 and this item: two LeanFinder formulations, a Loogle Stack/AlgebraicSpace pattern, a source grep, and LeanSearch. All services answered; none is marked unavailable. I read every result. The first LeanFinder returned local Zariski representability by schemes, affine schemes and their category; the second returned sheafed spaces and manifold structure groupoids. LeanSearch returned affine/subsingleton schemes, etale scheme morphisms and scheme-isomorphism tests. These have neither the algebraic-stack object nor the arbitrary smooth algebraic-space atlas of this theorem. Loogle and source grep returned zero hits. Thus none is an exact match or a one-line specialization.

## Review by Q17

I read Stacks `algebraic.tex`, Tag 04SZ, proposition-algebraic-stack-no-automorphisms, including its proof of (1) implies (3). It constructs the sheaf of isomorphism classes, carries the smooth scheme atlas to that sheaf, and applies the flat-lfp bootstrap. I also read `stacks.tex`, Tag 0432, whose proof is omitted; the delivery writes out the sheaf and equivalence arguments it omits. For the atlas comparison I read `algebraic.tex` Tags 0458 and 04TC and wrote the actual test-scheme bijection rather than citing these unnamed results as black boxes. I read `bootstrap.tex`, Tag 04S6, theorem-final-bootstrap, conditions (3) and (4), and `criteria.tex`, Tag 076V, lemma-stacks-etale. For smoothness I read `morphisms.tex`, Tags 01VE and 01VF, the locally-finite-presentation and flatness conclusions. There are no new-node sources to audit.

For step 1, I opened both cited node statements. The algebraic-stack definition really includes effective etale descent, algebraic-space diagonal, and a smooth surjective atlas on all scheme tests. These are precisely the hypotheses of the fppf-descent node, whose conclusion really gives both fppf object descent and the fppf sheaf condition for isomorphisms. The upgrade is needed because the project's definition uses the etale topology, while the bootstrap theorem uses fppf sheaves.

For step 2, I checked the fibred-groupoid definition's cartesian-lift property, and the class functor on arrows over an arbitrary base map. If a and b are two isomorphisms, b^-1 a is an automorphism, so uniqueness follows from the item's hypothesis, not merely from a geometric-point condition. Existence of an arrow over a base map is exactly existence of an isomorphism with the corresponding pullback. Quotienting objects by isomorphism therefore gives a fully faithful, essentially surjective functor over schemes. A choice of representatives is harmless: unique arrows enforce functoriality and the comparison coherence. This is a few-line argument from the fibre definitions, so no new equivalence lemma is created.

For step 3, I reopened the fppf-descent statement and the fppf-site definition. Matching classes give unique overlap isomorphisms; uniqueness forces the cocycle, so the cited effective descent applies. Local isomorphisms between two gluings glue by the cited sheaf-of-isomorphisms assertion. Both existence and uniqueness of a sheaf section are proved. No local-to-global equality is asserted without that descent input.

For step 4, I opened the actual 2-fibre-product definition and the atlas definition. An object on a test V is a pair of maps to U and T with an isomorphism in X(V). The hypothesis on all V makes that isomorphism unique whenever it exists. Thus forgetting it identifies the atlas pullback, over T and compatibly with every restriction, with the ordinary sheaf pullback. This checks precisely what Tags 0458/04TC accomplish here, without introducing a broader transfer lemma or assuming in advance that F is algebraic. In particular, no circular application of a theorem for algebraic-stack morphisms to the not-yet-algebraic F occurs.

For step 5, I read the scheme-as-algebraic-space definition, the complete one-sentence smooth-flat node, and the entire bootstrap statement. The algebraic-stack definition makes every etale scheme-chart composite V -> T smooth; the smooth-flat node supplies flatness AND local finite presentation for that actual composite. These are exactly the chartwise properties of the bootstrap node, and the projection is still the smooth surjective projection furnished by the atlas. For EVERY s in F(T) there is a representative x, so the scheme-test hypothesis is global, not just local or true on field points. The source U is a scheme, and the existing scheme-as-space definition gives its actual Yoneda sheaf as an algebraic space; no new object is substituted. The bootstrap gives all of algebraic-space representability, including the representable diagonal and etale atlas, rather than requiring those conclusions as hypotheses. The off-unit smooth-flat citation is declared as a generic tool use in split_report, with no replacement of a unit step.

For step 6, the algebraic-space statement defines maps as natural transformations. The displayed evaluation-at-id formula and its explicit inverse show Hom(T,R)=F(T), with naturality. This identifies h_R with the discrete class category constructed in step 2, and composing its equivalence gives the required equivalence over S and the isomorphism-class bijections. Thus the final conclusion includes every clause of the item.

I checked the edge cases: the empty base and empty test scheme (empty-cover descent gives the unique class); a representable scheme or algebraic space (the class presheaf is the original sheaf); disconnected/nonreduced tests (all arguments use the actual test scheme and no reduction); and BG for a nontrivial group scheme, including infinitesimal groups (excluded because the hypothesis is on every test scheme). In particular, restricting the automorphism hypothesis to geometric points would invalidate the uniqueness argument; the statement does not do that. No finite-type, quasi-separatedness, nonempty, field, or Noetherian assumption entered the proof.

I checked delivery-errors B through E against the actual files. There are no new nodes, hence no statement-only violations, new unstated notions, duplicate clauses, fake leaf claims or searches. All sources use their checked Stacks labels/tags. Every cited node's statement is quoted verbatim in citations.json; every non-elementary theorem used is one of the named existing descent, smooth-flatness or bootstrap nodes. The remaining elementary steps contain their actual arguments. Proof dependencies are exactly the union of the step citations; the candidate added dependency closures were searched and do not lead back to this item. No proof step exceeds 1000 characters, so there is no long step hiding an untracked lemma. No SGA source is used.
