## Worker report

Files written:
- dag/nodes/sec-deligne-laumon-a1/lem-per-filtered-category-pseudococones.json: item, split with six explicit steps; no statement change.
- dag/nodes/sec-deligne-laumon-a1/lem-per-filtered-pseudocone-representative-transport.json: one new statement-only unsplit lemma; no Mathlib match.
- citations.json: verbatim statements backing every citation of every item step.

Attachments: none. I searched the project's WeilConjectures source by the item tag, pseudococone/pseudocolimit terminology, and filtered-category terminology. FilteredColimitFunctorDescent handles strict compatible functors only. StageSystem.Const.descFunctor handles a pair category indexed by a directed preorder, not the present arbitrary filtered index and strict object-quotient model. Neither proves every clause of this item.

WANTED: none. The source for the representative calculus is present. The new coherent extension is explicitly agent-written rather than falsely attributed to a Stacks lemma.

What needed correction: the imported node had no proof. Tag 004A concerns splitting a fibred category and does not supply the claimed functor-category universal property. I did not use it as that theorem. I made the representative comparison isomorphisms explicit and extracted their independence as the single new lemma. The item statement is correct and unchanged. The existing initial-functor theorem, applied to opposite diagrams and Sets^op, gives final reindexing without inventing a second cofinality node.

Unfinished work: none for this one-level split. The new transport lemma is intentionally unsplit. Its argument is recorded below for its next worker; it is not hidden in its statement or proof fields.

## Review by N9

I read coord/delivery-errors.md B–E, the stage-1 contract, the chapter/unit records, and the current latest blueprint's lem-per-artin-gabber-affine-curve statement and proof. This is a categorical detail below the recorded completion-continuity ancestry, not a replacement of the unit's perverse-sheaf argument. I read categories.tex Tag 04AX (section-directed-colimits), including eventual equality and the actual parallel-arrow equalization axiom; Tag 04E7 (lemma-cofinal) and the dual initial-functor formulation; and Tag 004A (lemma-fibred-strict). The last concerns fibred categories, so I retained its historical source entry but explicitly did not invoke it. The proof_origin is agent, because the pseudococone extension is not verbatim in any of these tags. The new lemma's source says exactly the same limitation.

For Step 1 I opened lem-weil-pbc-filtered-colimit-categories: its object and arrow set descriptions give representatives, and its equality assertion is available to the new lemma. The new lemma states canonical transport between any two representatives of the same object and its square for equal complete arrows. Those are exactly the two facts Step 1 uses to descend the displayed formula. No claim that A_i are strictly compatible is made. The endpoints in each transport and each A_i(f) agree as written.

For Step 2 I checked clause (2) of the same finite-category-colimit node: a composable pair and its composite require only finitely many objects, arrows, and composition relations, so they lift simultaneously. The transport lemma gives inverse middle transports and the transition formula. I checked the comparison direction: lambda_i : F v_i -> A_i and lambda_i = theta_a lambda_k D(a). That is precisely the arrow equation for a map from an identity-comparison pseudococone to (A,theta). Thus this step proves essential surjectivity itself; the new node does not state descent or any clause of the item's conclusion.

For Step 3 the category-colimit node gives equal representatives after transitions and representation of every arrow. The identity-comparison modification equation says the components agree after a transition, so it proves component independence and ordinary naturality exactly as used. I also opened lem-trf-fully-faithful-ess-surj-equivalence and cite its actual criterion in Steps 3 and 6. Functor categories may be larger than the original universe, so I explicitly enlarge the containing universe before applying this criterion. There is no restriction to finite target categories. Postcomposition commutes with restriction as an equality of functors, including on transformations, hence gives the requested vertex naturality without a noncanonical choice of inverse.

For Step 4 I opened lem-weil-pbc-initial-functor-limit, which states both transfer of the limiting property and the canonical limit isomorphism for an initial functor. For w^op its initial test at j is the opposite of (j downarrow w); nonemptiness and connectedness survive opposites. The diagrams to which I apply it land in Sets^op, so their limits are exactly the set colimits needed, not limits in Sets. Both source index categories are small filtered as required by the category-colimit construction. Bijections of complete arrows and objects induce the displayed functor, and finite lifting in K checks compositions. This even gives an isomorphism, which suffices for the stated equivalence.

Step 5 writes the actual identity q v^K_k = v_wk, including arrows and transformations, so compatibility is not asserted with a bare word 'transport'. It needs no additional theorem. Step 6 constructs Q using Steps 1–3 for the pseudococone u_j e_j with comparisons u_k(sigma_a^-1). The signs and directions agree with the definition. I checked fullness and faithfulness using clause (3) of the finite-category-colimit node for E and for D. Every later stage still has an equivalence e_k. Conjugation by sigma supplies the necessary endpoint identification E(a)e_j x -> e_k D(a)x. Equality is only requested after a further transition, not at the original stage. Thus the proof works for nonfaithful transition functors and for comparisons that are not identities.

For the new lemma I checked its content against 04AX and wrote down the proof obligation explicitly: two witnesses k,a,b and k',a',b' can be mapped into a common stage, then the two maps out of i and the two maps out of j are equalized by successive postcompositions. The resulting composite arrows out of i and j agree for the two witnesses. Under one postcomposition c, coherence reads theta_ca = theta_a theta_c,D(a)x. Substituting into theta_cb,y theta_ca,x^-1 cancels the common theta_c because D(a)x = D(b)y. This proves independence. For a triple of representatives choose two equality witnesses for adjacent pairs; common-target them and equalize the two maps out of the middle stage. The common middle theta cancels, proving T_qr T_pq = T_pr. Identity and the single-transition formula follow by choosing identity witnesses. Equal arrow representatives become equal complete arrows at one stage; applying naturality of theta_a and theta_b gives exactly the square stated. The rho identity is the same cancellation with rho_i theta_a = eta_a rho_k D(a); applying H to the formula proves postcomposition. This is a genuine independent coherence lemma, not two-line elementary work, and its statement contains neither a descended functor nor a functor-category equivalence nor reindexing/invariance.

I tested singleton J (T is identity and the item reduces to the ordinary functor category), empty D(i) (no representative choices or component equations are required), an empty target A (the same existence restrictions hold on both sides), nonempty constant diagrams with nontrivial coherent comparison isomorphisms, and filtered categories with distinct parallel arrows (independence needs equalization, which the new lemma explicitly retains). There is no assumption that transitions are inclusions or faithful. In the reindexing clause K is nonempty because it is filtered. All uses are acyclic: the new node depends only on the preexisting category-colimit construction and definitions, never on this item. No proof step is over 2000 characters. The new node has no proof, proof dependencies, or disguised proof sketch. The JSON has single TeX escapes after parsing, complete objects and hypotheses, and filled blueprint provenance and same_as.

Mathlib searches were run solely with msearch.py and read as returned. One initial Loogle query used the nonexistent NatIso identifier; I recorded its diagnostic and ran the corrected NatTrans query. Semantic hits concern Types colimit equality, ordinary ColimitPresentation, or site DescentData, not representative transport with coherent category-valued comparison isomorphisms. I read the returned ColimitTypeFiltered, EventuallyConstant and DescentData source. Their hypotheses/conclusions do not specialize in one line to the new lemma. Searches for the item likewise do not state the functor-category equivalence or its two invariance assertions. Every new-node query is present verbatim in searches.jsonl, with the actual response metadata retained in mathlib_searches.

## Not duplicates

The whole DAG and imported blueprint were searched by pseudococone, Grothendieck construction, filtered 2-colimit, coherent cocone, common stage, and coherent Hom. No blueprint node states the new transport lemma. In particular the directed-preorder model and its evaluation-invariant lemma have a different index type and only fixed-endpoint transition assertions.

lem-per-filtered-pseudocone-representative-transport vs lem-a1-directed-ring-cocone-recognition: this existing statement concerns Recognition and functoriality of directed ring colimit cocones; it has no coherent category-valued functors or theta-conjugated representative transports.

lem-per-filtered-pseudocone-representative-transport vs lem-a1-ring-inverse-image-underlying-sets: this existing statement concerns Underlying sets of ring-valued inverse image, with its unit; it has no coherent category-valued functors or theta-conjugated representative transports.

lem-per-filtered-pseudocone-representative-transport vs lem-trf-commutative-monoid-filtered-colimit-underlying: this existing statement concerns Filtered colimits of commutative monoids have underlying set colimits; it has no coherent category-valued functors or theta-conjugated representative transports.

lem-per-filtered-pseudocone-representative-transport vs lem-trf-filtered-ring-log-pushout: this existing statement concerns Filtered ring colimits commute with fixed-monoid unit pushouts; it has no coherent category-valued functors or theta-conjugated representative transports.

lem-per-filtered-pseudocone-representative-transport vs lem-trf-filtered-varying-prelog-pushout: this existing statement concerns Filtered prelog pushouts with varying monoids and rings; it has no coherent category-valued functors or theta-conjugated representative transports.

lem-per-filtered-pseudocone-representative-transport vs lem-sfb-compatible-root-quotient-colimit: the existing statement is Colimit of the explicit compatible-root quotient; it does not assert independence of theta-conjugated transport between equal object representatives for arbitrary filtered J.

lem-per-filtered-pseudocone-representative-transport vs lem-sfb-localization-presented-colimit: the existing statement is Localization preserves a presented algebra colimit; it does not assert independence of theta-conjugated transport between equal object representatives for arbitrary filtered J.

lem-per-filtered-pseudocone-representative-transport vs lem-sfb-filtered-two-colimit-diagonal-equality: the existing statement is Diagonal Hom classes detect eventual equality at a later stage; it does not assert independence of theta-conjugated transport between equal object representatives for arbitrary filtered J.

lem-per-filtered-pseudocone-representative-transport vs def-sfb-simultaneous-root-tower: the existing statement is The canonical simultaneous-root diagram over an arbitrary set of positive orders; it does not assert independence of theta-conjugated transport between equal object representatives for arbitrary filtered J.

lem-per-filtered-pseudocone-representative-transport vs lem-sfb-filtered-two-colimit-common-stage-images: the existing statement is Simultaneous common-stage representatives and their comparison images; it does not assert independence of theta-conjugated transport between equal object representatives for arbitrary filtered J.

lem-per-filtered-pseudocone-representative-transport vs lem-sfb-presented-ring-colimit-geometry: this existing statement concerns Faithful flatness, ind-etaleness and spectrum limit of a presented ring colimit; it has no coherent category-valued functors or theta-conjugated representative transports.

lem-per-filtered-pseudocone-representative-transport vs lem-pc-filtered-colimit-commrings-elementwise: this existing statement concerns Filtered colimits of commutative rings, elementwise; it has no coherent category-valued functors or theta-conjugated representative transports.

lem-per-filtered-pseudocone-representative-transport vs lem-per-filtered-category-pseudococones: the existing item concludes a functor-category equivalence and two invariance properties; the new lemma proves only explicit transport identities for equal representatives, and has none of these conclusions.

lem-per-filtered-pseudocone-representative-transport vs lem-weil-pbc-filtered-colimit-sets-elementwise: the existing statement is Elements of a filtered colimit of sets; it does not assert independence of theta-conjugated transport between equal object representatives for arbitrary filtered J.

lem-per-filtered-pseudocone-representative-transport vs lem-weil-pbc-colimit-constant-connected-diagram: the existing statement is The colimit of a constant diagram over a connected (e.g. nonempty filtered) category; it does not assert independence of theta-conjugated transport between equal object representatives for arbitrary filtered J.

lem-per-filtered-pseudocone-representative-transport vs lem-weil-pbc-colimit-site-abelian-stage-image-refinement: the existing statement is Finite stage-image expressions have forward-stage representatives; it does not assert independence of theta-conjugated transport between equal object representatives for arbitrary filtered J.

lem-per-filtered-pseudocone-representative-transport vs lem-weil-pbc-filtered-colimit-algebras-elementwise: the existing statement is Elements of a filtered colimit of commutative algebras come from a stage; it does not assert independence of theta-conjugated transport between equal object representatives for arbitrary filtered J.

lem-per-filtered-pseudocone-representative-transport vs lem-weil-pbc-filtered-colimit-categories: the existing statement is The filtered colimit of a system of categories; finite diagrams and morphisms come from a stage; it does not assert independence of theta-conjugated transport between equal object representatives for arbitrary filtered J.

lem-per-filtered-pseudocone-representative-transport vs lem-weil-pbc-etale-limit-affine-stage-eventual-zero-tail: the existing statement is Finite-stage detection on affine tail; it does not assert independence of theta-conjugated transport between equal object representatives for arbitrary filtered J.

lem-per-filtered-pseudocone-representative-transport vs lem-weil-pbc-etale-limit-reindex-transition-coherence: the existing statement is Reindexing preserves inverse-image transition coherence; it does not assert independence of theta-conjugated transport between equal object representatives for arbitrary filtered J.

lem-per-filtered-pseudocone-representative-transport vs lem-weil-pbc-finite-type-ring-map-factors-filtered-colimit: this existing statement concerns Maps from a ring of finite type over Z into a filtered colimit of rings factor through a stage; it has no coherent category-valued functors or theta-conjugated representative transports.

lem-per-filtered-pseudocone-representative-transport vs lem-weil-pbc-filtered-colimit-category-list-equality: the existing statement is Finite object and arrow lists agree at a common refinement; it does not assert independence of theta-conjugated transport between equal object representatives for arbitrary filtered J.

lem-per-filtered-pseudocone-representative-transport vs lem-weil-pbc-filtered-colimit-finite-iso-lift: the existing statement is Finite isomorphisms lift above fixed stage objects; it does not assert independence of theta-conjugated transport between equal object representatives for arbitrary filtered J.

lem-per-filtered-pseudocone-representative-transport vs lem-weil-pbc-filtered-colimit-fiber-operations: the existing statement is Identity and composition on filtered arrow fibers; it does not assert independence of theta-conjugated transport between equal object representatives for arbitrary filtered J.

lem-per-filtered-pseudocone-representative-transport vs def-weil-pbc-filtered-colimit-hom-fibers: the existing statement is Hom fibers in the filtered arrow colimit; it does not assert independence of theta-conjugated transport between equal object representatives for arbitrary filtered J.

lem-per-filtered-pseudocone-representative-transport vs lem-weil-pbc-etale-limit-affine-stage-tail-colimit: the existing statement is Cohomology comparison is a colimit on the affine cofinal tail; it does not assert independence of theta-conjugated transport between equal object representatives for arbitrary filtered J.

lem-per-filtered-pseudocone-representative-transport vs lem-weil-pbc-filtered-colimit-modules-criterion: this existing statement concerns Elementwise criterion for a cocone of a filtered diagram of modules to be a colimit; it has no coherent category-valued functors or theta-conjugated representative transports.

lem-per-filtered-pseudocone-representative-transport vs lem-weil-pbc-filtered-colimit-category-structure: the existing statement is The category structure induced on the filtered object colimit; it does not assert independence of theta-conjugated transport between equal object representatives for arbitrary filtered J.

lem-per-filtered-pseudocone-representative-transport vs lem-weil-pbc-etale-limit-affine-stage-eventual-zero: the existing statement is Finite-stage detection of zero with one affine stage; it does not assert independence of theta-conjugated transport between equal object representatives for arbitrary filtered J.

lem-per-filtered-pseudocone-representative-transport vs lem-weil-pbc-filtered-colimit-category-iso: the existing statement is Invertible representatives from lifting finite functors; it does not assert independence of theta-conjugated transport between equal object representatives for arbitrary filtered J.

lem-per-filtered-pseudocone-representative-transport vs lem-weil-pbc-filtered-colimit-fiber-laws: the existing statement is Category axioms for filtered arrow fiber operations; it does not assert independence of theta-conjugated transport between equal object representatives for arbitrary filtered J.

lem-per-filtered-pseudocone-representative-transport vs lem-weil-pbc-filtered-colimit-category-finite-lift: the existing statement is Finite object and arrow lists lift with relations; it does not assert independence of theta-conjugated transport between equal object representatives for arbitrary filtered J.

lem-per-filtered-pseudocone-representative-transport vs lem-weil-pbc-colimit-site-finite-kan-arrow-lift: the existing statement is Finite Kan arrow diagrams lift simultaneously above their stage; it does not assert independence of theta-conjugated transport between equal object representatives for arbitrary filtered J.

lem-per-filtered-pseudocone-representative-transport vs lem-weil-pbc-filtered-colimit-category-finite-functor-lift: the existing statement is Construct a finite functor from finite-list lifts; it does not assert independence of theta-conjugated transport between equal object representatives for arbitrary filtered J.

lem-per-filtered-pseudocone-representative-transport vs lem-weil-pbc-filtered-colimit-category-descent: the existing statement is Finite-diagram and Hom descent from the object and arrow colimits; it does not assert independence of theta-conjugated transport between equal object representatives for arbitrary filtered J.

lem-per-filtered-pseudocone-representative-transport vs def-weil-directed-colimit-abelian-groups: this existing statement concerns Directed colimit of a directed system of abelian groups; it has no coherent category-valued functors or theta-conjugated representative transports.

lem-per-filtered-pseudocone-representative-transport vs lem-sfb-coherent-cocone-evaluation-invariant: that lemma is indexed by a preorder and checks a fixed common-stage Hom transition; this lemma has arbitrary filtered J and establishes independence between different equality witnesses of object representatives.

## Dry-run repair

The first dry run rejected a grouped bracket citation in the new statement. I changed it to one bracket per node, preserving the statement and dependencies, and updated the verbatim citation quotes.
