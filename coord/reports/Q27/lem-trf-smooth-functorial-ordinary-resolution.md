# Repair of the ordinary-resolution split

## Files written

- dag/nodes/sec-trace-formula/lem-trf-smooth-functorial-ordinary-resolution.json: statement, split; statement and statement dependencies unchanged; three-step assembly (1787 characters).
- dag/nodes/sec-trace-formula/lem-trf-embedded-to-intrinsic-smooth-resolution.json: statement, unsplit; no Mathlib match. Conditional passage from a synchronized embedded algorithm to intrinsic ordinary resolution and arbitrary smooth comparison on embeddable schemes (old Steps 1–3).
- dag/nodes/sec-trace-formula/lem-trf-synchronized-resolution-zariski-descent.json: statement, unsplit; no Mathlib match. Conditional stagewise descent from finite affine covers, regularity and cover independence (old Steps 4–5).
- dag/nodes/sec-trace-formula/lem-trf-descended-resolution-smooth-comparisons.json: statement, unsplit; no Mathlib match. Conditional descent of smooth comparisons from subordinate covers and coherence/nondeletion (old Steps 6–7).
- citations.json: a literal statement quotation for every node used by every assembly step.
- searches.jsonl: actual msearch.py records, including each new node's natural-language queries, Loogle and Mathlib grep.

## Attachments

None. I searched lean/WeilConjectures for the exact item blueprint tag and ordinary resolution, desingularization, embedded resolution and synchronization vocabulary. The desingularization declarations found there concern Popescu ring-map smoothing, not a characteristic-zero ordinary blowup resolution assignment. The item also has the recorded theorem in lean/Sheaf/AlgebraicGeometry/SmoothFunctorialOrdinaryResolution.lean:80–82, but it ends in sorry; it is not an attachment. No Lean file was changed.

## Wanted literature

WANTED: Bierstone, Milman and Temkin, Q-universal desingularization, Asian J. Math. 15 (2011), 229–250, Theorem 6.1, its Addendum and section 6.3, for the existing embedded-resolution input and its invariant synchronization. This is the preexisting wanted reference, not a new claim to have read that paper. ILO VIII 2.3.11 and 2.3.13 identify it explicitly. The three new nodes are conditional reductions from a given assignment, not additional assertions that this embedded algorithm exists.

## What was wrong and what this repair changes

The return (dedicated handoff at e2a95534abdca96856ae1c3b80c5b78fb624dc06) requires distributing the former 8220-character proof among at least two comparable new tasks, retaining every argument, while reducing the item's assembly to at most 3000 characters. The sandbox initially contained only dispatch markers, no node, report or search log. I copied the current repository node, read the handoff in coord/returns/Q27.md and the original Q125 report, and verified the seven step texts against the return's lengths. The read-only node contains the returned seven-step proof and unchanged theorem signature; I preserved all metadata, the statement and statement dependencies. No git command was run.

The work is now distributed over three conditional lemmas, not relabeled as one new resolution-existence theorem. The first accepts an already-given synchronized embedded algorithm and handles only globally embeddable schemes; it must still prove the ordinary blowup/strict-transform identification, embedding independence, standard-smooth lifting, and local-to-global comparison. The second assumes only a given labeled assignment compatible with open immersions, and proves existence and uniqueness of its global Zariski descent; it does not construct embedded resolution or assert general smooth functoriality. The third assumes both an embeddable assignment with smooth comparisons and its already-descended global towers, and proves the descent and coherence of comparisons. None asserts the unconditional statement of the item. These three tasks can be proved independently under their explicit hypotheses. They preserve ordinary blowups, extended ideal sheaves, synchronization labels, and no constant-relative-dimension hypothesis.

The old proof is allocated as 3682, 2367 and 2171 characters respectively. Every original step is copied verbatim below under its assigned task. That material is handoff guidance in this report, not a proof or proof sketch in a new node's statement. Each new node has status unsplit, proof [], proof_deps [], proof_origin null. Nothing is claimed proved about these new tasks. The parent proof merely instantiates their hypotheses and forgets auxiliary labels.

No statement dispute or source error was found. In particular I have not introduced a normalization, restricted the global inputs to separated schemes, assumed affine overlaps, or replaced invariant labels by independently renumbered local stages. The historical alteration branch recorded by blueprint.from is preserved. The current unit sk-i-curve-zero uses contracting correspondences; this assigned descendant is not its key node. No unit, chapter, target, or route was changed.

## Searches and source readings

For the item I reused its recorded original searches rather than pretending to rerun old searches. For every new node I ran msearch.py with that node's id in the LeanFinder and LeanSearch plain-language queries and read the returned hits. Those give two different phrasings. I also ran a valid Loogle name-fragment query and a separate Mathlib-source grep for each task; exact query strings and actual result summaries are in each node's mathlib_searches and searches.jsonl. No search was invented. All services answered. LeanFinder hits concern smooth charts, affine-cover refinements and pullback maps. LeanSearch also found Scheme.Cover.gluedCover, instIsIsoFromGlued and glueMorphisms; these glue already-specified schemes/morphisms but do not prove synchronized ideal descent, the common finite label list or cover independence. None is a one-line specialization proving a new node. Loogle and the task-specific blowup/resolution regexes gave no hits. No Mathlib leaf is asserted.

Before naming the nodes, I searched the whole DAG by synchronization, embeddable, labeled towers, resolution gluing/descent, and smooth ambient comparison, including statements (not only ids). I ran blueprint_refs.py ancestor and whole-blueprint searches for resolution, descent, blowup, embedded, synchronized resolution, blowup descent, and ordinary resolution. The broad matches are unrelated derived resolutions and generic blowup constructions; the focused searches give no blueprint statement for these reductions. The only relevant existing ordinary-resolution objects are the assigned parent, the embedded algorithm, and its invariant-calculus input; the latter two do not supply these conditional intrinsic descent reductions. I reused the definition def-trf-labeled-embedded-resolution instead of adding a duplicate definition.

I read the available ILO PDF, Exposé VIII 2.1.1–2.1.9 (ordinary blowups, strict transforms, contractions and flat pullback), 2.3.1, 2.3.4–2.3.5 (resolution, functoriality and the disjoint-union synchronization warning), and 2.3.10–2.3.13 (characteristic-zero algorithm, centers and varying relative dimension). For new node 1 the relevant source is 2.1.3(ii), 2.1.9 and 2.3.11–2.3.13; for node 2 it is 2.1.9 and 2.3.5(ii); for node 3 it is 2.1.9, 2.3.4 and 2.3.5(i)–(ii). These places motivate the conditional reductions; the expanded arguments are the earlier agent's, not separately named ILO theorems. There is no Stacks tag for characteristic-zero functorial desingularization. The source fields say this precisely rather than inventing a tag. For the retained local-lifting argument I also read Stacks morphisms.tex lemma-smooth-locally-standard-smooth (01V7), algebra.tex lemma-standard-smooth (00T7), and smoothing.tex lemma-lift-once (07CK). The latter whole theorem assumes nilpotence, but the reused quotient-lift node explicitly states the equation-lifting subargument for an arbitrary ideal; the new conditional lemma does not assert the whole 07CK theorem without that hypothesis.

## Not duplicates

lem-trf-embedded-to-intrinsic-smooth-resolution vs lem-trf-embedded-resolution-ambient-comparison: the latter gives an embedded algorithm and only ambient-smooth comparisons; the former assumes that data and derives intrinsic arbitrary smooth comparison on embeddable schemes by standard-smooth lifting.

lem-trf-embedded-to-intrinsic-smooth-resolution vs lem-trf-hilbert-samuel-resolution-invariant-calculus: the latter provides an invariant and maximum-stratum properties, not the arbitrary intrinsic morphism comparison or ordinary-tower reduction.

lem-trf-embedded-to-intrinsic-smooth-resolution vs lemma-nagata-strict-transform-ambient-closed: the latter identifies one strict-transform blowup; the former is a conditional algorithmic reduction using that identification at every stage.

lem-trf-synchronized-resolution-zariski-descent vs lem-trf-functorial-log-blowup-etale-descent: saturated log blowups and strict etale maps are different data; this task is descent of ordinary ideal blowup towers on reduced rational schemes with synchronized labels and all finite affine-cover comparisons.

lem-trf-synchronized-resolution-zariski-descent vs lem-per-normalized-blowup-tower-etale-descent: the existing theorem requires normal separated quasi-excellent inputs and normalizes every blowup; the new node allows nonnormal nonseparated reduced finite-type inputs and glues ordinary towers supplied by a rule, including synchronization and independence of cover.

lem-trf-descended-resolution-smooth-comparisons vs lem-trf-smooth-functorial-ordinary-resolution: the former assumes global towers already descend a given assignment and asserts conditional comparison descent; it supplies neither those towers nor an embedded algorithm. The parent proves unconditional existence by assembling all three tasks and the existing embedded input.

lem-trf-descended-resolution-smooth-comparisons vs lem-trf-synchronized-resolution-zariski-descent: tower/ideal existence and cover independence are distinct from descent of arbitrary smooth-map comparisons and the identity/composition/deletion laws.

## Review by Q27

I reviewed the repair with the original seven steps, the ILO sections above, every new statement, and all statements cited by the assembly open. Step 1 uses lem-trf-embedded-resolution-ambient-comparison for an existentially supplied E with a common ordered label set, smooth ambient comparisons, intrinsic embedding comparison, regular centers and the empty input. Its statement gives exactly those data, in agreement with def-trf-labeled-embedded-resolution, which I also opened. The new embedded-to-intrinsic lemma assumes that assignment, not the conclusion of the parent. It returns A on the entire embeddable class with the precise smooth and open comparison clauses that Steps 2 and 3 require. The standard-smooth quotient lift, affine smoothness equivalence, smooth composition, smooth-flatness and flat blowup comparison are arguments assigned to that unsplit task, not hidden assertions inside the assembly.

Step 2 uses only the new synchronized Zariski-descent statement. I checked that A from Step 1 has a common L, finite increasing labels, coherent regular centers, regular last level, open-immersion contraction with ideals and a trivial empty input. The descent statement supplies a global R for all reduced finite-type rational schemes with no separatedness assumption, preserves the full label list on a surjective affine-cover disjoint union, gives every center and final regularity assertion, and has transitive cover comparisons. Thus Step 3 can use those actual conclusions, not facts guessed from its future proof. The nonemptiness assertion concerns the whole lifted cover, not each individual chart. Missing labels are restored as identity stages before overlap gluing. Comparing covers via their combined family loses no label on either covering family.

Step 3 uses only the new descended-comparisons statement. It has both input assignments and explicitly assumes exactly Step 1's smooth comparisons and Step 2's affine-cover gluing property and cover cocycle. Its conclusion contains all clauses used: cartesian levels, extended ideals, unit-ideal deletion, original label order, identities, composition of counts and level maps, and no deletion for surjective maps. Forgetting labels requires no further lemma: the ordered retained-stage embedding and count are the index data of def-trf-ordinary-resolution-rule, and are part of this conclusion. The empty input and finite disjoint unions are expressly included. Every uses entry has a verbatim statement quotation in citations.json; no source tag is treated as a node citation. The three assembly steps are marked non-elementary because they invoke substantive lemmas; the hypothesis checking within each is elementary.

For the new statements I checked B1–B9: statement only; every object (L, E, the embeddable class, A, R, covers and maps) is quantified; ordinary towers, coherence, regularity, reducedness, smoothness, separatedness, closed/open immersions, extended ideals and cartesian products have their actual definition nodes; TeX has single escapes after JSON parsing; source places and blueprint ancestry are concrete; searches are real. None depends on the parent, so there is no circular interface. They are comparable argument packages, rather than a single renamed parent or elementary standalone nodes. No step of the new assembly exceeds 2000 characters.

I tested each new statement on empty/regular inputs and finite reduced zero-dimensional inputs (trivial towers), a nodal curve embedded in A² and in A³ (ambient independence without confusing the center ideal on X with its ambient ideal), projection by A¹ (varying dimension allowed), and an open immersion missing the node (unit stages may be deleted). For descent I checked a cover with repeated opens, a mixed-dimensional disconnected union, and a nonseparated scheme obtained by gluing affine charts; overlaps are covered by affines and never assumed affine. A nonempty global center can be empty on some components; its whole surjective covering family still sees it. For comparison descent, the subordinate affine cover exists by finite type/quasi-compactness; a finite disjoint union of its component smooth maps to U is smooth, and smooth maps are flat for the blowup pullback. For composition, extension of an ideal along two ring maps is extension along their composite, and a unit ideal stays unit. The canonical tensor identifications on B[I/a] produce the same level map for two-step and direct base change; surjectivity persists at each cartesian level, hence detects each nonempty center. These are the exact checks allocated to old Step 7 below.

This repair responds to the single return in full: three new unsplit tasks, unchanged item statement, all seven original arguments retained in the task handoff, and a 1787-character assembly. I corrected no mathematical assertion, and did not replace lost detail by a vague summary. No compiler, Lake, build tool, local DAG validator, new agent, repository write or launcher edit was used. Required validation is via the server delivery tool.

## Unfinished work

The three new nodes intentionally remain statement-only and unsplit for separate workers. The existing embedded-algorithm input remains the parent assembly's external existence input. No Mathlib leaf and no completed Lean proof is claimed.

## Full retained argument, allocated to the new tasks

The following text is copied verbatim from the current returned node, with its original citations and source places. It preserves all arguments needed to develop the three unsplit tasks and is not inserted as proof steps into those node files.

### lem-trf-embedded-to-intrinsic-smooth-resolution

Original Step 1 (1041 characters):

For a reduced finite-type $X$ admitting a closed embedding $i:X\hookrightarrow P$ into a smooth separated finite-type $\mathbf Q$-scheme, take the embedded tower of [lem-trf-embedded-resolution-ambient-comparison]. At each stage [lemma-nagata-strict-transform-ambient-closed] identifies $X_{i+1}$ with the ordinary blowup of $X_i$ in the ideal of $C_i\subset X_i$. Thus the strict-transform tower is an intrinsic ordinary blowup tower with coherent, nonempty, nowhere dense regular centers and regular last scheme. Keep its synchronization labels. The ambient-comparison clause of the embedded input identifies these intrinsic towers for different embeddings, including their ideals and labels; write the resulting tower $A(X)$. For an affine finite-type $X$, a finite algebra generating set gives a surjection $\mathbf Q[t_1,\ldots,t_N]\twoheadrightarrow\Gamma(X,\mathcal O_X)$ and hence the required closed embedding. Finite disjoint unions admit the disjoint union of these ambient embeddings; the algorithm is applied to this whole pair.

Cited nodes: lem-trf-embedded-resolution-ambient-comparison, lemma-nagata-strict-transform-ambient-closed, def-weil-pbc-finite-type-algebra, def-weil-closed-immersion.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, 2.1.3(ii), 2.3.11--2.3.13; embedded input followed by the ordinary strict-transform/blowup identification.

Original Step 2 (1609 characters):

First compare a smooth $h:Y\to X$ when both schemes have smooth separated ambient embeddings. By [lem-weil-pbc-smooth-locally-standard-smooth], there are affine charts $W=\operatorname{Spec}C\subset Y$ and $V\subset X$ covering $Y$ on which $W\to V$ is standard smooth. Embed $V$ in an affine space $\operatorname{Spec}B$, so $V=\operatorname{Spec}(B/I)$, as in Step 1. The quotient-lifting statement [lem-weil-pbc-standard-smooth-quotient-lift] supplies a standard smooth $B$-algebra $D$ with $D/ID\simeq C$. By [lem-weil-pbc-standard-smooth-is-smooth], $Q=\operatorname{Spec}D\to\operatorname{Spec}B$ is smooth by [lem-weil-pbc-smooth-ring-map-iff-smooth-affine], and its square with closed subschemes $W$ and $V$ is cartesian. The polynomial ring $B$ is a standard smooth $\mathbf Q$-algebra with no equations, so $\operatorname{Spec}B\to\operatorname{Spec}\mathbf Q$ is smooth by the same two statements, and the ambient $Q$ is smooth over $\mathbf Q$ by [lem-trf-smooth-composition]; being affine of finite type it is an allowed ambient scheme. Apply the embedded smooth-ambient comparison. Each open $V\subset X$, respectively $W\subset Y$, is the intersection with an open of its original ambient scheme; that ambient open need not be affine. Smooth-ambient open restriction and the intrinsic embedding comparison therefore identify the towers here with the restrictions of $A(X)$ and $A(Y)$. On these charts the latter is the contracted pullback of the former, with identical labels and extended ideals. The lifting requires no nilpotence of $I$, and the charts can have different relative dimensions.

Cited nodes: lem-trf-embedded-resolution-ambient-comparison, lem-weil-pbc-smooth-locally-standard-smooth, lem-weil-pbc-standard-smooth-quotient-lift, lem-weil-pbc-standard-smooth-is-smooth, lem-weil-pbc-smooth-ring-map-iff-smooth-affine, lem-trf-smooth-composition.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, 2.3.13; local ambient reduction, using Stacks 01V7 (lemma-smooth-locally-standard-smooth), 00T7 (lemma-standard-smooth), and the equation-lifting argument in 07CK (lemma-lift-once), only as stated in the cited quotient-lift node.

Original Step 3 (1032 characters):

The preceding local comparisons determine the global one on embeddable $Y$. Indeed a label occurs in $A(Y)$ exactly when its center meets some member $W$ of the covering; the same criterion holds for a nonempty center in $h^*A(X)$. Thus both contracted towers have the same labels in the same order. Induct along this finite ordered list. After the previously compared blowups the inverse images of the $W$ still cover. The local comparison gives equal ideal sheaves there for the next label, so the global ideals are equal. Their blowups agree, which completes the induction. Smooth maps are flat by [lem-pc-smooth-flat]. Flat blowup base change [thm-nagata-blowup-flat-base-change, def-nagata-blowup-flat-base-change-map] identifies the recursive pullback with the cartesian pullback. This proves $A(Y)=(h^*A(X))^c$, retaining labels and ideals; an omitted label is precisely a unit-ideal stage. For open restrictions this comparison follows directly from the smooth-ambient comparison before making the local reduction in Step 2.

Cited nodes: lem-trf-embedded-resolution-ambient-comparison, thm-nagata-blowup-flat-base-change, def-nagata-blowup-flat-base-change-map, lem-pc-smooth-flat.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, 2.1.9 and 2.3.4--2.3.5(ii); explicit use of invariant synchronization instead of renumbering local towers.

### lem-trf-synchronized-resolution-zariski-descent

Original Step 4 (1302 characters):

Let now $S$ be any reduced finite-type $\mathbf Q$-scheme, with no separatedness assumption. Choose a finite affine open cover $\{U_a\}$, possible by [def-weil-finite-type-morphism], and set $U=\coprod_a U_a$. Apply $A$ once to $U$, obtaining a finite common list of labels. For an affine open $W\subset U_a\cap U_b$, the two open maps $W\to U$ are smooth: their ring maps are localizations, which are finitely presented locally, and any lift across a first-order thickening still lands in the same open because the thickening has the same points [def-sbc-smooth-morphisms]. Step 3 identifies both contracted pullbacks with $A(W)$, with its labels and centers. Restore at each missing label the empty center and identity stage from the common label list for $A(U)$. The two uncontracted restrictions are then identical, with equal ideal sheaves. Induct on the labels: the initial spaces glue to $S$; at the next label the compatible local ideals glue to an ideal $I_i\subset\mathcal O_{S_i}$, and their blowups glue to $\operatorname{Bl}_{I_i}(S_i)$ by open base change. Triple-overlap agreement follows from equality of these ideals. This constructs a finite tower $R(S)$ with uncontracted pullback $A(U)$. Intersections of affine opens are covered by affine opens here; they are never assumed affine.

Cited nodes: def-weil-finite-type-morphism, thm-nagata-blowup-flat-base-change, def-nagata-blowup-flat-base-change-map, def-sbc-smooth-morphisms.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, 2.3.5(ii) and 2.1.9; stagewise Zariski gluing of the uncontracted synchronized centers.

Original Step 5 (1065 characters):

Every descended center is coherent, regular and nowhere dense, since these assertions hold on the open cover of the corresponding level supplied by $A(U)$. It is nonempty since its pullback center in $A(U)$ is nonempty. The final scheme is regular since it has the regular final charts of that tower. The affine charts of its levels are those of finite-type blowups from Step 1; hence no non-finite-type intermediate scheme is introduced. To compare two covers, run the same construction on their finite disjoint union. Over every overlap the labeled restrictions agree by Step 3. At every level the pullback to either original covering family is surjective. If a center of the union tower were empty on one whole family, equality on overlaps would make it empty on the other family as well, contradicting nonemptiness. Hence neither family loses a label. Their levelwise glued ideals, and therefore their whole towers, coincide. The same argument with three covers proves transitivity, so the construction gives one canonical rule, independent of the affine cover.

Cited nodes: lem-trf-embedded-resolution-ambient-comparison.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, 2.3.1, 2.3.4 and Remark 2.3.5(ii); the cover-independence and nondeletion argument is written out.

### lem-trf-descended-resolution-smooth-comparisons

Original Step 6 (1260 characters):

For a smooth $h:T\to S$, choose a finite affine cover $U=\coprod U_a\to S$ and a finite affine cover $V=\coprod V_b\to T$ subordinate to the opens $h^{-1}U_a$. The induced $V\to U$ is smooth, with no constancy requirement on relative dimension: on $V_b$ it is the open immersion $V_b\subset h^{-1}U_a$ (smooth as in Step 4 [def-sbc-smooth-morphisms]), followed by the restriction of $h$ to the open $h^{-1}U_a$, followed by the open immersion $U_a\subset U$, and composites of smooth maps are smooth [lem-trf-smooth-composition]. Step 3 compares $A(V)$ with the contracted pullback of $A(U)$. By construction $A(U)$ and $A(V)$ are the uncontracted pullbacks of $R(S)$ and $R(T)$ along their respective open covers. Descend the comparison one label at a time: a global extended ideal is a unit ideal if and only if it is unit on all the lifted $V_b$; at every retained label those local ideals are precisely the ideals of $A(V)$, and hence descend to those of $R(T)$. Blowup base change identifies the next levels, completing the induction. Thus $R(T)=(h^*R(S))^c$ with the extended ideals in their original order. In particular the construction applies to a finite disjoint union as one input, rather than resolving its components with unrelated stage numbers.

Cited nodes: thm-nagata-blowup-flat-base-change, def-nagata-blowup-flat-base-change-map, lem-trf-smooth-composition, def-sbc-smooth-morphisms.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, 2.1.9, 2.3.4--2.3.5 and 2.3.13; smooth comparison after synchronized affine descent.

Original Step 7 (911 characters):

The comparisons are canonical and respect identities and composition. On an affine blowup chart with center ideal $I\subset B$ and generator $a$, the base-change identifications use the canonical maps on $B[I/a]$; for $B\to C\to D$ the two identifications agree through $D\otimes_C(C\otimes_B B[I/a])\simeq D\otimes_B B[I/a]$, on every generator. Gluing gives the same comparison on every level. Extending ideals twice is extending them along the composite, and a unit ideal stays unit after extension; deleting first and then deleting again keeps exactly the ordered subsequence retained by the composite. Finally, when $h$ is surjective each level of its cartesian pullback is surjective over the corresponding $S_i$. The inverse image of every nonempty center is then nonempty, so no extended ideal is unit and no stage is deleted. For the empty scheme the algorithm and the descended tower have length zero.

Cited nodes: thm-nagata-blowup-flat-base-change, def-nagata-blowup-flat-base-change-map.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, 2.3.4 and Remark 2.3.5(i); identity/composition checked on charts and on ordered deletion.
