# Worker report: repair of lem-trf-j2-affine-cover

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-j2-affine-cover.json`: unchanged statement and statement dependencies; three assembly steps, 1360 characters total.
- `dag/nodes/sec-trace-formula/lem-trf-affine-test-algebra-chart-refinement.json`: statement-only, status unsplit, no Mathlib match. Carries the geometric preparation of old steps 1–3 (2091 characters of original proof).
- `dag/nodes/sec-trace-formula/lem-trf-regular-locus-affine-chart-gluing.json`: statement-only, status unsplit, no Mathlib match. Carries the regular-locus comparison and gluing of old steps 4–5 (1740 characters of original proof, with the J-2 applications left in the assembly).
- `citations.json`: one verbatim statement excerpt per parent step/node citation.
- `searches.jsonl`, `search-results/`, `search-jobs.json`: actual new-statement searches and their complete returned hits. `returned-proof.json` and `prior-report.md` retain the pre-repair evidence. Sandbox-only scripts generate the JSON/report; they are not library changes.

Two new nodes, zero Mathlib leaves. The new nodes contain no proof steps or proof dependencies. They are separate work items, of comparable argument size: the first does not mention regularity or J-2 at all; the second does not mention finite type algebras or J-2. Neither is a restatement or a clause of the parent conclusion. Their combination still needs the two uses of the quantified J-2 definition in the parent.

## Attachments

None. The exact blueprint-tag and concept searches in `lean/WeilConjectures/` found no complete project theorem of this item. I also read `lean/Sheaf/AlgebraicGeometry/JTwoAffineCover.lean`: `AlgebraicGeometry.j2_of_affine_open_cover` has a proof consisting of `sorry`, so cannot be attached. The chart/regular-locus concept search in both source directories found only the parent, its consumer, and unrelated Koszul statements. `WeilConjectures/RingTheory/Excellent.lean` now defines IsJ1 and IsJ2 and proves finite-type ascent of IsJ2, but does not prove affine-cover locality or either new statement.

## Wanted literature

None.

## Return addressed and repair base

The sandbox initially contained only dispatcher markers, with no node, report or search log. I restored the current live item (the returned five-step split) and the earlier Q39 report from the read-only clone; no earlier sandbox evidence was overwritten. The required initial dry run exited with the diagnostic that the restored report lacked `## Review by Q91`. The files here now repair the return substantively, rather than re-pushing the old split: two new independent obligations replace the original long proof by a short assembly. The item's existing reviewed/Lean/ancestry metadata is preserved. The original statement is true and is unchanged; no statement dispute is needed. No unit record is changed.

The chapter/unit records and SETUP's three levels were read. The inherited route is excellence of the normalization charts in the Step 5 spreading argument below `lem-trf-local-term-locality`. Both new nodes inherit the same chapter/unit and exact ancestor, with the item prepended to `blueprint.from.via`. Whole-blueprint searches for regular locus, J-2, 07R4 and affine finite type, and DAG searches for the tags, regularity, finite type charts and affine refinements found no duplicate of either new statement. Broad matches concern other coefficient or normalization problems, not these local geometric statements. No SGA source is used.

## Not duplicates

lem-trf-affine-test-algebra-chart-refinement vs lem-trf-j2-affine-cover: both cite 07R4, but the new statement constructs the test morphism and its compatible finite type charts without any J-2 assumption or conclusion; the item transfers J-2 between coordinate rings of different affine covers.

lem-trf-regular-locus-affine-chart-gluing vs lem-trf-j2-affine-cover: both cite 07R4, but the new statement compares regular-local stalks with prime localizations and tests openness on affine covers of one scheme, with no finite type algebra or J-2 assertion; the item applies this to all finite type test algebras.

lem-trf-affine-test-algebra-chart-refinement vs lem-weil-pbc-lft-pointwise-criterion: the existing criterion characterizes a given morphism pointwise, but does not construct the composite test morphism, prove Noetherianity or produce the compatible cover over a prescribed target family.

lem-trf-affine-test-algebra-chart-refinement vs lem-weil-pbc-lft-affine-pairs: the latter identifies finite type maps on already chosen affine pairs. It does not carry the affine-test construction, open inclusion/composition, local Noetherianity and selection of the covering pairs. Its statement is a tool for a future proof of the new obligation.

lem-trf-regular-locus-affine-chart-gluing vs lem-weil-pbc-affine-open-stalk-localization: the latter is the algebra-to-stalk isomorphism, with no assertion about preservation of the regular-local predicate or openness of regular loci. The new node carries precisely that comparison and its gluing, extracted as requested by the re-split return.

lem-trf-regular-locus-affine-chart-gluing vs lem-sc-affine-regular-stalk-comparison-bijective: 'regular' in the existing title refers to the regular module action in an explicit free-sheaf stalk computation, not regular local rings or regular loci. The same distinction applies to lem-sc-affine-regular-stalk-scalar.

lem-trf-affine-test-algebra-chart-refinement vs lem-trf-excellent-scheme-affine-cover: the existing parent transfers full excellence between charts; the new node only constructs test-algebra charts and does not assume excellence.

lem-trf-regular-locus-affine-chart-gluing vs lem-trf-excellent-scheme-affine-cover: the existing parent assumes excellent chart rings and concludes excellence on all affine opens, whereas the new node is only the stalk/localization comparison and topological openness test.

The other DAG files mentioning 07R4 were opened: lem-per-quasi-excellent-finite-type-stability assumes quasi-excellence on every base affine and concludes quasi-excellence upstairs; lem-per-normal-surface-exceptional-curves studies proper birational normal surfaces; lem-per-excellent-etale-constant-projection is a derived etale projection statement. None constructs these charts or states the regular-locus comparison. The only existing node whose own source carries 07R4 is the item itself; the pairs above distinguish it explicitly.

## Mathlib searches read

For each new node I ran LeanFinder twice with different phrasings, Loogle, grep and LeanSearch using only msearch.py. Every query is recorded verbatim in the node and `searches.jsonl`; the full responses are retained. All services returned normally. Existing item searches and their results are retained unchanged, as the item's statement/search question did not change.

For the chart node the best hits were `Scheme.OpenCover.affineRefinement` (Cover/Open.lean:156), `Scheme.Hom.finiteType_appLE` (Morphisms/FiniteType.lean:49, alias of the class field at 45), and the Noetherian affine-cover criteria. I read Cover/Open.lean:150–161 and Morphisms/FiniteType.lean:37–100: affineRefinement refines a pre-existing open cover, and finiteType_appLE requires an existing locally finite type morphism and an already chosen contained affine pair. Neither supplies the affine-test morphism, its composition through an open inclusion and Noetherianity plus the compatible charts in one specialization. The new statement needs their construction/composition and so is not a Mathlib leaf. The grep request was `affine.*(refin|cover)|locallyOfFiniteType.*(comp|Spec)|IsLocallyNoetherian` in AlgebraicGeometry; its 25 displayed hits were read, including the unrelated Proj/module presentation covers.

For the regular-locus node, the best hits were `IsAffineOpen.isLocalization_stalk` and `isLocalization_stalk'` (AffineScheme.lean:834 and 818), read with their proofs, and Noetherian affine-cover criteria. The regular-local definition and `IsRegularLocalRing.of_ringEquiv` were read in RingTheory/RegularLocalRing/Defs.lean:51–80. They establish ingredients, not the locus comparison or openness criterion. The second semantic phrasing also returned smooth-locus lemmas, which impose a relative smoothness problem rather than absolute regular-local stalks and therefore do not match. Loogle `IsRegularLocalRing, IsOpen` returned no hits; the regular-locus grep returned only regular-local-ring definitions and polynomial-localization results. I also ran the logged follow-up grep `affineRefinement|finiteType_appLE|Spec_iff|isLocalization_stalk` to locate the candidate sources; this is supplementary search evidence, not an invented node search.

## Review by Q91

I read Morphisms 07R4 (`lemma-J`) in full and More on Algebra 07P7 (`definition-J`). The former proves (4) implies (1) by an affine refinement and local identification of regular loci, then (1) implies (3) by testing finite type algebras on an arbitrary affine open. The definition quantifies over every finite type algebra. The printed S in the cover formula denotes X, as already recorded. There is no route change or new hypothesis on the parent.

For the chart node I read Morphisms 01T1 (`definition-finite-type`), 01T2 (`lemma-locally-finite-type-characterize`), 01T3 (`lemma-composition-finite-type`), 01T5 (`lemma-immersion-locally-finite-type`), 01T6 (`lemma-finite-type-noetherian`) and Schemes 01IT (`lemma-basis-affine-opens`). I opened every old cited node statement. The pointwise criterion really is an iff with a single pair at each point, so the whole affine Y,V supplies h locally finite type. The immersion node's clause (2) applies to the open inclusion through its identity closed-immersion factorization; the composition node's clause (e) covers locally finite type, not only proper maps. The Noetherianity nodes require exactly the actual locally Noetherian X. The affine basis chooses W_y inside the inverse image, not the possibly non-affine intersection itself, and the all-affine-pairs node gives finite type for the actual chosen pair. The new statement retains each of these obligations, not just a vague assertion that charts exist.

For the regular-locus node I read Schemes 01HV (`lemma-spec-sheaves`), especially (1) and (6), and the regular-local predicate in def-weil-regular-scheme. The existing stalk-localization node's clause (c) is genuinely an isomorphism from the localization of the chart ring to the ambient local ring. Preservation of regular locality requires identifying ideals, maximal ideals, generating sets and prime chains along that isomorphism; that comparison is now work for the new node, together with the open-subset and union arguments. The statement explicitly includes the whole-affine Spec B identification needed at the end, so it does not leave that old argument unassigned. No claim about openness under arbitrary morphisms is made.

New parent step 1 cites lem-trf-affine-test-algebra-chart-refinement: its hypotheses are exactly X locally Noetherian, the supplied affine cover, arbitrary affine V and finite type R-algebra B; its conclusion explicitly gives all the objects and finite type maps used. The citation quote is copied from that actual conclusion. No J-2 conclusion is taken from it.

New parent step 2 cites the J-2 sentence of def-exc-excellent-ring, not the G-ring or catenarity clauses, and uses it on the explicit finite type A_y-algebra C_y supplied in step 1. It then cites the new regular-locus node's iff for this locally Noetherian Y and the actual cover W_y. Those cited statements give exactly the openness assertions used; the proof does not appeal to their eventual proof steps.

New parent step 3 first cites pqf-lem-affine-open-locnoeth with ambient Y and the whole affine open Y, verifying B is Noetherian before invoking the last clause of the regular-locus node. That last clause explicitly identifies Reg(Spec B) with E(B). The final use of def-exc-excellent-ring is the defining quantified J-2 condition, now verified for every finite type B. The quote in citations.json contains the entire clause used. R and V remain arbitrary.

I checked B–E of delivery-errors point by point: self-contained statements, no proof sketch or steps in new nodes, single-escaped TeX, precise Stacks sources, searches actually run and read, no unsupported Mathlib claim, correct ancestry, no duplicate, and parent proof_deps exactly the union of uses. Every non-elementary parent inference has a statement citation, and every quote is verbatim. Both new nodes depend only on prior definition nodes, so neither can create a cycle back to this item. No off-unit statement tool is used in the assembly beyond the already existing Mathlib Noetherianity leaf.

Small cases checked for both new statements and their application: X empty, V empty, B=0, empty Y and empty index family, arbitrary infinite I, and nonreduced B. For the first node, if Y is empty then the function from its empty point set and the empty affine cover exist even when I is empty; if Y is nonempty its map into a covered X ensures a suitable i(y). A unital algebra over the zero ring is zero. No regular point or nonempty regular locus is assumed in the second node; e.g. a nilpotent thickening can have empty regular locus, and the empty union remains open. No finite subcover, separation or affine-intersection hypothesis was inserted.

The return asked for parallelizable work rather than a shorter paraphrase: old steps 1–3 and old steps 4–5 are assigned separately below, verbatim, with the exact local identifications preserved. Only the elementary applications of the quantified J-2 definition remain in the assembly. All new parent steps are under 2000 characters and their total is under 3000. The new nodes remain unsplit for later workers, as requested; no Lean or compiler/build command was used.

## Original argument allocation (verbatim)

The following is the pre-repair proof, retained without shortening. The geometry and local-ring arguments are assigned to the new nodes; the hypotheses and final J-2 applications are instantiated in the parent assembly.

### Returned step 1: lem-trf-affine-test-algebra-chart-refinement

Fix an affine open $V\subseteq X$ and put $R=\mathcal O_X(V)$. By [pqf-lem-affine-open-locnoeth], $R$ is Noetherian. Let $R\to B$ be any finite type algebra and put $Y=\operatorname{Spec}B$. Under the affine identification $V\cong\operatorname{Spec}R$, its structure morphism is $h=\operatorname{Spec}(R\to B)$ [def-weil-affine-spectrum]. Apply [lem-weil-pbc-lft-pointwise-criterion]: for every point of $Y$, take the whole affine $Y$ as its source neighbourhood and the whole affine $V$ as the target neighbourhood. The resulting ring map on global sections is exactly the given finite type map $R\to B$. Thus $h:Y\to V$ is locally of finite type. This also covers $B=0$, where the pointwise condition is vacuous.

Original statement citations: pqf-lem-affine-open-locnoeth, def-weil-affine-spectrum, lem-weil-pbc-lft-pointwise-criterion.

### Returned step 2: lem-trf-affine-test-algebra-chart-refinement

The inclusion $j:V\hookrightarrow X$ is an open immersion [def-weil-open-immersion]. It is an immersion: factor it as the identity of $V$ followed by $j$; the identity is a closed immersion because its underlying space is the whole closed subset $V$ and its sheaf map is the surjective identity [def-weil-closed-immersion]. Clause (2) of [lem-weil-pbc-immersion-base-change-lft] makes $j$ locally of finite type. Clause (e) of [lem-weil-pbc-proper-fp-permanence], applied to $h$ and $j$, makes $f=j\circ h:Y\to X$ locally of finite type. Since $X$ is locally Noetherian, [pqf-lem-locnoeth-lft] gives that $Y$ is locally Noetherian. Define $\operatorname{Reg}(Y)=\{y\in Y:\mathcal O_{Y,y}\text{ is regular local}\}$, using the regular-local-ring predicate of [def-weil-regular-scheme].

Original statement citations: def-weil-open-immersion, def-weil-closed-immersion, lem-weil-pbc-immersion-base-change-lft, lem-weil-pbc-proper-fp-permanence, pqf-lem-locnoeth-lft, def-weil-regular-scheme.

### Returned step 3: lem-trf-affine-test-algebra-chart-refinement

The opens $f^{-1}(U_i)$ cover $Y$. For each $y\in Y$, choose $i(y)$ with $f(y)\in U_{i(y)}$ and apply [lem-weil-pbc-affine-opens-basis] inside the open $f^{-1}(U_{i(y)})$ to obtain an affine open $W_y$ with $y\in W_y\subseteq f^{-1}(U_{i(y)})$. These $W_y$ cover $Y$. Put $A_y=\mathcal O_X(U_{i(y)})$ and $C_y=\mathcal O_Y(W_y)$. Apply [lem-weil-pbc-lft-affine-pairs] to the locally finite type morphism $f$ and the actual affine pair $(W_y,U_{i(y)})$. It says that $A_y\to C_y$ is of finite type. No intersection of two affine opens is asserted to be affine, and no finite subcover is needed.

Original statement citations: lem-weil-pbc-affine-opens-basis, lem-weil-pbc-lft-affine-pairs.

### Returned step 4: lem-trf-regular-locus-affine-chart-gluing

The ring $A_y$ is J-2 by hypothesis. Hence [def-exc-excellent-ring], applied to the finite type $A_y$-algebra $C_y$, says that the set $E_y=\{\mathfrak q\in\operatorname{Spec}C_y:(C_y)_{\mathfrak q}\text{ is regular local}\}$ is open. Under the canonical affine identification of $W_y$ with $\operatorname{Spec}C_y$, let $O_y\subseteq W_y$ correspond to $E_y$. For $z\in W_y$, clause (c) of [lem-weil-pbc-affine-open-stalk-localization], with ambient scheme $Y$ and affine open $W_y$, gives $(C_y)_{\mathfrak q_z}\cong\mathcal O_{Y,z}$. Regular locality is unchanged by this ring isomorphism directly from [def-weil-regular-scheme]: an isomorphism identifies the maximal ideals and their generating sets, the ideals witnessing Noetherianity, and the prime chains measuring Krull dimension. Thus $z\in O_y$ if and only if $z\in\operatorname{Reg}(Y)$, so $O_y=W_y\cap\operatorname{Reg}(Y)$. The set $O_y$ is open in $Y$ because it is open in the open subset $W_y$. Since the $W_y$ cover, $\operatorname{Reg}(Y)=\bigcup_{y\in Y}O_y$ is open in $Y$. For empty $Y$ this is the empty union and is open as well.

Original statement citations: def-exc-excellent-ring, lem-weil-pbc-affine-open-stalk-localization, def-weil-regular-scheme.

### Returned step 5: lem-trf-regular-locus-affine-chart-gluing

Apply clause (c) of [lem-weil-pbc-affine-open-stalk-localization] once more to the whole affine open $Y=\operatorname{Spec}B$ of $Y$. Its local ring at a prime $\mathfrak q$ is $B_{\mathfrak q}$, so the open subset $\operatorname{Reg}(Y)$ just proved open is exactly the ring regular locus of $B$; the same direct invariance of regular locality under isomorphism uses [def-weil-regular-scheme]. We have therefore proved openness of the regular locus for every finite type $R$-algebra $B$. This is precisely the J-2 predicate of [def-exc-excellent-ring]. Since $V$ was arbitrary, every affine open has a J-2 coordinate ring, as required.

Original statement citations: lem-weil-pbc-affine-open-stalk-localization, def-weil-regular-scheme, def-exc-excellent-ring.

## Unfinished work

The two new obligations intentionally remain statement-only, for independent stage-1 workers. The repair of this item is complete subject to server validation and delivery. No missing literature or tool workaround is involved.

## Retained earlier report

The Q39 report restored from the repository is included verbatim to preserve the earlier search, proof and source audit; its counts and five-step descriptions refer to the pre-repair version.

# Worker report: lem-trf-j2-affine-cover

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-j2-affine-cover.json`: statement, split into five complete steps; Mathlib searches find no J-2 affine-cover theorem. The statement, statement dependencies and existing blueprint ancestry are retained. Proof dependencies are the union of the step citations.
- `citations.json`: 17 verbatim excerpts, one for every step/node pair.
- `searches.jsonl`: the actual msearch log. The helper `write_split.py` is sandbox-only.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. All supporting facts already exist, including the Mathlib pointwise finite type criterion that makes a separate affine Spec criterion unnecessary.

## Attachments

None. I searched the read-only slopmaster2 `WeilConjectures/` tree by the exact item tag, J-2, regular locus, and related affine-cover terminology, and checked the upstream name table. There is no declaration of the project stating this item. Occurrences of `J.2` are projections from structures, not the J-2 predicate. Project uses of `HasRingHomProperty.Spec_iff` are applications within other arguments, not declarations of this item.

## Wanted literature

None. The Stacks sources required by this proof are present and were read locally.

## Audit and corrections

The imported item was unsplit with no proof and no Lean audit declaring an existing proof. Its statement is correct. I read Morphisms Tag 07R4, `lemma-J`, including the full equivalence and proof; its last paragraph proves (4) implies (1), and its second paragraph passes to finite type algebras on an arbitrary affine open, giving (3). The source's covering formula in (4) prints S instead of X; the item already explains this typographical issue. No statement correction or STATEMENT-DISPUTED is needed.

I also read More on Algebra Tag 07P7, `definition-J`, so the proof checks every finite type algebra, rather than just the regular locus of a chart ring. The locally Noetherian assumption is retained. No quasi-compactness of X, finite cover, separatedness, or affineness of an intersection is added.

The unit and chapter records were read first. The item is a component of `lem-trf-excellent-scheme-affine-cover`, used below the existing spreading/normalization branch of `lem-trf-local-term-locality`. It does not state the unit proposition and requires no edit to a unit's realization. The ancestor and via list are preserved. Whole-blueprint searches for J-2, regular locus, excellence, finite type ring, and Tag 01T2 gave no duplicate J-2 statement. DAG searches by the same notions and tag found the existing pointwise and all-affine-pairs criteria and the other tools used here. The two blueprint excellence results concern strictly henselian excellent DVRs/branches, not this general local property. There is no change of unit route and no SGA source is used.

The five recorded item searches were actually run with msearch by Q39 and logged. Semantic hits concern locally Noetherian schemes and finite type affine criteria, not J-2. Loogle `"J2"` and grep `J.?2.ring|IsJ2|regular.locus|regularLocus` returned zero hits. I also searched the potential affine-Spec helper: LeanFinder and LeanSearch returned the finite type `HasRingHomProperty` instance, Loogle returned `HasRingHomProperty.Spec_iff`, and grep located RingHomProperties.lean:360 and FiniteType.lean:54. I read those declarations. Before making any helper node I found `lem-weil-pbc-lft-pointwise-criterion`; choosing the whole affine source and target specializes that existing statement immediately, so no helper is created. Those extra searches remain in the log, without being misrepresented as searches for a new node.

## Not duplicates

No new nodes are proposed. In particular there is no new affine-Spec lemma: the existing `lem-weil-pbc-lft-pointwise-criterion` supplies it by taking whole affine neighbourhoods. The separate existing `lem-weil-pbc-lft-affine-pairs` is used in the other direction, to get finite type on every actual chart pair.

## Review by Q39

I checked the split against delivery-errors B through E with the cited node statements and source text open. This is the author's self-review for direct delivery.

Step 1 uses the full statement of `pqf-lem-affine-open-locnoeth` with S=X and the chosen affine V, so R is Noetherian under the actual hypothesis on X. `def-weil-affine-spectrum` supplies the map induced by R to B and its global sections. The statement of `lem-weil-pbc-lft-pointwise-criterion` is an equivalence with existence of one affine pair at every point. Taking Y and V themselves proves its right-hand condition directly; I do not take an affine-Spec implication from the proof of the all-pairs node. The sources read are Properties 01OW, `lemma-locally-Noetherian`, and Morphisms 01T1/01T2, `definition-finite-type`/`lemma-locally-finite-type-characterize`.

Step 2 uses `def-weil-open-immersion` for the open inclusion. From the actual definition in `def-weil-closed-immersion`, the identity is closed (whole underlying closed subset and surjective identity sheaf map); factoring j through this identity makes it an immersion. Clause (2) of `lem-weil-pbc-immersion-base-change-lft` really says immersions are locally of finite type. Clause (e) of `lem-weil-pbc-proper-fp-permanence` really includes composition for **locally** finite type morphisms, without a quasi-compactness condition: no properness clause is invoked. `pqf-lem-locnoeth-lft` applies to f and X and makes Y locally Noetherian. The regular-local predicate is the first sentence of `def-weil-regular-scheme`; I do not use the equivalence about regular schemes in that definition. The corresponding Stacks statements read are 01T5, 01T3, and 01T6 in morphisms.tex.

Step 3 uses the affine-basis statement of `lem-weil-pbc-affine-opens-basis` inside each open inverse image, with point y. The existence of the inverse-image open is continuity of f. The cover follows since each chosen chart contains its indexing point. `lem-weil-pbc-lft-affine-pairs` gives a finite type ring map on the exact pair W_y, U_i because f is locally finite type and the former maps into the latter. The sources read are Schemes 01IT, `lemma-basis-affine-opens`, and Morphisms 01T2. In particular W_y is chosen within an overlap; the overlap itself is never assumed affine.

Step 4 uses exactly the J-2 sentence of `def-exc-excellent-ring` on the finite type A_y-algebra C_y; it needs neither the G-ring nor the catenarity clauses. Clause (c) of `lem-weil-pbc-affine-open-stalk-localization` identifies the localization of C_y at the point's prime with the local ring of the ambient Y, which is precisely what is needed. The source read is Schemes 01HV, `lemma-spec-sheaves`, especially (1) and (6); the node includes its open-subscheme transport. Preservation of regular locality under a ring isomorphism is written directly from the regular-local definition: ideals, prime chains and generating sets are identified. It is a few-line use of definitions, not an unquoted assertion that regular loci commute with an arbitrary morphism. Openness passes through an affine isomorphism and then through the inclusion of an open subset; the union argument is elementary topology. These are the actual details of Reg(Y) intersect W_y = Reg(W_y) used in 07R4.

Step 5 applies the same localization-to-stalk statement to the whole affine Y. It identifies the scheme regular locus with the set of primes at which B is regular local, using the first sentence of `def-weil-regular-scheme`. Since B was arbitrary, the J-2 sentence of `def-exc-excellent-ring` now gives exactly the conclusion. There is no replacement by a weaker J-1 conclusion.

For edge cases I checked the empty scheme/empty covering, an empty affine V (R=0), and the zero finite type algebra B. Unital algebras over 0 are 0, and their spectra are empty; the pointwise condition and the empty-union openness argument still hold. For nonreduced rings (e.g. a polynomial algebra modulo a square over a field) the argument does not suppose the regular locus is nonempty: it uses precisely its openness from J-2. Infinite I is harmless because no finite subcover is extracted. None of the local-ring comparisons assumes regularity or reducedness. No new statement is left to test separately. All five proof steps are under 2000 characters and each carries its argument; no non-elementary subclaim is left as an unreferenced standard fact. The source typo was already documented, and the only refinement made during my own review was eliminating the contemplated duplicate affine-Spec helper after finding the existing pointwise criterion.

## Unfinished work

None in this one-level split. No Lean file was written and no compiler, Lake, or build tool was run. Delivery validation is by the required server-side dry run.
