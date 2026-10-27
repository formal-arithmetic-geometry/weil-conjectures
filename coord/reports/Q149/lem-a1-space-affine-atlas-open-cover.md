# Current-DAG repair — Q149

## Files written

- dag/nodes/sec-purity-real-sheaves/lem-a1-space-affine-atlas-open-cover.json: current repository metadata and unchanged statement/statement dependencies; revised first assembly step and proof dependencies.
- dag/nodes/sec-purity-real-sheaves/lem-a1-surjective-atlas-open-cover-point-lifting.json: retained statement-only new lemma, unsplit; no Mathlib match.
- dag/nodes/sec-purity-real-sheaves/lem-a1-surjective-chart-base-open-factorization.json: retained statement-only new lemma, unsplit; no Mathlib match.
- citations.json: refreshed verbatim quotations for all six step/citation pairs.
- report.md: this current repair record followed by the preserved earlier report, arguments and searches.

## Attachments

None. Read-only searches of WeilConjectures by blueprint id and affine-atlas concepts find no complete project declaration. The existing Sheaf theorem exists_affine_atlas_open_cover at AlgebraicSpaceAffineAtlasOpenCover.lean:60 still has sorry at line 70.

## WANTED

None.

## Return repaired

The return at head 1dad965c35f required rebasing onto the current DAG and rereading changed citations after the side-completion promotion failure. The retained sandbox has been compared field by field with the current read-clone item. Initially only proof, proof_deps and split_report differed, so the statement, statement dependencies, sources, blueprint ancestry and maintainer metadata were already current. The required initial dry run was interrupted at the transport layer; its process no longer existed when this turn resumed. The subsequent completed dry run detected a newly landed overlapping node, lem-a1-space-atlas-open-refinement-pullback (03FX).

I read that entire statement. Its final clause already gives affine source refinement of the prescribed surjective atlas over affine base opens, and its earlier clauses give the represented chart pullbacks and open immersions into the atlas pullback. I therefore removed the proposed lem-a1-fixed-atlas-affine-chart-refinement from this delivery and used the existing node. The parent only needs a surjective prescribed atlas, so the former child's extra non-surjective generality is unnecessary. The first assembly step now explicitly composes the open immersion with the etale atlas pullback, citing clauses (1) and (2) of lem-weil-pbc-etale-composition-cancellation. This is a genuine adjustment to the split, not an unchanged re-push. Two new independent arguments remain, as the released re-split order requires. All old arguments and search results are retained in the historical report below; the removed child's affine-refinement argument is now assigned to the existing 03FX node.

## Review by Q149

For this repair I reread the released stage-1 repair order, the current chapter and unit and their fixed route, the main-20261015 ancestor text, and Stacks spaces-properties.tex at 03FX (lemma-cover-by-union-affines), 03FY (lemma-union-of-quasi-compact), and 06NF (lemma-etale-image-open). These are respectively the affine refinement, covering construction, and image factorization actually used. No source or route change is needed. The main blueprint ancestor is a statement-only text; the expanded auxiliary algebraic-space argument follows the cited Stacks proofs.

I reopened every node used by the assembly. Step 1 takes an atlas from the explicit existence clause in def-trf-algebraic-space, applies the prescribed-atlas existence clause of lem-a1-space-atlas-open-refinement-pullback, and uses its stated P_i description and open-immersion conclusion. The atlas is surjective as that node requires. On every test the atlas projection is etale by the definition node, and the cited etale-composition node says both that an open immersion is etale and that etale maps compose. Thus individual chart etaleness follows without inferring it from coproduct etaleness or using a proof hidden in the cited node. Step 2 takes exactly the open subspace, image equality and representable surjective etale factor from lem-a1-etale-scheme-map-open-image, whose statement I reread unchanged. The retained point-lifting node gives coverage for this same surjective p and its actual open cover. Step 3 applies the retained factorization node to that same surjective factor a_i and the W_i furnished in step 1; its conclusion is a natural map to h_W_i over S. Every citation is backed by its full verbatim current statement in citations.json.

I reread both retained new statements and their logged semantic, Loogle and source-grep results rather than rerunning unchanged searches. The recorded scheme-cover results lack the residue-field extension lift for an algebraic-space target; IsOpenImmersion.lift concerns a scheme source and lacks the asserted natural scheme-test factorization for Y. The previous two-phrasing searches and argument preservation remain below. I checked empty source/target/base, empty W and W=S, a field extension with no rational lift, redundant opens and nonaffine S: the two statements and assembly still hold without quasi-compactness or separation. The new 03FX node assumes etaleness and describes atlas refinement, whereas point lifting applies to any fixed representable surjection and arbitrary fixed open cover; it does not state the extension-lift assertion. It likewise states no descent of a structural map from an arbitrary surjection through a given base open.

Against delivery-errors B–E, the two remaining new nodes are self-contained, statement-only, correctly tagged, already genuinely searched and independent of the parent. Their full old arguments are preserved below. No new leaf, definition, target change or hidden comparison is introduced. The assembly is below 3000 characters and each step is below 2000. I refreshed the parent from current metadata, left the two existing child statements and their search records intact, and regenerated the six citation quotes. Only the sandbox was written; no Lean or build commands were run.

## Not duplicates

lem-a1-surjective-atlas-open-cover-point-lifting vs lem-a1-space-atlas-open-refinement-pullback: the former gives explicit field-extension lifts for any fixed representable surjection and fixed source open cover, without etaleness; the latter constructs a coproduct refinement of an etale atlas and states its pullbacks and point surjectivity, not those extension lifts.

lem-a1-surjective-chart-base-open-factorization vs lem-a1-space-atlas-open-refinement-pullback: the former descends a given base-open factorization across any fixed representable surjection; the latter refines a surjective etale atlas and has no such factorization conclusion for its target.

The remaining same-tag comparisons are preserved under the historical Not duplicates section below and were reread against current statements.

## What remains unfinished

The two delivered new nodes remain statement-only and unsplit for future workers. Their full arguments remain below. No unresolved issue blocks delivery.

## Validation

The first completed current-DAG dry run diagnosed the overlapping 03FX node; that duplicate has been removed and the assembly adjusted. The repaired delivery then completed deliver.py --no-push with exit 0: OK (not pushed) at d0c88d6ae22, server preflight passed. Local read-only checks confirmed unchanged statement/statement dependencies, six exact current citation quotes, two statement-only new nodes and assembly-step lengths 705, 423 and 377 characters. The report update is revalidated before pushing.

# Preserved earlier attempt (historical)

The following report records the earlier three-child version, its searches, exact old proof and prior checks. Its counts, removed-child discussion and old validation are historical; the current delivery above supersedes them.

# Repair of lem-a1-space-affine-atlas-open-cover — Q149

## Files written

- dag/nodes/sec-purity-real-sheaves/lem-a1-space-affine-atlas-open-cover.json: unchanged statement and statement dependencies; three-step assembly proof.
- dag/nodes/sec-purity-real-sheaves/lem-a1-fixed-atlas-affine-chart-refinement.json: statement, unsplit; no exact Mathlib match after LeanFinder (two phrasings), LeanSearch, Loogle and logged source grep.
- dag/nodes/sec-purity-real-sheaves/lem-a1-surjective-atlas-open-cover-point-lifting.json: statement, unsplit; no exact Mathlib match after LeanFinder (two phrasings), LeanSearch, Loogle and logged source grep.
- dag/nodes/sec-purity-real-sheaves/lem-a1-surjective-chart-base-open-factorization.json: statement, unsplit; no exact Mathlib match after LeanFinder (two phrasings), LeanSearch, Loogle and logged source grep.
- citations.json: verbatim statement quotations for every parent step citation.
- searches.jsonl: actual search-command results; existing parent searches are retained.

## Attachments

None. Upstream WeilConjectures searches by blueprint tag and concepts found no declaration of this item. The landed Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineAtlasOpenCover declaration exists_affine_atlas_open_cover ends in sorry, so is not an attachment. Its statement is retained without Lean edits.

## WANTED

None. All sources used are available locally.

## What was wrong and repaired

The released stage-1 repair record explicitly reopens this previously reviewed split. The sandbox contained only dispatcher brief markers, with no node, report or search log to retain; I took the full current repository node, including the maintainer's earlier C4 repairs and recorded searches, as the repair base. The returned four-step proof totaled 3105 characters. It is now distributed among three statement-only nodes, without changing the parent statement, statement dependencies or route. The parent proof has 1155 characters. No Lean was written and no compiler, Lake or build was run.

## Argument preservation and work for the new nodes

These are instructions for future workers, not proof steps in the new JSON nodes. Each new node has an independently quantified statement and no proof or proof_deps field.

### Fixed-atlas chart refinement

This receives all of old steps 1 and 2 except the parent's elementary choice of an atlas. Fix the given representable etale p:h_V -> X. For each v in V choose an affine base open W_v containing its structural image, then an affine neighbourhood U_v of v inside its inverse image, using lem-weil-pbc-affine-opens-basis twice. The structural map factors uniquely through W_v by lem-weil-pbc-morphism-factors-through-open-subscheme. Use the set of points of V as index (empty when V is empty). On every scheme test T -> X, p represents P = T x_X V with etale projection P -> T. Pasting identifies T x_X U_v with P x_V U_v. The latter is the inverse-image open subscheme by lem-weil-pbc-open-immersion-base-change; open immersions are etale, and their composites with P -> T are etale by clauses (1) and (2) of lem-weil-pbc-etale-composition-cancellation. Thus every required chart is representable etale. The new statement records this actual pullback identification, rather than merely an existence of some unrelated affine atlas. Surjectivity of p is unnecessary for this argument.

### Open-cover point lifting

This receives the residue-field argument in old step 3; the already existing 06NF node still supplies the open images and surjective etale factorizations. Given x:Spec K -> X, representability and scheme-test surjectivity of p give the nonempty scheme P = Spec K x_X V. Choose z in P and its residue field L. The structural map supplies a field extension K -> L and a lift Spec L -> V agreeing with x after that extension. Its image belongs to one U_i and it factors through U_i by lem-weil-pbc-morphism-factors-through-open-subscheme. The resulting field-valued map represents the original class of x. Thus the images of the U_i jointly cover point classes, and any open subspaces with exactly these images cover X. Etaleness and affineness are unnecessary; the independent statement applies to any fixed representable surjection and source open cover.

### Base-open factorization descent

This receives all of old step 4. For a scheme test a:h_T -> Y and t in T, pull back q along Spec kappa(t) -> Y. The represented scheme surjects onto Spec kappa(t), so has a point with residue field L and hence a lift Spec L -> U. Since U -> S factors through W, the image of t in S belongs to W. Thus the whole image of T -> S lies in W, and lem-weil-pbc-morphism-factors-through-open-subscheme gives a unique b_a:T -> W. For r:T' -> T the maps b_(a composed h_r) and b_a composed r have the same composite into S; uniqueness identifies them. These maps therefore define the natural transformation Y -> h_W over S; uniqueness on every scheme test proves its uniqueness. Only representability and surjectivity of q are needed, and W need not be affine. This is why the new node is a general factorization theorem rather than a restatement of the parent's affine-base clause.

## Exact retained old proof

Old step 1: Choose a scheme atlas $p:h_V\to X$ that is representable, surjective and etale, using [def-trf-algebraic-space]. For each $v\in V$, choose an affine open $W_v\subseteq S$ containing its image, and then an affine open $U_v\subseteq V$ containing $v$ and contained in the inverse image of $W_v$. Both choices follow from [lem-weil-pbc-affine-opens-basis]. Thus the $U_v$ cover $V$, and each structural map $U_v\to S$ factors through the open subscheme $W_v$ by [lem-weil-pbc-morphism-factors-through-open-subscheme]. The index set $I=|V|$ is a set within [def-weil-size-convention]; if $V$ is empty, use the empty family. Write $U_i,W_i$ for these choices.

Old step 2: For each $i$, the composite $f_i:h_{U_i}\to h_V\to X$ is representable and etale. Indeed, for a scheme test $h_T\to X$, representability of $p$ gives the scheme $P=T\times_XV$, with etale projection $P\to T$ [def-trf-algebraic-space]. By pasting of fibre products, $T\times_XU_i=P\times_VU_i$, and its projection to $P$ is an open immersion by [lem-weil-pbc-open-immersion-base-change]: the inverse-image open subscheme of $P$ under $P\to V$ [def-weil-open-immersion]. Its projection to $T$ is therefore an open immersion followed by an etale morphism; clauses (1) and (2) of [lem-weil-pbc-etale-composition-cancellation] make it etale. This verifies the required property on every scheme test.

Old step 3: Apply [lem-a1-etale-scheme-map-open-image] to each $f_i$. It produces an open subspace $X_i\subseteq X$ with $|X_i|=\operatorname{im}(|U_i|\to|X|)$ and a representable surjective etale map $h_{U_i}\to X_i$. These open subspaces cover: given a field-valued point $x:\operatorname{Spec}K\to X$, the scheme $\operatorname{Spec}K\times_XV$ surjects onto $\operatorname{Spec}K$ by [def-trf-algebraic-space]. Choose a point of this nonempty scheme and its residue field $L$. The resulting map $\operatorname{Spec}L\to V$ has its image in some $U_i$, so factors through that open subscheme by [lem-weil-pbc-morphism-factors-through-open-subscheme] [def-weil-open-immersion]. Its composite to $X$ is the extension of $x$ to $L$, and hence represents the same point class. That class belongs to $|X_i|$. Thus $|X|=\bigcup_i|X_i|$, exactly the covering condition in the statement.

Old step 4: Fix $i$ and a scheme test $h_T\to X_i$. For each $t\in T$, base change the surjective map $h_{U_i}\to X_i$ along $\operatorname{Spec}\kappa(t)\to X_i$. By the scheme-test definition of surjectivity [def-trf-algebraic-space] this is a nonempty scheme. A point and its residue field give an extension $L/\kappa(t)$ and a lift $\operatorname{Spec}L\to U_i$. Since $U_i\to S$ factors through $W_i$, the image of $t$ under $T\to S$ lies in $W_i$. Consequently $T\to S$ has image contained in $W_i$ and factors uniquely through the open subscheme $W_i$ by [lem-weil-pbc-morphism-factors-through-open-subscheme] [def-weil-open-immersion]. For varying $T\to X_i$ these factorizations commute with pullback by uniqueness. They therefore define a natural transformation $X_i\to h_{W_i}$ whose composite with $h_{W_i}\to h_S$ is the structural map. This proves the affine-base clause for every $i$.

## Not duplicates

lem-a1-fixed-atlas-affine-chart-refinement vs lem-a1-space-affine-atlas-open-cover: the new node refines an arbitrary fixed representable etale scheme map, retains its specified source open embeddings and scheme-test pullbacks, and does not construct a disjoint-union atlas, topology or schemehood conclusion.

lem-a1-fixed-atlas-affine-chart-refinement vs lem-a1-algebraic-space-fpqc-sheaf: the new node refines an arbitrary fixed representable etale scheme map, retains its specified source open embeddings and scheme-test pullbacks, and does not construct a disjoint-union atlas, topology or schemehood conclusion.

lem-a1-fixed-atlas-affine-chart-refinement vs lem-a1-space-affine-etale-cover: the new node refines an arbitrary fixed representable etale scheme map, retains its specified source open embeddings and scheme-test pullbacks, and does not construct a disjoint-union atlas, topology or schemehood conclusion.

lem-a1-fixed-atlas-affine-chart-refinement vs lem-a1-space-etale-open-image: the new node refines an arbitrary fixed representable etale scheme map, retains its specified source open embeddings and scheme-test pullbacks, and does not construct a disjoint-union atlas, topology or schemehood conclusion.

lem-a1-fixed-atlas-affine-chart-refinement vs lem-a1-qc-map-affine-etale-neighbourhood: the new node refines an arbitrary fixed representable etale scheme map, retains its specified source open embeddings and scheme-test pullbacks, and does not construct a disjoint-union atlas, topology or schemehood conclusion.

lem-a1-surjective-atlas-open-cover-point-lifting vs lem-a1-space-affine-atlas-open-cover: the new node assumes a fixed representable surjection and a given source open cover and produces explicit lifts over field extensions; it constructs neither an atlas nor open image subspaces.

lem-a1-surjective-atlas-open-cover-point-lifting vs lem-a1-etale-scheme-map-open-image: the new node assumes a fixed representable surjection and a given source open cover and produces explicit lifts over field extensions; it constructs neither an atlas nor open image subspaces.

lem-a1-surjective-atlas-open-cover-point-lifting vs lem-a1-separated-locally-qf-space-representable: the new node assumes a fixed representable surjection and a given source open cover and produces explicit lifts over field extensions; it constructs neither an atlas nor open image subspaces.

lem-a1-surjective-atlas-open-cover-point-lifting vs lem-a1-qc-map-affine-etale-neighbourhood: the new node assumes a fixed representable surjection and a given source open cover and produces explicit lifts over field extensions; it constructs neither an atlas nor open image subspaces.

lem-a1-surjective-chart-base-open-factorization vs lem-a1-space-affine-atlas-open-cover: the new node descends a base-open factorization for a fixed representable surjection, with no etaleness or affine assumptions, and states the unique natural scheme-test factors; it constructs no cover or atlas.

lem-a1-surjective-chart-base-open-factorization vs lem-a1-etale-scheme-map-open-image: the new node descends a base-open factorization for a fixed representable surjection, with no etaleness or affine assumptions, and states the unique natural scheme-test factors; it constructs no cover or atlas.

lem-a1-surjective-chart-base-open-factorization vs lem-a1-separated-locally-qf-space-representable: the new node descends a base-open factorization for a fixed representable surjection, with no etaleness or affine assumptions, and states the unique natural scheme-test factors; it constructs no cover or atlas.

lem-a1-surjective-chart-base-open-factorization vs lem-a1-qc-map-affine-etale-neighbourhood: the new node descends a base-open factorization for a fixed representable surjection, with no etaleness or affine assumptions, and states the unique natural scheme-test factors; it constructs no cover or atlas.

The wider keyword/DAG searches also found lem-sfb-invariant-open-substack-descent (a smooth stack presentation and invariant-open correspondence, not base-open factorization for an arbitrary representable surjection) and lem-trf-space-fibre-products-etale-covers (base change of already jointly surjective etale families, not the residue-field lifting assertion for an arbitrary representable surjection). No existing statement gives these fixed-input constructions. Blueprint searches across all chapters for atlas/refinement, surjective/factorization/open, field-valued/surjective, affine/refinement/etale, and factor/surjective/subspace found no equivalent blueprint node. The inherited nearest ancestor remains lem-a1-affine-hc0.

## Previous review by Q149

I read the returned node and released repair record, the current chapter and unit records, the current blueprint chapter/unit texts and lem-a1-affine-hc0 proof, and Stacks spaces-properties.tex at 03FX (lemma-cover-by-union-affines, lines 700–722), 03FY (lemma-union-of-quasi-compact, lines 724–745), and 06NF (lemma-etale-image-open, lines 536–558). The first new node extracts 03FX's refinement and etale-composition argument before its coproduct, the second spells out 03FY's middle covering sentence with residue-field lifts, and the third spells out its final descent sentence. I read every parent citation's full statement, including the three new statements. I also read the old affine-basis, open-factorization, base-change and etale-composition dependency statements before assigning their arguments to the future workers. Their exact clauses are the inputs described above.

Parent step 1 uses def-trf-algebraic-space exactly for the existence of a representable surjective etale scheme atlas; its scheme-test definitions are also exactly those required by the refinement node. The new node supplies affine source opens covering that same V, etaleness of their composites, and affine base opens with structural factorizations. Surjectivity of p remains available for step 2. Parent step 2 uses the existing lem-a1-etale-scheme-map-open-image statement, not its proof: it explicitly gives open subspaces, equality of their point sets to images, and the representable surjective etale factors. Each f_i satisfies its etale/representable hypotheses from step 1. The lifting node then supplies coverage for those same U_i and p; its field-extension clause matches the point-class convention, so there is no assumption of rational-point surjectivity. Parent step 3 applies the factorization node to a_i and W_i; a_i is surjective representable by 06NF, while U_i -> W_i is available from step 1. Its conclusion is the actual natural map X_i -> h_W_i over S, not merely a point-set containment. These checks discharge C1 and C4 at the new boundary; citations.json quotes the actual statements verbatim.

I tested empty V (empty family, and if p is surjective X is empty), empty X and empty S, redundant source opens, an identity chart, a nonaffine base S, and non-surjective p for the refinement statement. For the lifting node, a field extension Spec L -> Spec K shows why a lift over K itself must not be demanded. For the factorization node, W empty forces U empty and then Y empty by scheme-test surjectivity; W=S gives the unique structural factorization. Neither the parent nor the new statements assumes quasi-compactness, separation, Noetherianity or quasi-separatedness. The restricted chart is not assumed surjective onto X. No affine-intersection claim is used. The two generalized new lemmas still have exactly the arguments of old steps 3 and 4; no extra descent theorem is being smuggled in.

Against B–E: new statements introduce every object and notion, cite definitions, use correctly escaped TeX, and specify Stacks tags and labels rather than moving section numbers. They have no proof steps or proof dependencies. Genuine searches with two semantic phrasings were inspected: scheme affineRefinement does not handle a fixed algebraic-space map or its scheme-test etaleness; scheme Cover.exists_eq does not assert field-extension lifting for an algebraic space; IsOpenImmersion.lift concerns schemes and cannot produce the algebraic-space natural factor without the test argument. None is a Mathlib leaf. The new nodes are different arguments of comparable workload, not new names for the parent or its cover-existence clauses. The old arguments are reproduced above without omission. Sources and route use only Stacks and the blueprint, with no SGA input. New proof dependencies only point downward to the three statement-only nodes and the pre-existing open-image theorem; there is no cycle through this parent. Every assembly step is below 2000 characters and the total is below 3000. No definition or target statement changes.

## What remains unfinished

The three new statement-only lemmas remain unsplit for parallel future workers, as required by the return. Their detailed arguments and lower-level inputs are recorded above. No part of this repair needs a new source or a human decision.

## Validation and delivery

Required remote deliver.py --no-push completed with exit 0 and printed OK (not pushed), preflight passed, at 80c2dfa705c. Local read-only verification confirmed that only parent proof, proof_deps and split_report changed, that the assembly has 1155 characters, and that every citation quote is an exact substring of its cited statement. The delivery invocation follows this successful dry run.
