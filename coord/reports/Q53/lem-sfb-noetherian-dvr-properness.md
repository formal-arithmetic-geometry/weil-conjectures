# Worker report: lem-sfb-noetherian-dvr-properness

1. Files written (all under this sandbox):
   - `dag/nodes/sec-six-functors-basics/lem-sfb-noetherian-dvr-properness.json`: statement unchanged; six assembly steps, 3000 characters in total.
   - `dag/nodes/sec-six-functors-basics/lem-sfb-noetherian-dvr-closed-diagonal.json`: statement, unsplit; no Mathlib match after five recorded searches.
   - `dag/nodes/sec-six-functors-basics/lem-sfb-dvr-proper-domination-closed-immersion.json`: statement, unsplit; no Mathlib match after five recorded searches.
   - `citations.json`: verbatim statements for every use by every parent proof step.
2. Attachments: none. Searching `lean/WeilConjectures/` by blueprint tag, `unique_dvr_lift`, and DVR/separation/properness concepts found no declaration stating this item. The matching local declaration `AlgebraicGeometry.isProper_iff_unique_dvr_lift` in `lean/Sheaf/AlgebraicGeometry/NoetherianDvrProperness.lean:75` ends in `sorry`. It is not a finished proof. No Lean was written or compiled.
3. WANTED: none.
4. The return requests distributing 5251 characters of proof across independently claimable nodes. This repair introduces two new, strictly smaller lemmas. Neither restates the properness equivalence or either of its implications: the first concludes only closedness of a diagonal from uniqueness; the second concludes only closedness of a supplied immersion in a proper-domination diagram from existence. The latter assumes no properness of the ambient structure morphism, no surjectivity of the domination, no separatedness of f, and no uniqueness for f. Localization, construction of the Chow diagram, and proper-surjective descent remain in the parent.
5. Nothing unfinished in the requested split. Both new nodes are deliberately statement-only: `status: unsplit`, empty `proof` and `proof_deps`, null `proof_origin`. Their arguments are recorded below for subsequent workers.

## Repair baseline and blueprint route

The sandbox had no files on arrival, despite the retained-work sentence in the repair brief. I copied the current shared item, which contains exactly the eight returned proof steps and the existing maintainer/Lean metadata; `returned-item.json` preserves that baseline. There was no earlier sandbox report or searches.jsonl to overwrite. Existing searches, citations expressed in the old proof, source-error discussion in the maintainer review, and metadata remain available in that baseline. The item file retains all existing metadata; only proof-owned fields are revised. No git command was run in the shared repository.

Read GOAL.md, SETUP.md's three blueprint levels, the chapter sec-six-functors-basics, and unit sk-thm-sf-ctf-stability. This is a geometric tool below the alteration/stable-pointed-Isom chain realizing det-thm-sf-ctf-stability-direct-images proof (3). The same recorded place is retained. `tools/blueprint_refs.py ancestor lem-sfb-noetherian-dvr-properness` returns None for this pre-existing created chain; both new nodes carry null from.node and the item's via list prefixed by the item, with the exact extracted argument appended to from.place. The chapter and unit records are unchanged.

DAG searches examined titles, statements, source places and tags 0207/0208, plus trait/valuation separation and immersion terminology, across all chapters. Blueprint searches included `DVR`, `valuative separated`, `valuative separation`, `valuative diagonal`, `DVR uniqueness`, `immersion domination`, and `valuative proper`. The DVR matches in coefficient reconstruction concern modules, not schemes; the domination matches are Chow constructions and elimination, not the supplied-diagram closure lemma. No equivalent blueprint node was found, so same_as is empty. General valuation-ring existence/uniqueness nodes are reused as the extracted arguments' tools, not duplicated.

## Not duplicates

lem-sfb-dvr-proper-domination-closed-immersion vs lem-sfb-generic-dvr-properness-criterion: The existing criterion concerns an integral source, its canonical generic point, and properness of its structure map. The new node concerns arbitrary Y -> X and an immersion Y -> P in a given commutative diagram, with no integral-source or generic-point assumption, and concludes only that i is closed.

lem-sfb-dvr-proper-domination-closed-immersion vs lem-sfb-noetherian-dvr-properness: The item is an equivalence between properness and unique DVR lifts of f. The new node proves closedness of a supplied immersion Y -> P from proper Y -> X, Noetherian P, separated q, and existence alone for f; it gives neither properness of f nor its valuative criterion.

Additional conceptual comparisons: the closed-diagonal node uses only uniqueness and concludes separation; the parent requires existence as well and concludes properness. `lemma-nagata-separated-valuation-lift-unique` has the reverse direction and all valuation rings. `lemma-nagata-proper-separated-valuation-extension` starts with properness, whereas the new domination node applies it only to pi while deriving closedness of i. `lem-weil-pbc-immersion-closed-image-closed-immersion` assumes the image is already closed, which is exactly the substantive assertion the new node must establish. `lem-sfb-noetherian-image-boundary-dvr` supplies a boundary trait but does not exclude boundary points. None can replace either new statement in one line.

## Review by Q53

I read Stacks `literature/stacks-project/limits.tex`, Tag 0208 (`lemma-Noetherian-dvr-valuative-proper`) in full for the item and the domination node, and Tag 0207 (`lemma-Noetherian-dvr-valuative-separation`) in full for the diagonal node. I also read the immediately preceding boundary-trait statement/proof, Tag 0CM2, and the existing boundary-node statement. The arguments use the valid missing-boundary-point case, without generic-component refinements. No excellence or finite-type hypothesis on the DVR is introduced. No SGA source is used.

For parent step 1, I checked the actual statements of def-weil-proper-morphism (proper implies separated), def-sc-discrete-valuation-ring (its valuation-ring characterization), and lemma-nagata-proper-separated-valuation-extension (unique lift for every valuation ring square). These supply the forward implication without Noetherian hypotheses.

For step 2, pqf-def-locnoeth supplies the affine cover, lem-sfb-finite-type-composition-base-change supplies finite type after base change, and def-pc-fibre-product supplies exactly the existence and uniqueness of the induced lift into the restricted source. The equality of the two projections is written in the retained step. lemma-nagata-projective-target-local asserts properness is local on this open cover, and lem-weil-pbc-finite-type-over-noetherian gives Noetherian and quasi-compact X once the base is affine Noetherian. This step, including the original restriction argument, is retained verbatim.

For step 3, I checked that the new closed-diagonal statement asks only for equality of two DVR morphisms with the same base map and generic restriction. The original unique-lift hypothesis implies exactly this, even if no existence is used. The Noetherian base and finite-type f were established in step 2. Its closed-immersion conclusion gives separatedness by def-weil-proper-morphism. This node receives the original steps 3 and 4 in full, as reproduced below; it carries a genuine two-stage boundary/diagonal argument, not a mere definition of separatedness.

For step 4, lem-weil-pbc-chow-noetherian explicitly requires separated finite-type f and Noetherian S, all now established, and explicitly gives pi proper and surjective and the immersion i into projective space with qi=f pi. lemma-nagata-projective-space-base-change-proper gives proper q. def-weil-proper-morphism, lem-sfb-finite-type-composition-base-change and lem-weil-pbc-finite-type-over-noetherian establish the Noetherian X' and P used by the next node. The whole original step 5 is retained, including why its birational refinement is unnecessary.

For step 5, the new domination lemma introduces all four schemes and four morphisms. In its application Y is X', whose quasi-compactness follows from its Noetherianity in step 4; P is Noetherian there, pi is proper, i is an immersion, and q is separated because it is proper. The parent's existence clause is exactly its DVR-existence hypothesis. Its conclusion is the closed immersion i needed for descent. The full argument of original steps 6 and 7 and the closed-image conversion at the start of step 8 belongs to this node, reproduced below. I checked the generic square for f, the square for pi, and the common base composite required by separated q separately: f pi u=q i u=q v j, pi u=h j, and q i w=f pi w=f h=q v.

For step 6, lem-weil-pbc-closed-immersion-proper clause (b) states precisely that proper q composed with the closed immersion i is proper. Proper implies universally closed by def-weil-proper-morphism. lem-weil-pbc-image-universally-closed descends this along surjective pi, and its final assertion requires only the already obtained separatedness and local finite type of f. Step 2 then supplies the original locally Noetherian base. Every cited node's statement was opened, and citations.json contains verbatim supporting text (the whole statement, including the used clause). The proof dependency list is exactly the union of uses. No step exceeds 2000 characters.

I tested the new statements against the empty source (vacuous diagonal or empty closed immersion), identity morphisms, the line with doubled origin (two trait lifts violate the diagonal node's uniqueness hypothesis), and an open punctured affine line into the affine line. In the latter test take pi=id and q=id: the trait centered at the missing origin has a generic map into the punctured line and no extension, so the domination lemma's DVR-existence assumption correctly fails. A proper closed subscheme with pi=id satisfies the conclusion. Removing surjectivity of pi from the new lemma is harmless: only extension through its properness is used; surjectivity is retained for the parent's separate descent. Removing separatedness of q would invalidate the comparison, so it is explicitly retained.

The two new arguments have comparable workloads: original steps 3-4 contain the finite-type diagonal calculation and boundary contradiction (1457 characters); original steps 6-7 plus closed-image conversion contain the finite-type immersion calculation, boundary trait, two lifts and separated comparison (about 1460 characters). They are independent: neither new node cites the other or the parent. Their proof fields are empty so other workers can start both immediately. Their detailed arguments and tool citations are below, rather than hidden in statements. The parent's 3000-character assembly preserves the remaining arguments. This directly repairs the single numbered return rather than merely summarizing its proof.

## Mathlib evidence

Each new node has five actual msearch.py records in searches.jsonl: two LeanFinder phrasings, Loogle, LeanSearch, and source grep. All services returned successfully. Read the hits and the relevant Mathlib source. `ValuativeCriterion.lean:86-87` defines uniqueness over all valuation rings, and `IsSeparated.of_valuativeCriterion` at 246-247 uses that condition. The analogous universal-closedness result at 238 also quantifies over all valuation rings. The file explicitly lists the Noetherian DVR reduction as future work at line 29. `IsClosedImmersion.iff_isProper_and_mono` at `ZariskisMainTheorem.lean:393-394` assumes properness already. `of_isPreimmersion` assumes the image closed, and `of_comp` assumes a closed-immersion composite. These hits do not supply either new DVR-only statement in one line. The item's existing searches are retained without inventing a new search history.

## Source error retained from the returned review

The unrestricted 0CM2 formulation in limits.tex is false for a trivial specialization: for id: Spec(F_p) -> Spec(F_p), it demands a DVR with fraction field F_p, which cannot exist. Its proof's use of exists-dvr requires a nonfield Noetherian local domain. Both extracted arguments use only a point in the closure of an image but outside that image, exactly the hypothesis of existing lem-sfb-noetherian-image-boundary-dvr; this forces a nontrivial specialization. I preserve this previously recorded issue rather than reinstating the unrestricted claim. The parent and the new statements themselves require no correction and no weakening.

## Full argument retained for subsequent workers

The following is the returned proof verbatim, with each portion assigned explicitly. Nothing from the old proof has been discarded. These are report notes, not proof fields of the new unsplit nodes.

### Original step 1: parent step 1 (verbatim)

If $f$ is proper, it is separated by definition. A DVR is a valuation ring, as included in the equivalent characterization in [def-sc-discrete-valuation-ring]. Apply [lemma-nagata-proper-separated-valuation-extension] to any of the stated DVR squares to obtain exactly the required unique lift. This proves the forward implication without a Noetherian hypothesis.

Tools: def-weil-proper-morphism, def-sc-discrete-valuation-ring, lemma-nagata-proper-separated-valuation-extension

Source: literature/stacks-project/limits.tex, Tag 0208 (lemma-Noetherian-dvr-valuative-proper), (1) implies (2) implies (3).

### Original step 2: parent step 2 (verbatim)

Assume the unique-DVR-lifting condition. Choose an affine open cover $S=\bigcup_i S_i$ with Noetherian coordinate rings, as in [pqf-def-locnoeth], and put $X_i=X\times_S S_i$. Finite type survives this base change by [lem-sfb-finite-type-composition-base-change]. The lifting condition survives too: compose a square over $S_i$ with $S_i\to S$; its lift to $X$, together with the prescribed map to $S_i$, gives a lift to $X_i$ by the fibre-product universal property. Two such lifts have the same projection to $X$ by the original uniqueness assumption and the same projection to $S_i$, hence coincide. By [lemma-nagata-projective-target-local] it suffices to prove properness of each $X_i\to S_i$. Relabel one such pair as $X\to S$. Now $S$ is affine Noetherian and $X$ is Noetherian by [lem-weil-pbc-finite-type-over-noetherian]; in particular $X$ is quasi-compact.

Tools: pqf-def-locnoeth, lem-sfb-finite-type-composition-base-change, def-pc-fibre-product, lemma-nagata-projective-target-local, lem-weil-pbc-finite-type-over-noetherian

Source: literature/stacks-project/limits.tex, Tag 0208, first paragraph of (4) implies (1): reduction to an affine Noetherian base; the same argument applies to condition (3).

### Original step 3: lem-sfb-noetherian-dvr-closed-diagonal

Put $T=X\times_S X$. Its projection to $X$ is the base change of $f$, so $T\to S$ is of finite type by base change and composition [lem-sfb-finite-type-composition-base-change]. Thus $T$ is Noetherian [lem-weil-pbc-finite-type-over-noetherian], and hence quasi-separated [lem-weil-pbc-locally-noetherian-quasi-separated]. The diagonal $\delta:X\to T$ is an immersion [lem-weil-pbc-diagonal-immersion], and therefore locally of finite type [lem-weil-pbc-immersion-base-change-lft]. Since its source $X$ is quasi-compact and its target $T$ quasi-separated, it is quasi-compact by [lem-weil-pbc-qcqs-morphism-permanence](1). Consequently $\delta$ is of finite type [def-weil-finite-type-morphism].

Tools: lem-sfb-finite-type-composition-base-change, lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-locally-noetherian-quasi-separated, lem-weil-pbc-diagonal-immersion, lem-weil-pbc-immersion-base-change-lft, lem-weil-pbc-qcqs-morphism-permanence, def-weil-finite-type-morphism

Source: literature/stacks-project/limits.tex, Tag 0207 (lemma-Noetherian-dvr-valuative-separation), finite-type case: the diagonal is a quasi-compact immersion of Noetherian schemes.

### Original step 4: lem-sfb-noetherian-dvr-closed-diagonal

If $\delta(X)$ were not closed, choose $t\in\overline{\delta(X)}\setminus\delta(X)$. Apply [lem-sfb-noetherian-image-boundary-dvr] to the finite-type map $\delta$ with Noetherian target $T$. It gives $a:\operatorname{Spec}K\to X$ and $c:\operatorname{Spec}A\to T$ with $c|_{\operatorname{Spec}K}=\delta a$ and $c(s_A)=t$. Write $h_1=p_1c$ and $h_2=p_2c$. The two maps have equal composite to $S$ and restrict to $a$ over $K$, so uniqueness in the assumed DVR square for $f$ gives $h_1=h_2$. The fibre-product universal property now gives $c=\delta h_1$, contradicting $t\notin\delta(X)$. Thus $\delta(X)$ is closed, and its immersion is a closed immersion by [lem-weil-pbc-immersion-closed-image-closed-immersion]. By [def-weil-proper-morphism], $f$ is separated.

Tools: lem-sfb-noetherian-image-boundary-dvr, def-pc-fibre-product, lem-weil-pbc-immersion-closed-image-closed-immersion, def-weil-proper-morphism

Source: literature/stacks-project/limits.tex, Tag 0207, finite-type diagonal argument, using the boundary-point formulation of Tag 0CM2 instead of the generic-component refinement.

### Original step 5: parent step 4 (verbatim)

Apply [lem-weil-pbc-chow-noetherian] to the separated finite-type map $f$ over our Noetherian $S$. Obtain $\pi:X'\to X$ proper and surjective, and an immersion $i:X'\to P=\mathbf P^n_S$ with $qi=f\pi$, where $q:P\to S$ is proper by [lemma-nagata-projective-space-base-change-proper]. Proper morphisms are of finite type [def-weil-proper-morphism]. Hence $X'\to S$ is of finite type by composition [lem-sfb-finite-type-composition-base-change]; so both $X'$ and $P$ are Noetherian by [lem-weil-pbc-finite-type-over-noetherian]. We only need properness and surjectivity of $\pi$; the birational refinement of Chow is unnecessary for condition (3), which tests every DVR square.

Tools: lem-weil-pbc-chow-noetherian, lemma-nagata-projective-space-base-change-proper, def-weil-proper-morphism, lem-sfb-finite-type-composition-base-change, lem-weil-pbc-finite-type-over-noetherian

Source: literature/stacks-project/limits.tex, Tag 0208, second paragraph of (4) implies (1), Chow construction; Tag 0200 (coherent-lemma-chow-Noetherian).

### Original step 6: lem-sfb-dvr-proper-domination-closed-immersion

The target $P$ is quasi-separated by [lem-weil-pbc-locally-noetherian-quasi-separated]. Since $X'$ is quasi-compact, [lem-weil-pbc-qcqs-morphism-permanence](1) makes $i$ quasi-compact, and [lem-weil-pbc-immersion-base-change-lft](2) makes it locally of finite type, hence finite type [def-weil-finite-type-morphism]. If its image is not closed, choose $y\in\overline{i(X')}\setminus i(X')$. Apply [lem-sfb-noetherian-image-boundary-dvr] to $i$ to obtain $u:\operatorname{Spec}K\to X'$ and $v:\operatorname{Spec}A\to P$ such that $iu=v|_{\operatorname{Spec}K}$ and $v(s_A)=y$.

Tools: lem-weil-pbc-locally-noetherian-quasi-separated, lem-weil-pbc-qcqs-morphism-permanence, lem-weil-pbc-immersion-base-change-lft, def-weil-finite-type-morphism, lem-sfb-noetherian-image-boundary-dvr

Source: literature/stacks-project/limits.tex, Tag 0208, missing boundary point of the Chow immersion and its DVR; expressed through Tag 0CM2 restricted to boundary points.

### Original step 7: lem-sfb-dvr-proper-domination-closed-immersion

The square for $f$ with top arrow $\pi u$ and bottom arrow $qv$ commutes, since $f\pi u=qiu=qv|_{\operatorname{Spec}K}$. The assumed existence gives $h:\operatorname{Spec}A\to X$ with $fh=qv$ and $h|_{\operatorname{Spec}K}=\pi u$. Apply [lemma-nagata-proper-separated-valuation-extension] to the proper (hence separated) map $\pi$, with top arrow $u$ and bottom arrow $h$, obtaining $w:\operatorname{Spec}A\to X'$ with $\pi w=h$ and $w|_{\operatorname{Spec}K}=u$. The maps $iw$ and $v$ to $P$ have equal composites to $S$, namely $qiw=f\pi w=fh=qv$, and equal generic restrictions $iu$. Since $q$ is separated, [lemma-nagata-separated-valuation-lift-unique] gives $iw=v$. In particular $y=v(s_A)=i(w(s_A))$, contrary to the choice of $y$. Therefore $i(X')$ is closed.

Tools: lemma-nagata-proper-separated-valuation-extension, def-weil-proper-morphism, lemma-nagata-separated-valuation-lift-unique

Source: literature/stacks-project/limits.tex, Tag 0208, diagram (equation-solid) and final contradiction; both applications use DVRs with no excellence or generic-image assumptions.

### Original step 8: closed-image conversion to lem-sfb-dvr-proper-domination-closed-immersion; remaining descent to parent step 6

By [lem-weil-pbc-immersion-closed-image-closed-immersion], $i$ is a closed immersion. Since $q$ is proper, [lem-weil-pbc-closed-immersion-proper](b) makes $qi=f\pi$ proper, in particular universally closed [def-weil-proper-morphism]. Because $\pi$ is surjective, [lem-weil-pbc-image-universally-closed] now gives that $f$ is universally closed, and its final assertion gives properness because $f$ is already separated and locally of finite type. The affine-local reduction in step 2 completes the result over the original locally Noetherian base.

Tools: lem-weil-pbc-immersion-closed-image-closed-immersion, lem-weil-pbc-closed-immersion-proper, def-weil-proper-morphism, lem-weil-pbc-image-universally-closed

Source: literature/stacks-project/limits.tex, Tag 0208, reduction to closedness of the Chow immersion; Tag 01IQ (schemes-lemma-immersion-when-closed) and Tag 03GN (morphisms-lemma-image-proper-is-proper).

## Validation

Required server dry run and push follow this review. No local DAG checker or compiler has been run.
