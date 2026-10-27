# Repair of lem-sfb-universal-closed-immersion-open

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-universal-closed-immersion-open.json`: unchanged statement; split proof, three assembly steps, 1087 characters.
- `dag/nodes/sec-six-functors-basics/lem-sfb-closed-graph-universally-closed-diagram.json`: new statement, status unsplit; full cartesian graph and universal-closedness package; no exact Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-universally-closed-unramified-radicial-criterion.json`: new statement, status unsplit; closed-immersion criterion for universally closed morphisms; no exact Mathlib match.
- `citations.json`: verbatim statement quotes for every parent-step citation.

## Attachments

None. The search of `lean/WeilConjectures/` by blueprint tag, notion and expected declaration found no finished project theorem for the item. `lean/Sheaf/AlgebraicGeometry/UniversalClosedImmersionOpen.lean` states the item but its proof is `sorry`, so it is not an attachment. No Lean is written or compiled.

## WANTED

None. All sources used are present in `literature/stacks-project/`.

## What was wrong and repair

The returned proof was mathematically reviewed but too large to leave as one worker item: six steps and 3244 characters. The sandbox initially contained only launcher brief markers, no retained nodes, report or search log. I therefore used the current live node as the retained-head baseline, preserving every maintainer field, statement, old search entry, blueprint field and Lean record. The current source has the same six steps and the Lean module named in the return. `baseline.json` retains that entire input locally, and the full six-step argument is reproduced below.

The repair creates two independently usable lemmas, with the old work assigned 1086 characters to the diagram argument (old steps 1--2) and 1484 characters to the criterion (old steps 4--5). The parent retains the application of the pre-existing Tag 05X9 locus theorem and the universal quantifier assembly (old steps 3 and 6). Neither child asserts existence of an open representing a closed-immersion functor. Neither is a clause of that existence statement. The explicit human re-split instruction calls for independently queued arguments; neither new node has proof steps, proof dependencies or proof-origin text. Their proof work is recorded in this report for the next workers, not hidden or erased.

## Argument allocation and retained proof

- Old step 1 (graph as a pullback of the target diagonal) and old step 2 (universal closedness of the graph composite, every base change and the self-product projection) belong to `lem-sfb-closed-graph-universally-closed-diagram`. Its statement explicitly includes the cartesian graph square, not just the permanence conclusion already in Mathlib.
- Old steps 4 and 5 (diagonal isomorphism, cancellation, separatedness, quasi-compactness, finite type, properness, proper-monomorphism criterion, and the converse) belong to `lem-sfb-universally-closed-unramified-radicial-criterion`.
- Old step 3 is new parent step 2; old step 6 is new parent step 3. Parent step 1 applies the diagram child and parent step 3 applies the criterion child with universal closedness already proved.

### Returned step 1

The graph $\Gamma_f:A\to A\times_B C$, with components $(\mathrm{id}_A,f)$, is the pullback of the diagonal $\Delta_q:C\to C\times_B C$ along $(f\circ\operatorname{pr}_1,\operatorname{pr}_2):A\times_B C\to C\times_B C$. Indeed, a map to this pullback is a pair $(a,c)$ with $f\circ a=c$, hence is uniquely determined by $a$. Since $q$ is separated, $\Delta_q$ is a closed immersion; closed-immersion base change therefore makes $\Gamma_f$ a closed immersion.

Cited nodes: `def-weil-proper-morphism`, `def-pc-fibre-product`, `lem-weil-pbc-closed-immersion-base-change`.

### Returned step 2

Closed immersions are universally closed, so $\Gamma_f$ is universally closed. The projection $\pi_C:A\times_B C\to C$ is universally closed by base change of $p$. Thus $f=\pi_C\circ\Gamma_f$ is universally closed: after any base change, each factor sends closed subsets to closed subsets, so their composite does too. Consequently every $f_T$ is universally closed. Also $\operatorname{pr}_1:A\times_C A\to A$ is universally closed by base change of $f$, and $p_2=p\circ\operatorname{pr}_1$ is universally closed by the same composition argument. In particular $p$ and $p_2$ are closed maps, by taking the identity base change.

Cited nodes: `lem-weil-pbc-closed-immersion-proper`, `lem-weil-pbc-universally-closed-base-change`, `def-weil-proper-morphism`.

### Returned step 3

Apply the universal unramified and universally injective locus theorem to $(p,q,f)$. Its local finite type assumption is the hypothesis on $p$; its two closedness assumptions were verified in step 2. It supplies an open subscheme $V\subseteq B$ such that, for every $h:T\to B$, factoring through $V$ is equivalent to $f_T$ being unramified and universally injective.

Cited nodes: `lem-sfb-universal-unramified-radicial-open`.

### Returned step 4

Fix $h:T\to B$ and write $g=f_T$. Suppose $g$ is unramified and universally injective. Its diagonal $\delta:A_T\to A_T\times_{C_T}A_T$ is an open immersion by the definition of unramified and is surjective by the diagonal criterion in the definition of universally injective. A surjective open immersion is an isomorphism: its open image is the whole target. Both projections composed with $\delta$ are the identity, so the two projections are equal. For any $r,s:D\to A_T$ with $g\circ r=g\circ s$, the map $(r,s)$ to the fibre product then gives $r=s$; hence $g$ is a monomorphism. Its diagonal, being an isomorphism, is a closed immersion, so $g$ is separated. Step 2 gives universal closedness, which implies quasi-compactness by the cited universal-closedness lemma. Together with local finite type from unramifiedness, this gives finite type by definition. Hence $g$ is proper. The proper-monomorphism criterion makes $g$ a closed immersion.

Cited nodes: `def-weil-unramified-morphism`, `def-weil-radicial-morphism`, `def-weil-open-immersion`, `def-pc-fibre-product`, `def-weil-proper-morphism`, `def-weil-closed-immersion`, `lem-pc-proper-monomorphism-closed`, `lem-weil-pbc-universally-closed-quasi-compact`, `def-weil-finite-type-morphism`.

### Returned step 5

Conversely, if $g=f_T$ is a closed immersion, the proper-monomorphism criterion gives that $g$ is proper and a monomorphism. Therefore it is locally of finite type. The two projections from $A_T\times_{C_T}A_T$ agree by cancellation of $g$; their common value is inverse to the diagonal, as checked by its two projections and the fibre-product universal property. Thus the diagonal is an isomorphism, in particular an open immersion and surjective. The definitions of unramified and universally injective now give both properties of $g$.

Cited nodes: `lem-pc-proper-monomorphism-closed`, `def-weil-proper-morphism`, `def-pc-fibre-product`, `def-weil-open-immersion`, `def-weil-unramified-morphism`, `def-weil-radicial-morphism`.

### Returned step 6

For each scheme $T$ and morphism $h:T\to B$, step 3 says that $h$ factors through $V$ exactly when $f_T$ is unramified and universally injective. Steps 4 and 5 show that this is equivalent to $f_T$ being a closed immersion. The same open $V$ therefore has the required universal property for all $T$ and $h$.

Cited nodes: .

## Mathlib and duplicate searches

All new search records are exact queries actually executed with the required msearch command and preserved in searches.jsonl. I read both semantic-search phrasings, the Loogle hits, and the grep hits. LeanSearch returned a genuine result for the criterion and rate-limit errors on the diagram and later searches; those errors are recorded as unavailable. LeanFinder and Loogle succeeded for both children, as did grep. Existing parent search entries are retained from the live node rather than claimed as fresh searches.

The important partial matches were read in source: Mathlib/AlgebraicGeometry/Morphisms/Proper.lean:111 gives universal closedness by cancellation of a separated map; Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean:393 gives closed immersion iff proper and mono. Neither gives the second child's diagonal argument. The graph and projection search hits give individual closed-immersion or universal-closedness conclusions; they do not give the entire cartesian graph identification plus self-product argument of the first child in a single specialization. These candidates should be reused by the future child worker. The new statement has no properness or local finite type assumption on p; the proper-source permanence nodes are insufficient for it.

I searched the whole DAG by 04NX, 04XV, 05W8, 05XA, unramified/universally-injective, monomorphism and universal-closedness keywords, and searched the blueprint index by universally closed, unramified, closed immersion, closed graph and these tags. No blueprint node states either new package. The ancestor command returns None, as it did for the inherited parent; the null ancestor and full via chain are preserved and extended. The inherited blueprint place explains the alteration/Hilbert/graph route to this auxiliary Tag 05XA theorem. No unit or chapter route is changed.

## Not duplicates

lem-sfb-closed-graph-universally-closed-diagram vs lem-sfb-universal-closed-immersion-open: the child proves only a graph/self-product universal-closedness package, with no local finite type assumption and no representing open; the parent constructs a representing open.
lem-sfb-closed-graph-universally-closed-diagram vs lemma-nagata-proper-to-separated-target: that node assumes proper source structure map and concludes properness of the horizontal map; the child assumes only universal closedness and also identifies the graph square and self-product.
lem-sfb-closed-graph-universally-closed-diagram vs lem-weil-pbc-proper-over-separated: same stronger proper-source hypothesis; neither the graph cartesian identification nor the self-product conclusion is stated there.
lem-sfb-universally-closed-unramified-radicial-criterion vs lem-pc-proper-monomorphism-closed: that node is 04XV (1) iff (2), involving properness and categorical monomorphisms; the child is 04XV (1) iff (5) with universal closedness fixed, and still needs the unramified/radicial diagonal argument and properness deduction.
lem-sfb-universally-closed-unramified-radicial-criterion vs lem-sfb-universal-closed-immersion-open: the child is a criterion for one universally closed map, without any parameter-base or locus-existence assertion.
lem-sfb-universally-closed-unramified-radicial-criterion vs lem-pc-complete-linear-system-closed: that node concerns extending a linear system on a proper scheme, not a characterization of an arbitrary universally closed morphism.
lem-sfb-universally-closed-unramified-radicial-criterion vs lem-sfb-trait-etale-branch-pinching: that node constructs a curve by trait branch pinching; it does not state the arbitrary-morphism criterion.
lem-sfb-universally-closed-unramified-radicial-criterion vs lem-weil-pbc-closed-immersion-proper: that node gives properness of a closed immersion and compositions with it; it does not identify unramified universally injective maps as closed immersions.

## Review by Q131

I read Tag 05XA (spaces-more-morphisms-lemma-where-closed-immersion), including its whole proof, against the parent statement. It asks precisely for p locally of finite type and universally closed and q separated. It has the same arbitrary-base-change equivalence; no properness, finite presentation, flatness or reducedness assumption is added. I also read Tag 05X9's statement and proof context, Tag 04NX's statement and graph proof, Tag 05W8's criterion, and scheme Tags 04XV and 05VH, including their diagonal arguments.

For new parent step 1 I opened the diagram child's statement and checked that it supplies both closed maps required for 05X9 and universal closedness of each f_T required later. The product is A times_C A, not A times_B A. Its graph square has Gamma_f on the left and Delta_q on the right; the bottom components are (f composed with pi_A, pi_C). The pullback parameter is determined uniquely by a because its other component must equal f composed with a. Separatedness of q therefore gives a closed graph by the base-change lemma; projection pi_C is a base change of p. Closed maps compose after any base change, so the graph factorization gives universal closedness of f. Base change to each C_T gives f_T; base change of f to A gives pr_1 on A times_C A, whose composite with p is universally closed. The identity base changes give closedness of p and p_2. These are exactly the old steps 1--2, fully retained above.

For parent step 2 I opened lem-sfb-universal-unramified-radicial-open, whose statement assumes only locally finite type p, closed p, and closed p_2 and provides one open for all schemes T and maps h. The first assumption is the original hypothesis and the last two are precisely step 1's conclusions. Its unramifiedness and universal injectivity conclusion is the input of step 3, not a claim about fibrewise closed immersions alone. The citation quote copies this complete statement.

For parent step 3 I opened the criterion child's statement: universal closedness is its only standing hypothesis, verified for g=f_T in step 1, and its equivalence is exactly what step 2 needs. I checked the full inherited criterion argument against each old cited statement: def-weil-unramified-morphism supplies local finite type and an open diagonal; def-weil-radicial-morphism supplies surjectivity of the same diagonal; def-weil-open-immersion identifies a surjective open immersion with its whole target; def-pc-fibre-product gives the projection and cancellation arguments. An isomorphism diagonal gives separatedness by def-weil-proper-morphism. The universally-closed-quasi-compact lemma gives the missing quasi-compactness, and def-weil-finite-type-morphism turns it and local finite type into finite type, hence properness. Only then does lem-pc-proper-monomorphism-closed give a closed immersion. Conversely that exact node gives properness and monomorphism, hence local finite type; cancellation identifies both projections, making the diagonal inverse their common value. Its open and surjective diagonal gives unramifiedness and universal injectivity by the same definitions. No inference uses a cited node's proof rather than its statement. This is the entire old steps 4--5, retained above.

Small-case checks: empty A gives the full base open, and both new statements hold for empty morphisms; identity f gives the full base open. Two distinct points mapping to a point have universally closed f but fail universal injectivity and closed immersion, so the criterion does not mistake universal closedness for a closed immersion. Spec(k) into Spec(k[epsilon]/epsilon^2) is a closed immersion and is unramified with surjective-isomorphism diagonal even though it is not flat: no flatness is used. The Frobenius of the affine line in positive characteristic is universally closed and universally injective but not unramified, so it is correctly excluded. With q not separated the graph need not be closed; that assumption remains on the diagram child. The statements apply to arbitrary, including non-reduced, test schemes.

I checked B1--B10: self-contained statements, definitions for each notion, single-escaped TeX, tagged sources, genuinely logged searches, no attachment from a sorry proof, and inherited blueprint references. For C1--C8 I checked every parent citation by opening its statement, wrote verbatim quotes, and retained the precise older component citations in the argument allocation. New children inherit the parent's unit; the existing locus theorem has the same unit, and no off-unit unproved tool is introduced. For D1--D5 the two children carry different arguments of comparable size and neither moves the whole open-locus conclusion; no circular invocation or lemma hidden in a long parent step remains. For E1--E7 I verified the stated hypotheses, the correct relative products/diagonals and arbitrary base changes as detailed above. No source error or statement dispute was found, no target statement was changed, and no SGA source is used. Parent proof steps are all below 2000 characters, with total below 3000.

## Unfinished work

The two new child proofs are deliberately left unsplit for independent workers, as the repair asks. No requested parent work is left incomplete. Delivery verification follows below.
