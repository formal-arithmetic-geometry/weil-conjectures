# Q114 repair of lem-pur-frame-independence

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-frame-independence.json: existing statement, five-step assembly (2515 characters), status split.
- dag/nodes/sec-smooth-purity/lem-pur-kummer-product-unit-permutation.json: statement, status unsplit, no Mathlib match.
- dag/nodes/sec-smooth-purity/lem-pur-kummer-product-shear-homotopy.json: statement, status unsplit, no Mathlib match.
- citations.json: verbatim statement excerpts for every citation of every assembly step.
- searches.jsonl: retained actual search-command records; repair.py: sandbox-only generation script.

## Attachments

None. The project declaration WeilConjectures.PurityFiniteSetting.frameClass_independent in lean/Sheaf/Paper/PurityFrameIndependence.lean:105 still has sorry. I searched lean/WeilConjectures by the blueprint tag and by frameClass, frame independence and fundamentalClass, and read RegularImmersion.lean:412,683 and FrameIndependence.lean:233,391. The overlap theorem requires smoothness over k, regular Z and an affine weakly regular first frame, which are not the arbitrary smooth-relative-base hypotheses of this item. The universal matrix theorem uses the upstream etale normalized-Kummer/six-functor objects; it is not a declaration about the concrete finite pro-etale product of def-pur-frame-class. Identifying those coefficient objects and products is not an attachment or a one-line Mathlib specialization.

## WANTED

None. All source places used are available locally.

## What was wrong and what changed

The returned item had 5628 characters of proof and did not distribute its two operation arguments to independent workers. The repair adds two comparable tasks: old steps 3--4 are the unit/permutation argument (1512 characters), and old steps 5--6 are the shear interpolation argument (1438 characters). Both new nodes have self-contained statements, actual recorded searches, empty proof/proof_deps and null proof_origin, and status unsplit. Their statements concern arbitrary tuples on arbitrary k-schemes, so neither is the whole frame-independence item. The parent retains its local-generator argument, spreading of all finite coefficients and equations, the bottom-degree descent hypothesis and the neighborhood comparison; it composes the two new results along the local chain.

There was no retained node/report/search file in this sandbox at start, only .brief2 through .brief5. I used the current repository copy as the returned head, preserving every imported and maintainer field. In particular the current statement_change dated 2026-10-22 and hfinite in the Lean record are retained unchanged. No stage-2 work, compilation, build, repository writes or launcher changes were performed.

## Not duplicates

lem-pur-kummer-product-unit-permutation vs lem-pur-frame-independence: only changes by units and permutations of arbitrary tuples, not arbitrary equal-ideal frames or their local-to-global comparison.
lem-pur-kummer-product-shear-homotopy vs lem-pur-frame-independence: a single explicit polynomial shear and its interpolation class on an affine line, not arbitrary changes of frame or descent.
lem-pur-kummer-product-unit-permutation vs lem-pur-supported-cup-functoriality: the existing node supplies general product, sign, Kummer and pullback laws; the new node proves the concrete simultaneous unit/permutation equality, including annihilation of extended unit boundaries and canonical rank-one twist symmetry.
lem-pur-kummer-product-unit-permutation vs prop-pur-affine-space-purity-compatibilities: the latter concerns the smooth-purity comparison gamma for coordinate affine-space projections, not products of boundaries for arbitrary regular functions on X; applying it would replace the stipulated argument.
lem-pur-kummer-product-shear-homotopy vs lem-pur-supported-affine-line-homotopy: that node only identifies projection pullback and section pullback on fixed-support cohomology; it does not construct the interpolation tuple, establish its scheme-theoretic support or identify the individual Kummer-boundary endpoint products.
lem-pur-kummer-product-shear-homotopy vs lem-pur-supported-cup-functoriality: the existing node gives naturality but not the fixed-support polynomial interpolation construction or equality of its endpoint classes.

I searched the whole DAG statement text for shear, unit multiple, permutation/Kummer and frame/monomial, plus whole blueprint searches for frame, shear, generating tuple, permutation, Kummer and unit multiple. No other node states either new assertion. The nearest blueprint ancestor is lem-pur-frame-independence; both from.via lists are empty and same_as is empty. The source is the exact blueprint operation paragraph; these are agent-formulated consequences, not falsely attributed Stacks theorems. The general Stacks ingredients already have nodes (Kummer, localization, cup symmetry, supported homotopy).

## Mathlib search reading

The exact queries, tools and returned names are recorded in each new node and in searches.jsonl. Unit/permutation: LeanSearch returned ordinary finite products and symmetric tensors (Equiv.Perm.prod_comp and SymmetricPower.tprod_equiv, whose Mathlib source I read at Algebra/BigOperators/Group/Finset/Defs.lean:421 and LinearAlgebra/TensorPower/Symmetric.lean:123); these do not encode varying supports, localization boundaries or twists. The second semantic phrasing returned Selmer/class groups and group cohomology. Shear: both LeanFinder phrasings returned root-system/Witt-polynomial/structure-sheaf/cotangent arithmetic, not supported cohomology. LeanSearch for shear was rate limited and is recorded unavailable. Both Loogle queries ran with no hits; prescribed Mathlib grep commands ran with no hits. Existing item searches were read and retained, not invented or rerun. The extra logged local-tuple searches were exploratory; no third node was created, since spreading a finite chain is a short argument from the existing local-ring tuple lemma.

## Review by Q114

I read the current main-20261015 statement and full proof of frame independence, the older imported statement/proof, the smooth-purity chapter and sk-prop-a1-kummer unit records, and each cited statement in the current DAG. The blueprint's route is unit changes, permutations and shears; I retained it. Its strict-local-neighborhood, general Smith-form and constant-sheaf claims had already been repaired in the returned proof; those repairs are retained, including the explicit finite-stalk-dimension condition now needed for bottom-degree descent. There is no new statement dispute and the parent statement is unchanged.

Step 1 uses def-pur-frame-class exactly for the individual-boundary product and its empty-product convention; def-weil-pbc-etale-site explicitly says fibre products are etale site objects. Step 2 uses lem-pur-relative-support-bottom-descent exactly for testing equality on a cover with the displayed finite ambient stalks, r=c, pure codimension and c generators. The finite module I_x has the two c-generator tuples, so lem-pur-local-generating-tuples applies even when the ideal is zero or the generating tuples are nonminimal. Coefficients and unit inverses are finitely many stalk elements, represented on a common open; inverse and final-tuple equations hold after further shrinking. This is the written elementary spreading argument, not an unstated strict-henselian scheme argument. The cited cup-functoriality statement explicitly includes arbitrary scheme pullbacks, their boundaries and products, so it identifies restrictions of each intermediate frame class. Open restriction preserves etaleness and the ideal.

Step 3 applies the new unit/permutation assertion to the current tuple, X=N, with sigma the identity for a unit operation and units all 1 for a permutation. Its arbitrary-scheme statement needs no extra finiteness, regularity or constant-twist choice. K_N is exactly the ordered defining formula of def-pur-frame-class. Step 4 applies the new shear assertion with the distinct indices in the local chain and its actual section a; the old proof supplies its entire fixed-support interpolation and endpoint argument, preserved below. It does not call A1_N an etale frame. Step 5 composes the finite equalities and uses the bottom-descent equality clause again, with the same hypotheses as step 2; the etale fibre product and cup naturality statements supply the common-neighborhood comparison. Every uses entry has a verbatim statement excerpt in citations.json, including all boundary/product pullback clauses actually used. No step takes a construction merely from a cited proof.

For the first new node I read the source's Unit multiples and Permutations paragraphs and the precise statements of def-pur-frame-class, lem-pur-supported-cup-functoriality and thm-pur-with-support-exactness. A unit class extending across X has zero individual localization boundary; each degree-two swap has sign +1. The rank-one twist symmetry is checked with a local generator, so no chosen global trivialization is added. For the second I read the Elementary shears paragraph and the supported-affine-line-homotopy statement: it works for arbitrary X, C, q and r on the finite pro-etale site, and says each section is inverse to the canonical projection pullback. The polynomial shear has the same ideal by subtraction, not just the same topological zero set. Individual boundary naturality gives both endpoints; the inverse sections give their equality. The full old arguments are reproduced below for the future proof workers; new node files intentionally contain statements only.

I tested c=0 (empty tuple and unit), c=1 (only unit changes/permutations and no shear), c=2 adjacent swaps with sign (-1)^4=1, a=0, arbitrary nonunit a, the zero ideal, unit ideal/empty support, nonreduced zero schemes and disconnected X. The shear inverse is subtraction by a h_j, valid also with nilpotents. No field, PID, regular-sequence, smoothness or finite-type hypothesis enters either operation calculation. Finite coefficients with ramified n are the concrete classes of def-pur-frame-class for every n, not an unsupported free change of coefficient ring. The two extracted arguments have comparable proof sizes, and neither includes the parent's local-generator or descent argument. Each non-elementary assembly step is below 2000 characters and the whole assembly is below 3000. I checked delivery-errors B--E: self-contained statements/definitions; real searches and unavailable verdicts; exact citations and hypotheses; no duplicate or circular replacement; no hidden scheme/support identification. The definition node and new nodes do not depend on frame independence, so no new cycle is introduced. No SGA source is used.

## Preserved arguments for the parallel proof workers

The following are the complete current repository proof texts, copied without abridgement. Steps 3--4 are assigned to lem-pur-kummer-product-unit-permutation; steps 5--6 to lem-pur-kummer-product-shear-homotopy; steps 1--2 and 7 remain the parent assembly. They are report guidance, not proofs recorded on the new statement-only nodes.

### Returned step 1

Work with two length-$c$ frames $f,g$ on the same etale neighborhood $U$, generating the same ideal $I$ of $Z_U$. This is the meaning of frame independence; for frames on different etale neighborhoods compare their restrictions on the fibre product over $V$, which is an object of the small etale site by [def-weil-pbc-etale-site]. Use exactly the individual-boundary, ordered-product construction of [def-pur-frame-class]. If $c=0$, both classes are the specified empty product $1$ in $H^0(U,A)$, so they agree. Henceforth $c>0$.

Cited statements: def-pur-frame-class, def-weil-pbc-etale-site.

### Returned step 2

Apply [lem-pur-relative-support-bottom-descent] directly to the displayed frame data $(V,B,Z,U,c)$, with $r=c$ and the finite-dimensional ambient-stalk hypothesis, to test equality of our degree-$2c$ supported classes on an etale cover; a Zariski cover suffices. At any point $x\in U$, the germs of $f,g$ generate the same finite module $I_x$ over the local ring $\mathcal O_{U,x}$. By [lem-pur-local-generating-tuples], a finite succession of permutations, unit multiples and shears transforms these germs into one another. This finite succession spreads to an affine open neighborhood $N$ of $x$ in $U$ (spreading the finite generator changes needs no further finiteness hypothesis): represent every coefficient and unit inverse as a section on a neighborhood; the finitely many equalities hold after shrinking because equality in a stalk means equality on a smaller neighborhood. $N\to U\to V$ is etale, so each intermediate tuple is again a frame on $N$. On that neighborhood every operation is invertible, preserves the generated ideal, and transforms the actual sections $f$ into $g$. Thus it remains to check these three operations on an open neighborhood. The pullback and boundary/product compatibilities of [lem-pur-supported-cup-functoriality] identify the restriction of each frame class with the same construction on that neighborhood. No strictly henselian local scheme is treated as an etale neighborhood, and no general Smith normal form is used.

Cited statements: def-pur-frame-class, lem-pur-relative-support-bottom-descent, lem-pur-local-generating-tuples, lem-pur-supported-cup-functoriality.

### Returned step 3

For a unit multiple $f_i'=u f_i$, the divisor $D_i$ and its complement $W_i$ are unchanged. By [lem-pur-supported-cup-functoriality], $\kappa_{W_i}(u f_i)=\kappa_{W_i}(u)+\kappa_{W_i}(f_i)$ and $\kappa_{W_i}(u)$ is the restriction of $\kappa_U(u)$. Exactness of [thm-pur-with-support-exactness] shows that its boundary in $H^2_{D_i}(U,A(1))$ is zero. Additivity of that boundary therefore leaves $\alpha_i$ unchanged, and hence leaves its ordered product with the other factors, the class of [def-pur-frame-class], unchanged.

Cited statements: lem-pur-supported-cup-functoriality, thm-pur-with-support-exactness, def-pur-frame-class.

### Returned step 4

For an adjacent transposition, the corresponding supported factors in [def-pur-frame-class] both have cohomological degree $2$ and twist $1$. Associativity and graded symmetry in [lem-pur-supported-cup-functoriality] give sign $(-1)^{2\cdot2}=1$, after the canonical support-intersection and twist identifications. For the twists: $A(1)$ is locally free of rank one over $A$ (as recorded in [def-pur-frame-class]), and on a cover where $A(1)\cong A$ with local generator $e$ the swap sends $ae\otimes be\mapsto be\otimes ae=ab\,e\otimes e$, so the swap of two adjacent factors of $A(1)^{\otimes c}$ is the identity and the identification with $A(c)$ is unaffected. The supports $D_i\times_UD_{i+1}$ and $D_{i+1}\times_UD_i$ are the same closed subscheme of $U$. Thus the class is unchanged. Every permutation is a succession of adjacent transpositions (move the entry in the first desired position to the front, then repeat on the remaining list), so all permutations preserve the class.

Cited statements: def-pur-frame-class, lem-pur-supported-cup-functoriality.

### Returned step 5

For the shear $f_i'=f_i+a f_j$, where $i\ne j$, put $T=\mathbf A^1_U$ with projection $p$ and coordinate $t$. The tuple $F(t)$ obtained by replacing $f_i$ by $f_i+t a f_j$ has ideal $I\mathcal O_T$: containment in one direction is immediate, and in the other direction recover $f_i$ by subtracting $t a f_j$. Its common zero scheme is therefore $Z_T=p^{-1}Z_U$. Construct $\eta\in H^{2c}_{Z_T}(T,A(c))$ by the same explicit formula as [def-pur-frame-class]: on the complement of each individual zero scheme take the Kummer class of that function, its localization boundary, then the ordered supported product. This formula is available for functions on $T$ by [lem-pur-supported-cup-functoriality] and [thm-pur-with-support-exactness]. We do not assert that $T\to V$ is etale or call it an etale frame. Pullback along the zero and unit sections, using those same compatibility laws, gives respectively $s_0^*\eta=\operatorname{cl}(f)$ and $s_1^*\eta=\operatorname{cl}(f')$.

Cited statements: def-pur-frame-class, lem-pur-supported-cup-functoriality, thm-pur-with-support-exactness.

### Returned step 6

Apply [lem-pur-supported-affine-line-homotopy] to $(U,Z_U)$ in degree $2c$ and twist $c$. Write $\eta=p^*\xi$ using its canonical isomorphism. Since $p s_0=p s_1=\mathrm{id}_U$, pullback composition from [lem-pur-supported-cup-functoriality] gives $s_0^*\eta=\xi=s_1^*\eta$. Combined with step 5 this proves shear invariance. This uses projection invariance of supported cohomology, not a claim that a global cohomology group is a constant sheaf on $\mathbf A^1_U$.

Cited statements: lem-pur-supported-affine-line-homotopy, lem-pur-supported-cup-functoriality.

### Returned step 7

On each of the neighborhoods from step 2, successively apply steps 3--6 along the finite sequence of generator changes to obtain equality of the two frame classes. By [lem-pur-relative-support-bottom-descent] these local equalities give equality in $H^{2c}_{Z_U}(U,A(c))$. In the comparison of different neighborhoods from step 1, the common fibre product is an etale object by [def-weil-pbc-etale-site] and its pulled-back tuples define the pulled-back frame classes by [lem-pur-supported-cup-functoriality]. The equality just proved applies there as well. Thus the class depends only on the defining ideal, with the canonical etale-restriction interpretation of [def-pur-frame-class].

Cited statements: lem-pur-relative-support-bottom-descent, lem-pur-supported-cup-functoriality, def-pur-frame-class, def-weil-pbc-etale-site.

## What remains

The two new nodes are intentionally unsplit tasks for other workers. No requested repair point remains. Validation and delivery results will be appended after the required server dry run.
