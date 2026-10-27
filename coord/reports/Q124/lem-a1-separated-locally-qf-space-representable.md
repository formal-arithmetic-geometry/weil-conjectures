# Repair report: lem-a1-separated-locally-qf-space-representable

## Files written

- dag/nodes/sec-purity-real-sheaves/lem-a1-separated-locally-qf-space-representable.json: existing statement node; unchanged statement and statement dependencies; four-step assembly (1627 characters).
- dag/nodes/sec-purity-real-sheaves/lem-a1-separated-lqf-affine-relation-cover.json: new statement-only node, status unsplit; no Mathlib match after two semantic phrasings, Loogle, LeanSearch and grep.
- dag/nodes/sec-purity-real-sheaves/lem-a1-closed-relation-schematic-neighbourhood.json: new statement-only node, status unsplit; no Mathlib match after two semantic phrasings, Loogle, LeanSearch and grep.
- citations.json: one verbatim statement quotation for every node cited by every parent step.

## Attachments

None. I searched lean/WeilConjectures by blueprint tag and by representability/quasi-finiteness terminology. The matching declaration is in lean/Sheaf/AlgebraicGeometry/SeparatedLocallyQuasiFiniteSpaceRepresentable.lean and its proof ends in sorry. It is not finished. The current Lean statement agrees with the item, including arbitrary S and T and the compatibility over T.

## WANTED

None. All sources used below are present locally. No SGA source is used.

## What was wrong and what changed

The released stage-1 repair note requests at least two independent new tasks, not compression of the 6514-character proof. The sandbox contained only dispatcher marker files, with no prior node, report, citations or search log. I therefore copied the current repository item as the repair base. I retained every field not owned by stage 1, the statement, statement dependencies, and the existing proof route. No Lean, repository or launcher file was written and no compiler was run.

The old proof is preserved verbatim below. Task A carries old steps 1-4 (3337 characters): changing the base of the space, the affine target/atlas cover, permanence on its open pieces, the affine closed kernel relation, and the quotient identification after arbitrary scheme base change. Task B carries old steps 5-7 (2016 characters) and the initial schematic-image construction from old step 8: finite clopen restriction, module-generator proof of finite projections, finite locally free affine quotient, open embedding of that quotient, and its schematic image under etale base change. The remaining applications of the gluing criterion and the naturality calculation in old step 8 are exactly the short parent assembly. This distributes two substantial geometric arguments of comparable size; neither new statement claims the parent's global representability conclusion.

## Unfinished work

The two new tasks are intentionally statement-only and ready for independent workers. Their proof seeds are the allocation and verbatim text below. No proof work is hidden in either statement and both have empty proof and proof_deps and null proof_origin.

## Source and duplicate searches

I read GOAL.md, the stage-1 brief, stage document, worker role, SETUP's three levels, the chapter/unit records, and delivery-errors B-E (including the repeated inherited block). I read the released repair note. The current blueprint ancestor is lem-a1-affine-hc0 (main-20261015); it states compact-support degree-zero vanishing and does not itself state either auxiliary. blueprint_refs.py ancestor confirms this ancestor. Full-blueprint searches for locally quasi-finite, affine relation, schematic neighbourhood, space presentation, 03XX, 03XW, 03FY and 0262 found no duplicate of either new task. DAG source-tag and statement searches were made across all chapters. I read the closest candidates listed below, in particular the existing atlas-presentation theorem, which will be reused rather than recreated when Task A is proved.

The actual Mathlib searches are recorded in searches.jsonl and copied into each new node with identical query text and actual returned records. All four services ran. Semantic hits were scheme covers, scheme separatedness/local quasi-finiteness, affine finite-morphism properties, or ordinary etale morphisms. Loogle for the second task returned etale ring quotients and infinitesimal lifting, with unrelated input and output. Grep found only StandardEtalePair ring quotient constructions for that task and no algebraic-space presentations. The second semantic wording again found no algebraic-space statements; none is an exact theorem or one-line specialization. The existing parent's detailed searches are retained, not fabricated or rewritten.

## Not duplicates

lem-a1-separated-lqf-affine-relation-cover vs lem-a1-separated-locally-qf-space-representable: Task A only constructs local closed affine relation presentations and their base-change quotient identities; it does not assert the space or the pieces are schemes.
lem-a1-separated-lqf-affine-relation-cover vs lem-a1-separated-etale-space-scheme: that theorem concludes global representability for a chartwise etale space; Task A treats chartwise locally quasi-finite spaces and only constructs presentations.
lem-a1-closed-relation-schematic-neighbourhood vs lem-a1-separated-locally-qf-space-representable: Task B starts with an affine atlas and closed affine kernel presentation and constructs a pointed finite-clopen quotient diagram and a schematic open image. It does not assert global representability for an arbitrary space over a scheme.
lem-a1-closed-relation-schematic-neighbourhood vs lem-a1-separated-etale-space-scheme: that theorem asserts global schemehood under chartwise etaleness; Task B constructs finite restricted diagrams and pointwise schematic images under local quasi-finiteness.
lem-a1-separated-lqf-affine-relation-cover vs lem-a1-space-affine-atlas-open-cover: that node supplies only the affine target/atlas cover, not inherited separated/local quasi-finite properties, closed affine kernel pairs, or base-change quotient identifications.
lem-a1-separated-lqf-affine-relation-cover vs lem-a1-etale-atlas-presentation: that node starts with a single atlas and supplies a quotient and kernel pair. It does not construct a cover with affine targets and affine closed relations or prove permanence of both properties on it.
lem-a1-separated-lqf-affine-relation-cover vs lem-trf-etale-quotient-affine-open-cover: that node starts with an arbitrary etale relation and covers its sheaf quotient by affine-chart quotients; it neither gives closed affine relations over affine target opens nor retains local quasi-finiteness and separatedness.
lem-a1-separated-lqf-affine-relation-cover vs lem-a1-space-separated-lqf-permanence: permanence gives properties of chosen opens of a base change, not their existence with affine atlases, closed affine kernel relations and quotient identities.
lem-a1-closed-relation-schematic-neighbourhood vs lem-a1-proper-etale-relation-finite-neighbourhood: that node gives the finite clopen pieces. Task B additionally proves finite locally free projections, affine representability of their quotient, open embedding into the base-changed space, and a schematic image in the original space.
lem-a1-closed-relation-schematic-neighbourhood vs lem-a1-finite-flat-affine-relation-quotient: that node starts with finite locally free projections and constructs their affine quotient. Task B must construct those inputs after pointed etale localization, embed the quotient, and descend its image.
lem-a1-closed-relation-schematic-neighbourhood vs lem-a1-etale-quasi-affine-image-scheme: that node starts with a quasi-affine open in a base change. Task B constructs that open from a closed affine relation with finite clopen restriction; it also retains the finite diagram witnesses.

## Review by Q124

I read spaces-morphisms.tex Tag 03XX (proposition-locally-quasi-finite-separated-over-scheme), including all five proof paragraphs. For Task A I also read spaces-properties.tex Tag 03FY (lemma-union-of-quasi-compact) and spaces.tex Tag 0262 (lemma-space-presentation). For Task B I read more-groupoids.tex Tag 03X5 (lemma-quasi-finite-over-base-j-proper), groupoids.tex Tag 03BM (proposition-finite-flat-equivalence), spaces.tex Tag 02WU (lemma-finding-opens), and spaces-morphisms.tex Tag 03XW (lemma-neighbourhood-scheme). I checked each tag against tags/tags rather than relying on section numbers. The task sources name the precise paragraphs of 03XX, and these auxiliary sources supply the same route as the old split.

Parent step 1 uses Task A's statement, not its future proof: it explicitly returns the covering, affine data, property permanence and quotient/base-change identities. Its hypotheses are verbatim the item's two assumptions; no quasi-compactness or Noetherian condition is added. Parent step 2 uses Task B, whose inputs are all among Task A's conclusions. In particular the diagonal belongs to X_i/T_i, the closed relation map has target U_i times over T_i with U_i, and U_i/T_i is locally quasi-finite. The conclusion supplies W for every atlas point, so surjectivity covers the space. On a scheme test H, membership in a representable open is checked on residue-field points of H; the pullback opens therefore cover H. This is the exact functor-covering clause used by the gluing criterion.

Parent step 3 uses the actual statement of def-trf-algebraic-space for the fppf sheaf property and the actual clauses (1), (2a), (2b), (2c) of lem-pc-schemes-criterion for representability. The first application has representable W_i,u, open inclusions and the sectionwise covering established in step 2. The second has representable X_i, open inclusions and the sectionwise covering explicitly returned by Task A. The criterion is declared as a generic off-unit tool. Parent step 4 is elementary: evaluating the natural transformation at id_Z defines g and naturality proves its value on every a:H to Z. No uncited fullness theorem is used.

For Task B I checked the crucial inputs to 03X5: affine U,R,T, locally quasi-finite U/T (apply the chartwise assumption to the atlas), etale projections and a closed relation. In 03BM the projection finiteness follows by the written module-generator argument, not from an unjustified finiteness of the whole space. In 02WU the original projections are etale and surjective, the clopen inclusion is flat and locally of finite presentation, and the relation is the FULL restriction, not an arbitrary subrelation. The target quotient is the base-changed X because it is its atlas kernel pair. The quotient is affine over affine T', hence quasi-affine by the identity open immersion, so 03XW has exactly its four hypotheses. That theorem returns a schematic image; it is not etale descent of arbitrary schemes. No theorem being proved is used by either new task.

Small cases: E empty or T empty gives an empty cover and the empty representing scheme; the pointwise claim for an empty atlas is vacuous. For identity X=T with affine atlas T the relation is the diagonal and T'=T, U'=T, R'=T gives Q=T and W=T. For a finite etale affine atlas the witnesses may be the whole finite pieces; projection finiteness remains valid. An infinite disjoint union of points over a field is locally quasi-finite but not quasi-compact: the cover is set-indexed and the tasks only make individual U_i, R_i or restricted pieces finite, never the whole E. I also checked that nilpotents do not alter the open factorization test: factoring into an open subscheme depends on its underlying point image, unlike factoring through a closed subscheme. There is no statement dispute or changed target, and no step exceeds 2000 characters after repair.

The substantive correction is the requested decomposition. The old eight arguments are not replaced by a compressed proof: they are preserved below for the next workers, assigned to two named statement-only tasks, while the parent only assembles their conclusions. I also compared each newly cited statement with citations.json; every quote is verbatim. DAG dependencies will be checked by the required server dry run.

## Allocation and verbatim old proof

Task A: old steps 1-4. Task B: old steps 5-7 and old step 8 through the sentence `In particular $x\in W$.` The two gluing applications and the final naturality argument from old step 8 are retained in parent steps 3-4, with the sectionwise covering verification made explicit in step 2. These proof seeds are in this report only, not in the unsplit node statements.

### Old step 1

Regard $E$ as an algebraic space over $T$. Indeed its fppf sheaf is the sheaf of sections of $E$ with the specified composite to $T$; the sheaf condition restricts to that fibre. Its relative diagonal is a base change of its diagonal over $S$, and its original atlas, equipped with the composite map to $T$, is still representable surjective etale [def-trf-algebraic-space, lem-trf-space-fibre-products-etale-covers]. Apply [lem-a1-space-affine-atlas-open-cover] over $T$. It gives open subspaces $E_i$ covering $E$, affine opens $T_i\subseteq T$ through which $E_i$ maps, and affine schemes $U_i$ with representable surjective etale maps $U_i\to E_i$. It is enough to prove each $E_i$ is a scheme by [lem-pc-schemes-criterion]: the fppf sheaf is a Zariski sheaf, the inclusions are representable open immersions, and the pullbacks of this open covering along any scheme section cover that scheme. These are precisely its three hypotheses.

Cited statements: def-trf-algebraic-space, lem-trf-space-fibre-products-etale-covers, lem-a1-space-affine-atlas-open-cover, lem-pc-schemes-criterion.

### Old step 2

Each $E_i\to T_i$ satisfies the hypotheses of the item. For a representable etale scheme chart $V\to E_i$, the composite $V\to E_i\to E$ is again representable etale: an open immersion is etale and etale composites are etale on scheme tests [lem-weil-pbc-etale-composition-cancellation]. Thus $V\to T$ is locally quasi-finite by hypothesis; apply clause (2) of [lem-weil-pbc-separated-lqf-base-change] along $T_i\to T$. The source of this base change is $V\times_TT_i=V$, since $V\to T$ factors through the open $T_i$, so $V\to T_i$ is locally quasi-finite. The relative diagonal of $E_i/T_i$ is the pullback of that of $E/T$ to $E_i\times_T E_i$: the fibre products over $T_i$ and $T$ agree because $T_i\to T$ is a monomorphism. Its scheme tests are closed immersions by [lem-weil-pbc-closed-immersion-base-change]. We henceforth write $X\to T$ and $U\to X$ for one such piece; both $T$ and $U$ are affine.

Cited statements: lem-weil-pbc-etale-composition-cancellation, lem-weil-pbc-closed-immersion-base-change, def-trf-algebraic-space, lem-weil-pbc-separated-lqf-base-change.

### Old step 3

Put $R=U\times_XU$. The diagonal representability in [def-trf-algebraic-space] makes this a scheme. Its projections $s,t:R\to U$ are etale and surjective by base change of the atlas [lem-trf-space-fibre-products-etale-covers]. By the fibre-product universal property it is an equivalence relation, and the map $j:R\to U\times_TU$ is the scheme base change of $\Delta_{X/T}$; it is a closed immersion by the assumed testwise closedness. The affine fibre-product formula [lem-weil-pbc-fibre-product-affine-spectra] makes $U\times_TU$ affine. The affine criterion for a closed immersion [def-weil-closed-immersion] therefore makes $R$ affine. Finally $U\to T$ is locally quasi-finite by the chartwise hypothesis applied to $U\to X$.

Cited statements: def-trf-algebraic-space, lem-trf-space-fibre-products-etale-covers, lem-weil-pbc-fibre-product-affine-spectra, def-weil-closed-immersion.

### Old step 4

The fppf quotient sheaf $U/R$ is $X$. To verify this identification, a section $x\in X(H)$ lifts on the covering $H\times_XU\to H$, which is a surjective etale morphism of schemes by [def-trf-algebraic-space]. Such a morphism is an fppf covering since etale means flat and locally of finite presentation [def-weil-etale-morphism, def-pc-fppf-site]. Two lifts have the same image exactly when they are related by $R(H)=U(H)\times_{X(H)}U(H)$. These local bijections glue by the sheaf axiom, giving $U/R\simeq X$. The same verification applies after any base change to a scheme over $T$, since the atlas remains etale surjective [lem-trf-space-fibre-products-etale-covers]. The quotient and its universal property are the ones in [lem-trf-etale-relation-quotient].

Cited statements: def-trf-algebraic-space, def-weil-etale-morphism, def-pc-fppf-site, lem-trf-space-fibre-products-etale-covers, lem-trf-etale-relation-quotient.

### Old step 5

Fix a point $x\in|X|$ and choose $u\in U$ mapping to it, using surjectivity of the atlas. All hypotheses of [lem-a1-proper-etale-relation-finite-neighbourhood] hold by step 3: $U,R,T$ are affine, $U/T$ is locally quasi-finite, the relation map is closed, and $s,t$ are etale. Obtain an affine etale neighbourhood $(T',p')\to(T,p)$, a point $u'$ over $u$, and clopen pieces $U',R'$ finite over $T'$ such that $R'$ is the full restricted relation on $U'\subset U\times_TT'$. Its projections $s',t'$ are etale. Here $p$ is the image of $u$ in $T$; no finiteness of the entire atlas or of $X/T$ has been assumed.

Cited statements: lem-a1-proper-etale-relation-finite-neighbourhood.

### Old step 6

The finite morphisms $U',R'\to T'$ have affine sources because $T'$ is affine [def-weil-finite-integral-morphism]. Write their coordinate rings as $A',B'$ over $D=\Gamma(T',\mathcal O_{T'})$. The finite set generating $B'$ as a $D$-module also generates it as an $A'$-module via either projection, since $D\to B'$ factors through either map $A'\to B'$. Thus $s',t'$ are finite. They are etale by step 5, hence flat and locally of finite presentation by [def-weil-etale-morphism]. They are therefore finite locally free by [def-pc-finite-locally-free]. Apply [lem-a1-finite-flat-affine-relation-quotient] over $T'$: the quotient $Q=U'/R'$ is an affine scheme.

Cited statements: def-weil-finite-integral-morphism, def-weil-etale-morphism, def-pc-finite-locally-free, lem-a1-finite-flat-affine-relation-quotient.

### Old step 7

By [lem-trf-etale-relation-finding-opens], the inclusion $U'\to U\times_TT'$ induces an open immersion $Q\to (U\times_TT')/(R\times_TT')$. Its hypotheses hold: the original projections after base change are etale and surjective by [lem-trf-space-fibre-products-etale-covers], so they are flat and locally of finite presentation [def-weil-etale-morphism]; the clopen inclusion of $U'$ is an open immersion, hence etale by [lem-weil-pbc-etale-composition-cancellation], hence flat and locally of finite presentation as well; and the relation on $U'$ is the full restricted relation from step 5. By step 4 the target quotient is $X_{T'}$. Thus the affine scheme $Q$ represents an open subspace $V'\subset X_{T'}$. Its point coming from $u'$ maps to $x$.

Cited statements: lem-trf-etale-relation-finding-opens, lem-trf-space-fibre-products-etale-covers, def-weil-etale-morphism, lem-weil-pbc-etale-composition-cancellation.

### Old step 8

The map $V'\to T'$ is a morphism between affine schemes; its inverse images of principal affine opens are spectra of localizations of its coordinate ring, so it is affine, and in particular quasi-affine (factor it as its identity open immersion followed by this affine map). Apply [lem-a1-etale-quasi-affine-image-scheme] to $X\to T$, the affine etale map $T'\to T$, and $V'$. It supplies a representable open subspace $W\subseteq X$ whose underlying open set is the image of $|V'|$. In particular $x\in W$. Since $x$ was arbitrary, representable opens cover $X$, and [lem-pc-schemes-criterion] makes $X$ representable: it is a Zariski sheaf and, for each section over a scheme $H$, the base changes of these representable opens are open subschemes covering $H$, so the required functor covering condition holds. Apply this to every $E_i$ from step 1 and use the same criterion once more to obtain a scheme $Z$ representing $E$. For the composite natural transformation $\alpha:h_Z\simeq E\to h_T$, define $g=\alpha_Z(\mathrm{id}_Z):Z\to T$. Naturality gives $\alpha_H(a)=g\circ a$ for every $a:H\to Z$, so the representing isomorphism is over $T$, as required.

Cited statements: lem-a1-etale-quasi-affine-image-scheme, lem-pc-schemes-criterion, def-trf-algebraic-space.
