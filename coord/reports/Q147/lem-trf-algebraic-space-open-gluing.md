# Repair report: lem-trf-algebraic-space-open-gluing

## Files written

- dag/nodes/sec-trace-formula/lem-trf-algebraic-space-open-gluing.json: statement retained verbatim; four-step assembly.
- dag/nodes/sec-trace-formula/lem-trf-open-sheaf-coproduct-base-change.json: new statement, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-open-cover-representable-diagonal.json: new statement, unsplit; no Mathlib match.
- citations.json: verbatim statement quotations for all parent step citations.

## Attachments

None. The project declaration AlgebraicGeometry.algebraicSpace_of_open_gluing in lean/Sheaf/AlgebraicGeometry/AlgebraicSpaceOpenGluing.lean has a sorry. Searches of WeilConjectures by blueprint tag, name and concept found no exact finished declaration; no Lean was written or compiled.

## WANTED

None. All sources used are present locally.

## What was wrong and what changed

The returned seven-step proof contained 5562 characters of mathematical work. The repair creates two separate proof jobs rather than compressing that work: coproduct base change (old steps 1, 2, 4; 2502 characters), and open-cover/diagonal descent (old steps 3, 5; 1650 characters). The existing partition lemma is reused; the elementary covering assembly and original etale/atlas arguments remain in the parent. No statement dispute or source correction was needed. The sandbox had only dispatcher marker files when this repair began, so the read-only current main node, which contains the exact returned seven steps and the prior source/search/Lean records, supplied the baseline. All its non-proof metadata is retained, including prior review history; no repository or launcher file was changed.

The two new statements have strictly smaller hypotheses and tasks than the parent. The coproduct node does not assume local surjectivity, algebraicity of the summands, or algebraicity of H; its conclusion is an explicit relative scheme representation. The diagonal node has no H and no atlas hypotheses; it assumes local membership in open subsheaves with representable diagonals and constructs the scheme tests of the diagonal. Neither node states that F is an algebraic space. They are independent and can be worked on simultaneously.

## Preserved arguments for the two future workers

These are report-only proof materials. The new node files deliberately have no proof steps or proof dependencies. The full original arguments below have not been shortened.

### lem-trf-open-sheaf-coproduct-base-change

Read spaces.tex Tag 02WR, first paragraph (lemma-glueing-algebraic-spaces), descent.tex Tag 023Q (lemma-fpqc-universal-effective-epimorphisms), sites.tex Tags 00WI/00WK (lemma-colimit-sheaves/lemma-sections-sheafification). The old reference to covering in Step 3 is not needed for the representation: only the open schemes V_i are needed; the covering conclusion belongs to the other node. The existing lem-trf-fppf-sheaf-coproduct-partition is available as a stronger local-representative tool. Naturalness in T follows by applying the same section construction after precomposition: all assignments use restriction, the given pullback equations and the uniquely glued maps.

Original step 1: First, representable functors $h_Z$ on the big fppf site are sheaves. Indeed, for any fppf covering and any affine open $A$ in its target, [lem-pc-fppf-affine-refinement] supplies finitely many affine opens of the covering schemes above $A$ whose images cover $A$. Thus the covering satisfies exactly [def-weil-pbc-fpqc-covering]. Apply [lem-weil-pbc-fpqc-representable-descent] to descend compatible maps into $Z$. For maps over $S$, the descended map is over $S$ because its composite to $S$ agrees with the prescribed structural map after the covering, and the uniqueness assertion of the same descent lemma detects this equality. This works for the empty target as well.

Original step 2: Put $H=\coprod_iF_i$ in sheaves and let $P(T)=\coprod_iF_i(T)$ be the sectionwise presheaf coproduct. The universal property in [def-weil-pbc-sheafification] identifies $P^\#$ with $H$: a map from either to a sheaf $K$ is exactly a family of maps $F_i\to K$. Consequently [lem-weil-pbc-site-sheafification-sections-local] says that a section of $H$ is fppf locally represented by a section of one $F_i$, and equality of two such representatives in $H$ holds locally already in $P$. In particular unequal indices can coincide only on the empty scheme: every nonempty scheme admits no empty fppf covering, and restriction in $P$ preserves the index.

Original step 4: Let $E_T=H\times_Fh_T$. It is a sheaf: matching sections in the two factors glue uniquely, and their equality in $F$ persists by the sheaf uniqueness axiom [def-weil-pbc-sites-and-cohomology]. Form the scheme $C_T=\coprod_iV_i$ by [lem-weil-pbc-scheme-coproduct-family]. Its coprojections have disjoint open images covering $C_T$. The maps $h_{V_i}\to E_T$ therefore define a natural map $h_{C_T}\to E_T$: for $W\to C_T$, restrict to the inverse images of those disjoint opens and glue the resulting sections of $E_T$. This uses [lem-pc-zariski-coverings-are-fppf]. Every section $(a,t)$ of $E_T(W)$ fppf locally has $a$ in one $F_i$ by Step 2; the equality over $F$ then gives a map to $V_i$, hence to $C_T$. Any two local maps inducing $(a,t)$ agree: by Step 2 their indices agree after a further fppf refinement, and with the same index their maps to $V_i$ agree because $F_i\to F$ is a subfunctor and $V_i$ is its pullback to $T$. The sheaf property of $h_{C_T}$ from Step 1 glues these maps uniquely. The resulting inverse is natural and proves $h_{C_T}\simeq E_T$ over $h_T$. Thus $q:H\to F$ is representable, and its scheme test is $C_T\to T$, which is surjective by Step 3.


### lem-trf-open-cover-representable-diagonal

Read spaces.tex Tag 02WR, first paragraph after the representation sentence and the entire second paragraph, and schemes.tex Tag 01JJ (lemma-glue-functors). In this independent job the stated local-membership hypothesis supplies the covering directly; references below to H and Step 2 are the way the original parent established that hypothesis, not additional assumptions of this node. Only representability of the diagonals of F_i is needed, not their atlases. Representables are Zariski sheaves by scheme morphism gluing; their fppf sheaf property is also established in the coproduct node proof materials below.

Original step 3: Fix a scheme $T$ and a map $h_T\to F$. By the representable-open hypothesis, $h_T\times_FF_i=h_{V_i}$ for an open subscheme $V_i\subseteq T$, using [def-trf-algebraic-space] and [def-weil-open-immersion]. The sheaf surjectivity of $H\to F$ gives fppf local lifts of this map to $H$; refining by Step 2 gives an fppf covering $T_a\to T$ whose maps to $F$ factor through some $F_{i(a)}$. Each $T_a\to T$ therefore factors through $V_{i(a)}$ by the fibre-product universal property. The family $T_a\to T$ is jointly surjective by [def-pc-fppf-site], so $T=\bigcup_iV_i$. All such tests, including their further pullbacks, give open coverings in this way.

Original step 5: For schemes $T,T'$ mapping to $F$, set $G=h_T\times_Fh_{T'}$ and $G_i=G\times_FF_i$. Write $V_i=T\times_FF_i$ and $V'_i=T'\times_FF_i$ as in Step 3. Since $F_i\subset F$ is monic, the sectionwise pullback equations give $G_i=h_{V_i}\times_{F_i}h_{V'_i}$. This is represented by a scheme because the diagonal of the algebraic space $F_i$ is representable [def-trf-algebraic-space]. For every $h_W\to G$, the pullback of $G_i\to G$ is $h_W\times_FF_i$, an open subscheme of $W$, and these opens cover $W$ by Step 3. Thus the $G_i$ are representable open subfunctors covering $G$. Moreover $G$ is a Zariski sheaf: its sections are pairs of scheme maps with equal images in the sheaf $F$, and the sheaf condition follows by componentwise gluing, Step 1 and [lem-pc-zariski-coverings-are-fppf]. Apply [lem-pc-schemes-criterion] to obtain a scheme representing $G$. An arbitrary test of $F\to F\times F$ is exactly such a pair of maps from a scheme, so this proves representability of the diagonal of $F$.

### Arguments retained in the parent

Original step 6: For every test $h_T\to F$, Step 4 represents the base change of $q$ by $C_T=\coprod_iV_i\to T$. Its restriction to each coproduct summand is the open immersion $V_i\hookrightarrow T$, hence etale by [lem-weil-pbc-etale-composition-cancellation](1). The summands are an open covering by [lem-weil-pbc-scheme-coproduct-family]. Apply [lem-weil-pbc-etale-local-on-source] to conclude that $C_T\to T$ is etale. It is surjective by Step 3. Hence $q:H\to F$ is representable, surjective and etale, in the scheme-test sense of [def-trf-algebraic-space].

Original step 7: By the hypothesis that $H$ is an algebraic space and [def-trf-algebraic-space], choose a scheme $U$ and a representable surjective etale map $h_U\to H$. For any $h_T\to F$, the fibre-product equations identify $h_U\times_Fh_T$ with $h_U\times_HE_T$. Step 4 represents $E_T$ by the scheme $C_T$. Therefore $h_U\times_HE_T$ is a scheme, and its projection to $C_T$ is etale and surjective by the scheme-test definition for the atlas $h_U\to H$. The map $C_T\to T$ is etale and surjective by Step 6. Their composite is etale by [lem-weil-pbc-etale-composition-cancellation](2) and surjective by [lem-trf-surjective-morphism-composition]. Thus $h_U\to F$ is a representable surjective etale scheme atlas. Together with the given fppf sheaf condition and Step 5's representable diagonal, this is precisely the definition of an algebraic space [def-trf-algebraic-space].

## Searches and source checks

Before creation I searched the full DAG for Tags 02WR, 02WO, 0F15, coproduct/base-change concepts and open-subfunctor/diagonal concepts, and ran blueprint_refs.py search with 02WR, coproduct, sheaf coproduct, diagonal, representable diagonal, atlas and fibre product, plus ancestor for the item. No blueprint statement duplicates either new result. lem-trf-fppf-sheaf-coproduct-partition gives a clopen partition of a scheme section of H, not the representation of H times_F h_T. lem-pc-schemes-criterion is the scheme representability criterion applied after constructing G_i; it does not construct the cover of the fibre product or establish diagonal locality. lem-trf-algebraic-space-coproduct concerns algebraicity of a disjoint sheaf coproduct, not a relative coproduct map to an arbitrary sheaf.

Every new-node Mathlib query was executed with msearch.py and is recorded exactly in searches.jsonl and the node records. Both results were searched with LeanFinder, Loogle, grep and LeanSearch, with a second semantic phrasing. One initial LeanSearch request was rate-limited, recorded unavailable; the subsequent different phrasing succeeded. I read Mathlib/AlgebraicGeometry/Sites/Representability.lean lines 20-61 and 198-211, Mathlib/AlgebraicGeometry/Limits.lean lines 436-484, and Mathlib/CategoryTheory/MorphismProperty/Representable.lean lines 660-675. The representability theorem applies to an already constructed cover by scheme-representable opens; diag_iff is a generic equivalence requiring proof of representability of all scheme maps. Neither is a one-line proof of the new diagonal statement. coprodPresheafObjIso describes structure-sheaf ring sections, not the functor of points or a sheaf fibre product. Scheme coproduct and extensive-category hits do not identify the relative fppf sheaf pullback in one line.

## Not duplicates

lem-trf-open-sheaf-coproduct-base-change vs lem-a1-space-affine-atlas-open-cover: the existing statement starts with an algebraic space and produces open subspaces with affine atlases; this helper asserts a relative coproduct pullback representation.

lem-trf-open-sheaf-coproduct-base-change vs lem-coef-infinity-parameter-cone-extension: the existing statement concerns quasicategories, inner fibrations and cone extensions; its 02WR reference is from a different context and it has no scheme/sheaf gluing conclusion.

lem-trf-open-sheaf-coproduct-base-change vs lem-coef-infinity-relative-cone-initial-corner: the existing statement concerns quasicategories, inner fibrations and cone extensions; its 02WR reference is from a different context and it has no scheme/sheaf gluing conclusion.

lem-trf-open-sheaf-coproduct-base-change vs lem-coef-infinity-relative-initial-boundary: the existing statement concerns quasicategories, inner fibrations and cone extensions; its 02WR reference is from a different context and it has no scheme/sheaf gluing conclusion.

lem-trf-open-sheaf-coproduct-base-change vs lem-trf-algebraic-space-open-gluing: the existing statement concludes algebraicity of F from algebraic summands and coproduct; this helper isolates the relative coproduct representation without any algebraicity or covering assumption.

lem-trf-open-sheaf-coproduct-base-change vs lem-trf-etale-relation-quotient: the existing statement constructs the quotient of a scheme etale equivalence relation; this helper concerns arbitrary sheaves and contains no equivalence relation or quotient.

lem-trf-open-cover-representable-diagonal vs lem-a1-space-affine-atlas-open-cover: the existing statement starts with an algebraic space and produces open subspaces with affine atlases; this helper asserts representability of a diagonal from locally covering open subsheaves.

lem-trf-open-cover-representable-diagonal vs lem-coef-infinity-parameter-cone-extension: the existing statement concerns quasicategories, inner fibrations and cone extensions; its 02WR reference is from a different context and it has no scheme/sheaf gluing conclusion.

lem-trf-open-cover-representable-diagonal vs lem-coef-infinity-relative-cone-initial-corner: the existing statement concerns quasicategories, inner fibrations and cone extensions; its 02WR reference is from a different context and it has no scheme/sheaf gluing conclusion.

lem-trf-open-cover-representable-diagonal vs lem-coef-infinity-relative-initial-boundary: the existing statement concerns quasicategories, inner fibrations and cone extensions; its 02WR reference is from a different context and it has no scheme/sheaf gluing conclusion.

lem-trf-open-cover-representable-diagonal vs lem-trf-algebraic-space-open-gluing: the existing statement concludes algebraicity of F from algebraic summands and coproduct; this helper isolates open-cover descent of the diagonal without any atlas or coproduct hypothesis.

lem-trf-open-cover-representable-diagonal vs lem-trf-etale-relation-quotient: the existing statement constructs the quotient of a scheme etale equivalence relation; this helper concerns arbitrary sheaves and contains no equivalence relation or quotient.

lem-trf-open-cover-representable-diagonal vs lem-pc-schemes-criterion: the existing criterion assumes a sheaf already has a covering by scheme-representable open subfunctors. The new statement starts with subsheaves F_i having representable diagonals, not necessarily themselves schemes, and constructs the open cover of each fibre-product functor and its scheme representations before that criterion can apply; it also upgrades fppf local membership to covering by the scheme-test opens.

lem-trf-open-cover-representable-diagonal vs lem-weil-pbc-scheme-morphism-gluing: the existing statement glues compatible maps from an open cover of an already given scheme X to an already given scheme Z. The new result establishes existence of a scheme representing a fibre-product sheaf from open subsheaves with representable diagonals. Gluing maps supplies its representables' sheaf condition, not the new representation.

## Review by Q147

I read the complete statement and all three proof paragraphs of spaces.tex Tag 02WR (lemma-glueing-algebraic-spaces), and the statement/proof of schemes.tex Tag 01JJ (lemma-glue-functors). The source explicitly first represents the coproduct pullback, then glues the diagonal, then composes an atlas. This repair keeps that route. I also read descent.tex Tag 023Q and sites.tex Tags 00WI and 00WK for the nontrivial sheaf foundations assigned to the first new job. No SGA source or alternative quotient route is used. The fixed trace-formula chapter and sk-i-curve-zero unit were read; this is still the existing generic algebraic-space tool in the recorded locality/quotient ancestry.

For new node A I checked that every object is introduced, that the V_i exist by representable open inclusions, that its size condition merely puts the coproduct scheme in the chosen big site, and that no covering assumption is needed for the canonical representation. Its full proof task includes the old affine refinement/fpqc sheaf descent, sheafification/local summand discussion, and natural inverse constructed by gluing; those arguments are preserved verbatim above. For new node B I checked that each scheme-test open cover follows from local membership and joint surjectivity, that monicity is supplied by subfunctor inclusions, that G_i is V_i times_{F_i} V'_i (not a product over F without justification), and that only the representable diagonal of F_i is used. The sheaf condition for G is componentwise; Tag 01JJ is applied only after all representable-open and covering hypotheses are proved. Its original arguments are preserved above. Both new files remain statement-only unsplit jobs with empty proof and proof_deps.

For parent step 1 I opened lem-trf-fppf-sheaf-coproduct-partition and lem-pc-zariski-coverings-are-fppf: the first explicitly supplies clopen partitions and component sections, the second makes that partition an fppf cover. Sheaf surjectivity is used only in its local-lifting sense, and covering composition refines these two coverings. I opened def-weil-pbc-sites-and-cohomology and cited its explicit axiom (ii) for that composition. Step 2 cites A for exactly the isomorphism over h_T, and B for the covering and diagonal conclusion; I checked that step 1 provides B's local-cover premise. I read def-trf-algebraic-space, whose statement explicitly includes each summand's representable diagonal. Neither helper depends on the parent, so there is no cycle.

For parent step 3 I opened lem-weil-pbc-etale-composition-cancellation, lem-weil-pbc-scheme-coproduct-family and lem-weil-pbc-etale-local-on-source. Their statements respectively say open immersions are etale, coprojections form a disjoint open cover, and etaleness can be checked on an arbitrary open cover of the source. This matches the C_T projection and imposes no finite/quasi-compact condition. def-trf-algebraic-space defines the scheme-test meaning of representable etale surjective. For step 4 its atlas definition supplies U and representable surjective etale U to H. The fibre-product identification is the explicit reassociation of pairs with equal images in F. The same definition applies to the scheme test C_T of the atlas; composition-cancellation clause (2) and lem-trf-surjective-morphism-composition give exactly the two properties for the composite to T. The conclusion combines this atlas with the diagonal from step 2 and the given fppf sheaf condition. citations.json quotes the exact statement of each citation, including the new nodes.

I checked empty index sets, empty schemes and summands, singleton families, infinite small families, and repeated/overlapping opens. For I empty, the coproduct sheaf has no section on a nonempty scheme by the existing partition statement; local covering in B forces all scheme tests to be empty, so the diagonal tests and atlas projections remain valid. For repeated opens the scheme coproduct retains separate labels; it is not incorrectly identified with their union. Infinite families require no finite-cover assumption, and no disjointness is imposed on the V_i inside T. The arguments impose no reducedness, separatedness or Noetherian hypotheses.

The return's numbered demand is repaired by two independently usable new nodes, unchanged parent statement, complete allocation of every old argument, and a parent proof below 3000 characters. No parent step exceeds 2000 characters. The two new proof jobs have comparable substantial work (2502 and 1650 original characters), with etaleness and atlas assembly retained explicitly in the parent. No hidden argument was removed in exchange for shorter prose.

## Unfinished work

The two new nodes intentionally remain unsplit for other workers, as the human requested. There is no unfinished part of this re-split delivery.

## Validation

The first dry run identified two additional same-tag comparisons through Tag 01JJ in the new diagonal node source. I opened both statements and added the explicit distinctions above. Also made the site covering-composition citation in step 1 explicit; its exact defining axiom is now quoted in citations.json. Required final dry run pending.
