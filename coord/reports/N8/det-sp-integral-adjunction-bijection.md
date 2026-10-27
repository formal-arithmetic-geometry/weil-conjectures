# Repair delivery: det-sp-integral-adjunction-bijection

## Files written

- `dag/nodes/sec-smooth-purity/det-sp-integral-adjunction-bijection.json`: existing statement, repaired split; unchanged statement and statement dependencies. Four assembly steps, 1939 characters in total.
- `dag/nodes/sec-smooth-purity/lem-sp-integral-reconstruction-comparisons.json`: new statement-only, unsplit; no Mathlib match. Isolates the geometric reconstruction datum, natural comparisons, restriction to normalized subcategories, and reconstruction of actual morphisms.
- `dag/nodes/sec-smooth-purity/lem-sp-twisted-pullback-reduction-tower.json`: new statement-only, unsplit; no Mathlib match. Isolates the coherent source comparison for arbitrary twist and shift, including the ramified coefficient levels, and its realization against any supplied tower isomorphism.
- `report.md`, `citations.json`: this review and verbatim quotes for every node cited by each assembly step. Retained `searches.jsonl` and original search-output files; the additional focused comparison searches are in `msearch-source-comparison*.txt`. `old-proof.json` preserves the returned six proof steps; `repair.py` and `write_report.py` are sandbox-only editing helpers.

## Attachments

None for this item. The search for the exact `(blueprint: det-sp-integral-adjunction-bijection)` tag in `lean/WeilConjectures` returned no declaration. Concept searches found `IntegralCoefficients.lean`, `NormalizedTowerRealization.lean`, `BoundedConstructibleUpperShriek.lean` and smooth-purity `Rational.lean`. I read their relevant interfaces: they use small-etale normalized DVR systems, and the rational packaging assumes a supplied compatible finite purity family. None states the entire completed pro-etale tower adjunction, its actual unit/counit reductions and its specified purity map under this item's hypotheses. They cannot justify ATTACH. The existing DAG Mathlib leaf `lem-sp-fully-faithful-adjunction-restriction` is reused, not delivered again.

## WANTED

None. All used source texts are present locally. No SGA source is used.

## Return and retained work

The released repair note of 2026-10-22 requires at least two comparable statement-only new nodes and an assembly proof of at most 3000 characters. The initial sandbox item matched the current shared copy in every JSON field. Its six-step proof, historical citations, statement correction and split-report history were retained as source material. Its report was absent, so the mandated initial dry run exited with the missing `## Review by N8` diagnostic before any mathematical gate. This repair changes the proof structure rather than repushing an unchanged split. The statement, statement dependencies, blueprint fields, import flags and Lean audit are unchanged. The historical passed review remains historical and is not represented as a review of this repair.

## Sources and argument allocation

I read the chapter record `sec-smooth-purity`, the unit `sk-prop-sp-integral-adjunction`, and the current main-20261015 item statement and proof. The unit's route is reduction/reconstruction, the geometric tower adjunction, then realization of tower purity; the repair retains that route. The new nodes' precise source is the item's proof, respectively Normalization/Bijections and Purity. This is an agent-written blueprint proof, so the parent's proof origin remains `agent`.

I also read the current statements of all nine old proof dependencies. For reconstruction I read the blueprint direct-image clause (2), the normalized-equivalence statement, and Bhatt–Scholze Lemma 3.5.7 in the local PDF: it identifies reduction and total derived inverse limit and supplies the adjoint equivalence. The Noetherian qualification is explicit in the current DAG statement; Stacks Tag 01T6, `lemma-finite-type-noetherian` in `morphisms.tex`, was checked at its source. For the new twisted-source comparison I read `def-pur-integral-derived-operations`, `def-coefficient-twists-detailed`, the current statements of `lem-pur-integral-operations-preserve-constructible` and `prop-weil-twist-preserves`, the twist-preserves blueprint source, and Bhatt–Scholze Lemmas 6.5.5 and 6.5.9 in the local PDF. For the categorical assembly I read Mathlib `CategoryTheory/Adjunction/Restrict.lean`, including `restrictFullyFaithful` and the unit, counit and Hom formulas, and compared them with the existing Mathlib leaf.

The old argument is allocated without removing any inference:

1. Old step 1 (786 characters) goes to the reconstruction-comparisons node: finite-type schemes over a field are Noetherian, reduction lands in normalized constructible towers, tower exceptional pullback preserves that subcategory, and the actual reconstruction counit gives the comparison for H, naturally. For the future proof, the field has only two ideals; apply Tag 01T6 to the two structure maps, then `det-sp-reduction-tower-normalized`, `det-sp-tower-gamma` (3) and `det-sp-normalized-equivalence`. This is a proposed proof allocation in the report, not proof steps smuggled into the new node.
2. Old step 2 (748 characters) and the restriction portion of old step 3 go to the same new node. Keep the chosen compactification and direct-image clause (2); b is its actual whole-tower comparison. Naturality is the equality of the two maps induced by the same reduced-complex morphism. The map c is the actual reconstruction counit, so its naturality is the counit's naturality. F_bullet and G_bullet preserve the normalized subcategories by tower-gamma (3); their subcategories are full, so the existing tower Hom bijection restricts with the same unit and counit. The Noetherian constructible reconstruction equivalence supplies full faithfulness.
3. The remaining part of old step 3 (1302 characters) and old step 4 (637 characters) are assigned to the existing independently available Mathlib restriction leaf and explicitly assembled in the parent. Apply it with the normalized full subcategories and b,c, not with unrestricted categories on which preservation was never asserted. The exact three Hom maps and both unit/counit equations are kept. This work is already separated as a node and must not be duplicated by a new geometric lemma that merely applies it.
4. Old step 5 (595 characters) is explicitly present as the reconstruction identity in the new reconstruction-comparisons node. Its future proof is the naturality equation Lr(a)u_A=u_Ba, multiplied by u_B inverse; the parent applies this identity to its two actual maps. No arbitrary levelwise family is lifted. Thus this elementary identity stays with its reconstruction datum rather than being made a spurious third node.
5. Old step 6 (1538 characters) goes to the new twisted-pullback-reduction node, except that applying the existing tower-gamma theorem is assembled in the parent. The future argument retains pullback preservation and reduction, restriction from uniformizer levels to en using (ell^n)=(varpi^(en)), invertibility/local triviality of the integral Tate line, the local tensor comparison N tensor_R R tensor_R B_n = N tensor_R B_n, termwise shift/tensor compatibility including the shifted differential, and compatibility with every quotient transition because both coefficient-factor maps multiply in the same way. These give q as an actual derived-tower map and prove that its source is derived complete and constructible. Finally apply the total derived-limit functor to q and a supplied tower isomorphism and precompose with the actual reconstruction unit. Functoriality carries inverse maps to inverse maps. The new statement is deliberately generalized to arbitrary m,s and a supplied tower map v; it neither assumes nor restates integral smooth purity.

The two new statements have comparable sizes (2637 and 2908 characters) and separate arguments. They have empty proof lists, empty proof-dependency lists and null proof origins; other workers may split them independently. Their statements give assertions, not proof sketches. All six original proof texts are preserved below so the allocation can be checked directly.

## Mathlib and duplicate searches

I read the retained results before reusing them. For reconstruction the two LeanFinder phrasings returned scheme normalization and ordinary sheaf pushforward comparisons, not the derived complete coefficient-tower datum. Loogle returned equivalence/adjunction constructors; the grep query for normalized constructible towers returned no hits; LeanSearch returned ordinary module-sheaf pullback adjunctions. These do not specialize in one line to the geometric reconstruction statement.

For the source comparison the retained LeanFinder phrasings returned perfectoid/Proj and local-cohomology results. The added focused LeanFinder query returned ordinary adic-completion tensor equivalences; focused LeanSearch returned ordinary completion, derived shifts and direct limits. Loogle `CategoryTheory.Functor.mapIso` supplies the elementary final application of a functor to an isomorphism, not the entire-tower completed pullback/Tate source comparison. The original grep returned a pullback-pasting comment; the additional grep returned no hits. Each exact query and its actual result is recorded from `searches.jsonl` in the relevant new node; no unrun search or unavailable service is described as a no-match. The original item searches remain unchanged, since its statement has not changed.

Whole-DAG searches by reconstruction, reduction, twist, source place and the proposed ids, together with `blueprint_refs.py search` for reconstruction, integral adjunction, twist reduction and pullback twist, found no identical blueprint statement. `blueprint_refs.py ancestor` gives this imported item itself; both new nodes have it as `from.node` with empty via and precise proof places. Candidate comparison statements were opened, not judged from titles. The following distinctions also explain why the new nodes are genuine tasks despite nearby general infrastructure.

## Not duplicates

- lem-sp-integral-reconstruction-comparisons vs det-sp-normalized-equivalence: the existing node supplies the single-scheme equivalence; the new node proves the natural geometric b,c comparisons and the domain-correct restriction of the f-tower adjunction under the compactification and finite-type hypotheses.
- lem-sp-integral-reconstruction-comparisons vs det-sp-integral-direct-image-tower: that node gives the direct-image comparison only; it does not assemble the actual exceptional reconstruction counit, restricted tower adjunction and all naturality data used here.
- lem-sp-integral-reconstruction-comparisons vs lem-sp-fully-faithful-adjunction-restriction: the leaf assumes arbitrary fully faithful inclusions, restricted functors and natural b,c; the new task verifies precisely those geometric hypotheses. The new node does not re-prove the abstract Hom-chain theorem.
- lem-sp-integral-reconstruction-comparisons vs lem-pur-normalized-reconstruction-adjunction-calculus: the existing general conjugation result assumes system functors/adjunction on the supplied subcategories; the new node establishes the constructible geometric restrictions and canonical comparison with the separately derived compact-support functor for a chosen compactification. It includes no new general conjugation theorem.
- lem-sp-integral-reconstruction-comparisons vs lem-pur-integral-reconstructed-representing-pair: the existing assertion is representability at one supplied input using a specified Brown comparison (or a single-degree hypothesis), and explicitly assumes no global integral adjoint. The new node constructs functorial smooth-tower reconstruction data without those supplied comparison assumptions.
- lem-sp-twisted-pullback-reduction-tower vs lem-pur-completed-operation-tower-substitution: that node handles finite expressions in completed tensor and pullback on supplied normalized systems; it does not identify the ordinary integral Tate-line twist and shifts with the specified finite twists at the ell-power levels or assert constructible preservation for the displayed source.
- lem-sp-twisted-pullback-reduction-tower vs lem-pur-finite-tensor-presentation-reduction: the existing statement compares two finite uniformizer quotients; the new one starts at a completed integral object, includes whole-tower coherence and realizes the comparison after restricting to ell-power levels.
- lem-sp-twisted-pullback-reduction-tower vs lem-sf-integral-line-tensor-comparison-iso: that statement gives ordinary-to-completed tensor comparison for one supplied rank-one line; it does not identify the whole completed-pullback/twist/shift reduction tower or its finite Tate transitions.
- lem-sp-twisted-pullback-reduction-tower vs lem-pur-integral-ambient-operation-models: the existing statement compares ambient operations followed by completion, without constructibility and without the specified Tate lines or shift source. The new task is their coherent constructible twisted-source comparison, not that ambient comparison.
- lem-sp-twisted-pullback-reduction-tower vs lem-pur-integral-geometric-comparison-realization: the latter needs a finite-field descent/Frobenius datum and explicitly depends on this item. It is downstream and cannot justify this proof. The new node has neither Frobenius hypotheses nor that dependency.

## Review by N8

I checked B–E of delivery-errors against the actual statements and local sources. Both new statements introduce their coefficient ring sheaves, scheme hypotheses, categories and actual total-limit functor, cite the definition/construction nodes used in their notation, and remain statement-only. I preserved the repaired source orientation and did not identify the ordinary constant integral sheaf with the completed ring sheaf.

In assembly step 1 the reconstruction node asserts H's domain, the actual c counit, b's entire-tower meaning, full faithfulness and the adjunction on the correct full normalized subcategories. Those are exactly the hypotheses consumed by step 2. X and Y are finite type over k, so the Noetherian restriction is satisfied; separated finite type also gives qcqs for the old reduction input. The compactification is already fixed in the parent's unchanged hypotheses. The two naturality equations are included in the new node's statement, not borrowed from its unwritten proof.

In step 2 I checked the exact existing restriction-leaf statement: its composite Hom bijection, both triangle identities, and its formulas have the displayed directions. In Mathlib notation comm1=b.symm and comm2=c.symm. In particular the unit uses G_bullet(b inverse) and c inverse, whereas the counit uses b and F_bullet(c). The counit is the inverse image of identity under the Hom bijection. All domains match: the unit starts at M and ends at HFM; the counit starts at FHK and ends at K.

In step 3 the new reconstruction node explicitly states a=u_B inverse L(r(a))u_A. Substitution of step 2's two equalities therefore identifies actual integral morphisms, not merely their evaluations. Tower-gluing clause (3) explicitly says its level comparisons are compatible with units and counits, which is precisely the finite-reduction claim used. The quote in citations.json is that sentence, not a definition of exceptional pullback.

In step 4 the new twisted-source node states an entire derived-tower isomorphism q with actual coefficient transitions and a realization assertion. Tower-gamma clause (2) explicitly states that gamma is an isomorphism natural on the finite-Tor tower category. Step 1 puts r_YK in the normalized constructible subcategory, so it satisfies those finite-Tor/common-bound hypotheses. Substituting m=d, s=2d, C=G_bullet r_Y, v=gamma gives exactly the specified source and target and the required map; no isomorphism was inferred from degreewise cohomology.

I tested the assertions with f the identity and d=0: b,c are the canonical reconstruction data, and the unit/counit equations reduce to the equivalence triangle formulas. K=0 and M=0 give zero towers and the unique maps. The new twisted-source claim also works for m=0 and s=0, leaving only completed pullback reduction; negative m uses the dual invertible line, and arbitrary shifts retain the usual differential sign. For ramified E the equality is of ideals (ell^n)=(varpi^(en)), not of chosen generators; hence it does not assert a false equality ell=varpi^e. Every coefficient level remains n>=1, with quotient transitions n to j for j<=n; no nonexistent level-zero quotient is used. No general inverse-limit/tensor interchange or lifting of arbitrary finite-map families is claimed.

I corrected the absent report and replaced the oversized proof by two independently schedulable tasks plus an explicit assembly. I checked the new statements against duplicate candidates above and kept the already available categorical theorem instead of introducing a duplicate. Every assembly citation has a verbatim quote from the statement actually read. No individual step exceeds 2000 characters, and the entire proof is 1939 characters. The statement remains byte-for-byte equal to the returned/live item. No Lean source, compiler, Lake, shared repository file or launcher script was written or run.

## Source error retained from the returned repair

The blueprint Bijections paragraph calls the counit the image of identity on H(K). With its displayed Hom-bijection direction this is the inverse image; the parent's corrected assembly retains that correction. The historical source free-variable/geometric-domain correction and tower-orientation note are retained in the item's split_report; this delivery makes no additional statement change.

## Unfinished work

The two new nodes are intentionally unsplit, as the return requires. Nothing requested for this one-level repair is omitted. Server dry run and delivery outcomes are recorded after validation.

## Original returned proof (retained verbatim)

### Original step 1

Both $X$ and $Y$ are Noetherian by [lem-weil-pbc-finite-type-over-noetherian], applied to their finite-type maps to $\operatorname{Spec}k$; a field is Noetherian because its only ideals are $0$ and itself. Thus the constructible restriction in [det-sp-normalized-equivalence] applies. *Normalization.* $\operatorname{red}_YK$ is normalized constructible, and $f^!_\bullet$
preserves normalized constructible towers ([det-sp-tower-gamma], (3)). By the
equivalence of [det-sp-normalized-equivalence], $H_{f,\mathcal O_E}(K)=R\varprojlim
f^!_\bullet\operatorname{red}_YK$ lies in $\Dbc(X,\mathcal O_E)$ and
$\operatorname{red}_XH_{f,\mathcal O_E}(K)\simeq f^!_\bullet\operatorname{red}_YK$ (counit isomorphism on
normalized towers). Functoriality of $H$ follows from that of $f^!_\bullet$.

Uses: det-sp-reduction-tower-normalized, det-sp-tower-gamma, det-sp-normalized-equivalence, lem-weil-pbc-finite-type-over-noetherian.

### Original step 2

Put $r_T=\operatorname{red}_T$, $L_T=R\varprojlim$, $F=Rf_{!,\mathcal O_E}$, $F_\bullet=Rf_{!,\bullet}$ and $G_\bullet=f^!_\bullet$. Clause (2) of [det-sp-integral-direct-image-tower], for $M$ and the chosen compactification $f=\bar f\circ j$, gives $FM\simeq L_YF_\bullet r_XM$ in $\Dbc(Y,\mathcal O_E)$ and $b_M:r_YFM\xrightarrow{\sim}F_\bullet r_XM$. These canonical comparisons are natural: for $a:M\to M'$, both $F_\bullet r_X(a)b_M$ and $b_{M'}r_YF(a)$ are the map induced by the same morphism of reduced complexes. Step 1 supplies $c_K:r_XH(K)\xrightarrow{\sim}G_\bullet r_YK$, natural as the counit of the reconstruction adjunction evaluated at $G_\bullet r_YK$. The functors $r_X,r_Y$ are fully faithful by [det-sp-normalized-equivalence].

Uses: det-sp-integral-direct-image-tower, det-sp-normalized-equivalence.

### Original step 3

Apply [lem-sp-fully-faithful-adjunction-restriction] with $\mathcal C=\Dbc(X,\mathcal O_E)$, $\mathcal D=\Dbc(Y,\mathcal O_E)$, $\mathcal C',\mathcal D'$ the full subcategories of normalized constructible towers inside the uniformly bounded constructible finite-Tor tower categories on $X$ and $Y$, $i=r_X$, $j=r_Y$ (which land there and are fully faithful by Step 2), $F'=F_\bullet$, $G'=G_\bullet$, and the natural comparisons $b,c$ of Step 2. Both $F_\bullet$ and $G_\bullet$ preserve normalized constructible towers ([det-sp-tower-gamma], (3)), so they restrict to functors $\mathcal C'\to\mathcal D'$ and $\mathcal D'\to\mathcal C'$. The tower adjunction of [det-sp-tower-gluing] (2) has its Hom bijection for every $M_\bullet$ and $K_\bullet$ in the uniformly bounded categories, in particular for normalized ones; since $\mathcal C',\mathcal D'$ are full, the same natural bijections give $F_\bullet\dashv G_\bullet$ on $\mathcal C',\mathcal D'$, with the same unit and counit. The lemma gives exactly the three displayed Hom bijections and the adjunction $F\dashv H$, including its triangle identities. Explicitly the first comparison sends $a:FM\to K$ to $r_Y(a)b_M^{-1}$, and the last sends $h:r_XM\to G_\bullet r_YK$ to the unique $\widetilde h:M\to H(K)$ with $r_X(\widetilde h)=c_K^{-1}h$.

Uses: lem-sp-fully-faithful-adjunction-restriction, det-sp-tower-gluing, det-sp-tower-gamma.

### Original step 4

Write $\eta^\bullet,\varepsilon^\bullet$ for the tower unit and counit. The unit/counit formulas of [lem-sp-fully-faithful-adjunction-restriction] specialize to
$$r_X(\eta_M)=c_{FM}^{-1}G_\bullet(b_M^{-1})\eta^\bullet_{r_XM},\qquad r_Y(\varepsilon_K)=\varepsilon^\bullet_{r_YK}F_\bullet(c_K)b_{H(K)}.$$
Thus the integral unit and counit reduce to the tower unit and counit under $b,c$. Evaluating these equalities at level $n\geq1$, clause (3) of [det-sp-tower-gluing] identifies their components with the finite units and counits. The counit is the inverse image of $1_{H(K)}$ under the Hom bijection; the unit is the image of $1_{FM}$.

Uses: lem-sp-fully-faithful-adjunction-restriction, det-sp-tower-gluing.

### Original step 5

Let $u_A:A\xrightarrow{\sim}L_Tr_TA$ be the reconstruction unit of [det-sp-normalized-equivalence]. For any morphism $a:A\to B$ in the integral category its naturality equation is $L_Tr_T(a)u_A=u_Ba$, so $a=u_B^{-1}L_T(r_Ta)u_A$. Apply this equation to $a=\eta_M$ for $T=X$ and to $a=\varepsilon_K$ for $T=Y$, substituting their reductions from Step 4. It identifies these maps with the derived limits of the tower unit and counit under the canonical comparisons $b,c,u$. This is equality of actual morphisms, with no passage from an arbitrary family of finite-level maps to a coherent morphism.

Uses: det-sp-normalized-equivalence.

### Original step 6

Let $P=f^*_{\mathcal O_E}K(d)[2d]$. By [lem-pur-integral-operations-preserve-constructible], integral pullback preserves $\Dbc$ and its canonical reductions are $f^*_{\mathcal O_E/\ell^n}(K/\ell^n)$. The powers $(\ell^n)$ are a cofinal subsequence of the uniformizer powers: $(\ell^n)=(\varpi_E^{en})$, where $e$ is the ramification index. The cited reduction formulas therefore apply at these levels. By [prop-weil-twist-preserves], the integral twist is an invertible locally free rank-one sheaf, preserves $\Dbc$, and has the finite twists as reductions. Locally trivializing this line identifies its tensor comparison with $N\otimes^L_{R_X}R_X\otimes^L_{R_X}B_n=N\otimes^L_{R_X}B_n$, where $R_X=\widehat{\mathcal O}_{E,X}$ and $B_n=(\mathcal O_E/\ell^n)_X$; hence this comparison is an isomorphism. Shifts commute with reduction because shifting a complex commutes termwise with tensor and its differential. These canonical comparisons commute with quotient transitions (both composites multiply the coefficient factors), and give $r_XP\simeq f^*_\bullet r_YK(d)[2d]$. In particular $P\in\Dbc(X,\mathcal O_E)$ is derived complete. Clause (2) of [det-sp-tower-gamma] now supplies a tower isomorphism $r_XP\xrightarrow{\sim}G_\bullet r_YK$. Apply the functor $L_X=R\varprojlim$ and precompose with the reconstruction unit $P\xrightarrow{\sim}L_Xr_XP$ of [det-sp-normalized-equivalence]. The composite is the stated $\gamma^H_{f,\mathcal O_E}(K):P\xrightarrow{\sim}H(K)$; a functor carries an isomorphism and its inverse to inverse maps.

Uses: lem-pur-integral-operations-preserve-constructible, prop-weil-twist-preserves, det-sp-tower-gamma, det-sp-normalized-equivalence.
