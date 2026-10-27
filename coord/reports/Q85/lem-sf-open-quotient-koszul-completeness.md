## Worker report

Files written:

- `dag/nodes/sec-six-functors/lem-sf-open-quotient-koszul-completeness.json`: repaired split, statement unchanged, five-step assembly (2799 characters).
- `dag/nodes/sec-six-functors/lem-sf-sequence-tensor-augmentation-unit.json`: new statement, status unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-sf-regular-roos-koszul-unit.json`: new statement, status unsplit; no Mathlib match.
- `citations.json`: one verbatim statement quotation for every assembly-step citation.

Attachments: none. The notion/tag search in `lean/WeilConjectures/` found no declaration stating the item. The recorded theorem `WeilConjectures.openQuotientKoszulCompleteness`, `lean/Sheaf/SixFunctors/OpenQuotientKoszulCompleteness.lean:351`, ends with `sorry`; it is not finished evidence. No Lean was written and no compiler, Lake, or build was run.

WANTED: none.

The previous attempt stopped on an apparent conflict between the live reviewed split and the size gate. This return explicitly authorizes the re-split, overriding that obstacle. The retained item was byte-identical to the current live item; all retained statement, citations, source pointers, Lean metadata, arithmetic hypotheses, and logged search results were read before editing. There was no split to attach. The first required dry run reconfirmed the unchanged-node and 7363-character failures. This repair changes the proof, creates two separately assignable tasks, and retains all eight original arguments below. It does not change the statement. Earlier review metadata belongs to the earlier split and is preserved as required, not offered as approval of this repair.

The new arguments have comparable scope: the first identifies an actual unit before evaluation, on a common strict representative; the second passes from existence of a quotient Roos triangle to the actual Koszul unit using a reflector, then proves the converse. Neither is the whole DVR/open theorem or a mere renaming of one of its special-case clauses. The first allows arbitrary ring-sheaf towers and the second arbitrary regular ringed-site coefficients without exact products. Each has an empty proof, empty proof_deps, null proof_origin and status unsplit, so other workers can split them independently.

Nothing remains unfinished in this stage-1 delivery except those intentionally statement-only new tasks. No assumption was added to the parent.

## Review by Q85

I read the compatibility unit, the chapter, and the current `fix-prop-coherence.proof.md` sentence about tensor reassociation, evaluation, and adjunction units/counits. This re-split stays on that coefficient route. I read Stacks `sites-cohomology.tex`, Tag 07A6 (`lemma-adjoint`), which derives the ringed-topos adjunction from its ordinary one, and Tag 0941 (`lemma-derived-limit-is-ok`), which computes total sequence-site limit on K-injective towers and compares it with the Roos limit. These are the sources for the first new task, with the strict tensor normalization supplied by the agent argument below. I read `algebraization.tex`, Tags 099B (`lemma-derived-completion`) and 0A0E (`lemma-derived-completion-koszul`): the first gives the local-complete reflector and the actual unit; the second computes it by the strict Koszul tower. These are the sources for the second new task, combined with the already stated regular-quotient reconstruction lemma. Neither Stacks statement alone is misquoted as the full new lemma.

For the coefficient part I read `sites-modules.tex`, Tag 093M (`lemma-completion-flat`), including its flatness and quotient identifications. For the open part I read `proetale.tex`, Tag 09BP (`lemma-j-shriek-limits`): its hypothesis is a quasi-compact open immersion of schemes, without a finite-type or Noetherian restriction on the schemes. Its proof uses the exact open/closed sequence and closed inverse-image product preservation. The existing completed extension-zero node gives exactly the preservation conclusion the assembly uses. No SGA source is used.

Step 1: I opened the statements of `lem-weil-l-adic-extension-integers-dvr` (clauses 2--4), `lem-weil-valued-dvr-finite-quotients` (clauses 2--3), `def-weil-pbc-noetherian-ring`, `def-pc-perfect-ring-complex`, and `def-weil-pbc-adic-coefficient-datum`. They supply respectively a PID domain, a nonzero uniformizer and finite residue field, finite quotients and canonical surjections, and the two definitions being checked. The repetition argument gives positive additive annihilators; multiplication by every positive power is injective in the domain; the cokernel is the quotient. Rank-one free terms are finite projective. Those are elementary steps, not new nodes.

Step 2: I opened `lem-weil-pbc-completed-constant-sheaf-reduction`. Its finite-quotient clause really identifies the constant and continuous-component sheaves, and its finite-projective-resolution clause gives the displayed two-term resolution over the completed sheaf. Both transitions are postcomposition with the same quotient homomorphism. Hence the inverse-limit identification preserves every projection. Vanishing of H^{-1} of the two-term resolution proves regularity of t on the sheaf; H^0 identifies its quotient with B_n. This is the hypothesis needed by the new regular-site criterion, with no unproved flatness of the finite quotient over the completion.

Step 3: I opened the datum and `lem-coef-derived-system-evaluation-calculus` statements: both use a single flat-term K-flat representative and the same strict tensor tower. `lem-pc-kflat-resolution` explicitly promises flat terms, so this choice meets the new sequence lemma's hypothesis. Its site is the fixed small skeleton, A is the completed ring sheaf, B_n are its constant finite quotient sheaves, and the structural maps are the actual limit projections. The new lemma identifies the whole augmentation with the actual transported adjunction unit. `def-weil-pbc-completed-quotient-completion-unit` defines comp by that same derived constant/limit unit followed by total limit of the augmentation. Thus no equality is inferred merely from finite projections. The normalization result from the old proof is retained in the first task's argument below.

Step 4: I opened `prop-weil-pbc-koszul-reconstruction`: its isomorphism c is specified and its statement says c kappa = comp. Step 1 supplies the Noetherian, finite-perfect quotient datum for that proposition. The new regular-site criterion needs only the regular element proved in Step 2, a small site, and unbounded derived categories; its Koszul transitions are exactly (t,1). Its condition (i) is the existential Roos triangle of `def-weil-derived-complete`, whose statement I read in full, including the warning that a lift to the limit is not uniquely determined. Its other conditions give invertibility of the actual kappa and comp. Together with Step 3 this gives actual u invertible. It does not identify an arbitrary isomorphism from the existential Roos triangle with kappa.

Step 5: I opened `lem-cbc-completed-extension-zero-comparison`, `lem-sf-open-tensor-normalization`, and the calculus statement. The identity square is cartesian, both vertical maps are j, its quasi-compactness is a parent hypothesis, and the coefficient datum was established in Step 1. The first conclusion of the open theorem is preservation of intrinsic completeness. Its ringed slice extension is the extension in the open normalization node with completed coefficient restriction; applying Step 4 to X gives quotient completeness and invertible actual u. The calculus explicitly says the composite of that actual u with the nth total-limit projection is the actual reduction map. This final assertion is a consequence of that equation, not a criterion for equality of maps to a limit.

I checked B1--B10: the new nodes introduce all objects, site sizes, actions, towers, maps and comparison choices; every notion is defined inline or through a statement dependency; the new statements contain assertions only and no proof sketch; TeX has single mathematical backslashes after JSON decoding; sources name the exact Stacks labels and tags. Their blueprint ancestor is `fix-prop-coherence`, with the parent's full via chain and specific argument places, and same_as is empty after the blueprint searches. I searched the whole DAG by tags and concepts, not only this unit, and read the closest matches discussed below. The generic tools used by the assembly remain declared in split_report.tool_uses; I did not manufacture maintainer tool-use approvals.

I ran both new statements through LeanFinder with a second formulation, Loogle, LeanSearch and the prescribed Mathlib grep. All searches completed, and searches.jsonl records their exact query texts and digests. The returned generic `CategoryTheory.Adjunction.derivedη` and `derivedη_fac_app` were read in `Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean`; they give a factorization through abstract derivation comparisons. They do not identify ringed sequence systems, the strict tensor augmentation, or its ordinary/total-limit comparison in one specialization. The other hits concern underived sheaf pullback units, ordinary module completion, derived t-structure representatives, or condensed module constructions. None states either task. The parent's earlier recorded searches are retained, and were not fabricated or needlessly repeated.

Small cases: zero P makes all units identities on zero. For the sequence task, a constant identity algebra tower reduces to the constant/limit unit, and no transition needs to be surjective. For the regular criterion, t a unit makes all quotient and Koszul completions zero, so all four conditions hold exactly when P is zero. A zero regular section can occur only on the zero ring sheaf and causes no exception. For a t-torsion input, derived tensor must still be computed on Q; the proof never replaces it with an underived quotient of P. No exactness of countable sheaf products is imported: the criterion uses total derived limit and products in D throughout, which distinguishes it from the existing exact-product cone criterion. For the parent I checked n=1, the identity open, and the empty open; in the empty case j_!K is zero. No construction relies on a nonempty scheme or constructibility.

The return asks for at least two comparable new tasks and an assembly of at most 3000 characters. The new statements have 2272 and approximately 2400 characters; their inherited argument blocks have 2312 and 1715 characters. The assembly has 2799. Each non-elementary assembly step is under 2000 characters. The original mathematical arguments are retained verbatim below; no hidden standard comparison is replaced by an unexplained word such as transport. The erroneous conflict report from the previous attempt is retained in the final appendix and is resolved by the explicit return authorization.

## Distribution of the returned proof

Old Steps 1--2 remain the arithmetic and coefficient recognition in assembly Steps 1--2. Old Steps 3--4 are the new sequence-tensor-augmentation-unit task, specialized in assembly Step 3. Old Step 5 is the specified c kappa = comp equation in assembly Step 4. Old Steps 6--7 are the new regular-roos-koszul-unit task, specialized in assembly Step 4. Old Step 8 is the identity-square open assembly in Step 5. Thus all eight arguments remain visible; the two substantial comparisons are separately assignable, while elementary arithmetic and specialization are kept in the parent.

For the first new task on general ringed sites, the proposed proof is the old Steps 3--4 below, with the following precise generalization. Use the sequence-projection adjunction and its K-injective pushforward/total-limit comparison. For the tensor system F(Q), the ordinary identity is adjoint to h_Q(x)=(x tensor 1)_n, since its adjunct sends x tensor b to b(x tensor 1). On a K-injective resolution j:F(Q) -> J of semilinear systems, the derived adjunct is represented by the compatible family x -> (j_n(x tensor 1))_n into p_*J. This is also the derived constant/limit unit followed by R lim of the strict tensor augmentation under the specified comparison. Naturality of that comparison and the universal ordinary-to-derived-limit map give the h_Q formula in the new statement. This is the general version of the completed-quotient-unit-normalization input in old Step 4. Derived naturality and localization through quasi-isomorphisms between K-flat representatives give independence of Q. The proof is on entire strict systems, never only on their evaluated Hom classes.

For the second new task, use `lem-pur-derived-complete-koszul-reconstruction` for the levelwise quasi-isomorphism of strict Koszul and quotient towers and its unit-compatible total-limit comparison. From a triangle in (i) it gives some isomorphism P -> C_t(P). The reflector theorem gives local completeness of C_t(P); restriction and derived internal Hom preserve isomorphisms, so P has that local property. The same reflector theorem makes the actual kappa_P invertible. The specified comparison gives comp_P invertible. Conversely, if comp_P is invertible, its finite projections are the actual quotient maps by the strict augmentation and the constant/limit adjunction. Transport the canonical total-limit Roos triangle along comp_P; the product objects and 1-s are unchanged and the first map becomes the prescribed quotient family. This proves (i). The reflector equates (ii) with (iii), and the strict comparison equates (iii) with (iv). This proof uses no exact-product chain cone and no Noetherian ring condition; it is exactly the old Steps 6--7 with their regular-site hypotheses made independent of the DVR instance.

The verbatim old argument follows for the future workers. It is report material, not a proof field of either unsplit node.

### Old step 1

Apply [lem-weil-l-adic-extension-integers-dvr] to the absolute value specified in the coefficient datum: $R$ is a domain and a principal ideal ring, $t\ne0$, and its residue field is finite. Every ideal is generated by one element, so $R$ is Noetherian by [def-weil-pbc-noetherian-ring]. Apply [lem-weil-valued-dvr-finite-quotients] with this valuation ring and uniformizer to obtain finite $A_n$ and the stated quotient maps. The additive group of $R/(t)$ is finite; if its cardinality is $q$, the sequence $0,x,\ldots,qx$ has a repetition for every $x$, so a positive integer kills $x$. Multiplication by $t^n$ is injective since $R$ is a domain and $t\ne0$. Thus $[R\xrightarrow{t^n}R]$ has zero cohomology in degree $-1$ and cokernel $A_n$ in degree $0$. Its terms are rank-one free modules, hence finitely generated projective, so it is the required perfect resolution by [def-pc-perfect-ring-complex]. These verify every ring hypothesis in [def-weil-pbc-adic-coefficient-datum].

### Old step 2

Use [lem-weil-pbc-completed-constant-sheaf-reduction] for $(A,I)=(R,(t))$. Its finite-quotient clause identifies the locally constant sheaf $\underline{A_n}$ with the sheafification of $V\mapsto\operatorname{Cont}(\pi_0(|V|),A_n)$. For $m\ge n$, both descriptions of the quotient transition send a locally constant section $f$ to $q_{m,n}\circ f$; this equality before sheafification proves compatibility for the entire strict tower. The limit identification therefore respects every projection and gives $\widehat R_T=A_T$. Apply the resolution clause of the same lemma to the resolution in Step 1: $[\widehat R_T\xrightarrow{t^n}\widehat R_T]$ represents $B_{n,T}$. Consequently multiplication by $t^n$ on $\widehat R_T$ is injective and the canonical cokernel is $B_{n,T}$. In particular the regular-generator hypothesis needed below holds for $\mathcal O=\widehat R_T$ and $a=t$.

### Old step 3

Choose one flat-term K-flat resolution $Q\to P$ by [lem-pc-kflat-resolution]. By [def-weil-pbc-adic-coefficient-datum], the strict quotient tower $P_\bullet$ is represented by $(Q\otimes_{\widehat R_T}B_{n,T})_n$, with transitions $1\otimes q_{m,n}$ and scalar restriction to $\widehat R_T$. By [lem-coef-derived-system-evaluation-calculus], exactly this same complex of semilinear systems represents $\mathcal R_TP$. Applying $U_T$ forgets only the quotient-ring actions, leaving those differentials and transitions unchanged. Thus the two strict derived towers are canonically identified, before applying evaluation or $R\lim$. Their strict augmentations from $\Delta Q$ are also identical: at every level the map is $x\mapsto x\otimes1$, and $(1\otimes q_{m,n})(x\otimes1)=x\otimes1$.

### Old step 4

Apply [lem-coef-sequence-projection-derived-adjunction] on the fixed small skeleton of $T_{\mathrm{proet}}$, with $A=\widehat R_T$, $B_n=B_{n,T}$ and structural maps the limit projections. Step 3 supplies its flat-term K-flat representative and its sheaf tensor model. The ordinary Hom correspondence sends $h:Q\to\lim_n\operatorname{Res}N_n$ to $(x\otimes b\mapsto b\pi_n h(x))_n$. For $N_n=Q\otimes B_{n,T}$ the identity of the strict system is therefore adjoint to $h(x)=(x\otimes1)_n$: its adjunct sends $x\otimes b$ to $b(x\otimes1)=x\otimes b$. This is the ordinary quotient-limit unit, not merely a family of maps after localization. That lemma specifies the derived correspondence as the derived fraction extension of this ordinary correspondence, and [lem-coef-sequence-pushforward-limit-projections] specifies transport from $Rp_*$ to the actual total $R\lim\,U_T$. Hence the derived unit is localization of this ordinary $h$, followed by the universal ordinary-limit-to-derived-limit comparison. On the same K-flat $Q$, [lem-weil-pbc-completed-quotient-unit-normalization] identifies precisely this composite with the derived constant/limit unit followed by $R\lim$ of the strict quotient augmentation. The latter is $\operatorname{comp}_P$ by [def-weil-pbc-completed-quotient-completion-unit]. Thus $u_P=\operatorname{comp}_P$. This comparison takes place on the whole strict augmentation; it does not infer equality from finite projections. Naturality of both derived constructions transports it from $Q$ to $P$.

### Old step 5

All hypotheses of [prop-weil-pbc-koszul-reconstruction] are now verified by Steps 1-3. Its specified comparison $c_P$ is an isomorphism and satisfies $c_P\kappa_P=\operatorname{comp}_P$. Substituting Step 4 proves $c_P\kappa_P=u_P$. The statement concerns the specified comparison of the Koszul and quotient towers, so no replacement by an arbitrary isomorphism of their limits is made.

### Old step 6

Set $\mathcal O=\widehat R_T$. Step 2 identifies $B_{n,T}=\mathcal O/t^n\mathcal O$ and proves $t$ regular. For the K-flat $Q$ of Step 3, [lem-pur-derived-complete-koszul-reconstruction] therefore applies to exactly these strict reductions. If $P$ is quotient-complete in the Roos-triangle convention of [def-weil-derived-complete], its second assertion gives an isomorphism $P\simeq C_t(P)$, where $C_t(P)=R\lim_n(P\otimes^L[\mathcal O\xrightarrow{t^n}\mathcal O])$. By [lem-weil-pbc-ringed-koszul-completion-reflector], $C_t(P)$ is locally derived $(t)$-complete. This property is invariant under isomorphisms: restriction and derived internal Hom send an isomorphism to an isomorphism. Thus $P$ is locally derived $(t)$-complete. The last equivalence in the reflector theorem makes its actual Koszul unit $\kappa_P$ invertible. We used the existence of $P\simeq C_t(P)$ only to transport completeness; we did not identify that possibly noncanonical isomorphism with $\kappa_P$.

### Old step 7

Conversely, suppose $\kappa_P$ is invertible. Step 5 and invertibility of $c_P$ give invertibility of $\operatorname{comp}_P=u_P$. The canonical total-limit Roos triangle of [lem-weil-pbc-ringed-strict-tower-homotopy-limit] has first map $\iota:R\lim P_\bullet\to\prod_n^D P_n$. By [lem-coef-derived-system-evaluation-calculus], the components of $\iota u_P$ are the actual reductions $P\to\operatorname{Res}_n P_n$. Transporting this distinguished triangle along the isomorphism $u_P$ gives the triangle required by [def-weil-derived-complete]. This proves quotient completeness. Together with Step 6, this gives both directions of the equivalence and also proves that the actual unit is invertible for every quotient-complete object.

### Old step 8

Let $j:U\hookrightarrow X$ be as stated and let $K$ be quotient-complete. Step 6 makes $K$ intrinsically $(t)$-complete. Apply [lem-cbc-completed-extension-zero-comparison] with $(A,I)=(R,(t))$ to the cartesian square having $g=\mathrm{id}_X$, $g_U=\mathrm{id}_U$ and $j'=j$. Its hypotheses require the adic datum and quasi-compactness of $j$, both already available, and its first conclusion says that the ordinary localized ringed extension $j_!K$ is intrinsically complete. This is the same extension functor as in [lem-sf-open-tensor-normalization]: both use exact extension on the slice with coefficient ring $\widehat R_X|_U=\widehat R_U$. Step 7 now gives quotient completeness of $j_!K$ and invertibility of its actual $u_{j_!K}=\operatorname{comp}_{j_!K}$. Finally the unit/projection equation in [lem-coef-derived-system-evaluation-calculus] gives its actual reduction map at every $n$. The cited open theorem assumes quasi-compactness of the immersion but no boundedness, constructibility, finite type of either scheme, or independent inverse-limit commutation hypothesis.

## Not duplicates

lem-sf-sequence-tensor-augmentation-unit vs lem-sbc-derived-restriction-zero-transport: The existing statement transports restricted etale H^0 and a coefficient map; it explicitly contains no derived adjunction unit and no sequence-site total-limit augmentation.

lem-sf-sequence-tensor-augmentation-unit vs lem-sbc-restricted-derived-section-zero-comparison: The existing statement computes H^0 of etale section pullback for a scheme map, without any strict ring sequence or tensor augmentation.

lem-sf-sequence-tensor-augmentation-unit vs lem-sbc-derived-section-pullback-zero: The existing statement compares H^0 of a single etale section pullback with the ordinary section map; the new statement concerns the whole unbounded sequence-site unit.

lem-sf-sequence-tensor-augmentation-unit vs lem-sbc-derived-section-single-unit: The existing statement is a single-degree etale sheaf/Leray unit equation, without a strict ring-sequence tensor functor or its total derived limit.

lem-sf-sequence-tensor-augmentation-unit vs lem-sbc-restricted-derived-section-shift-comparison: The existing statement computes shifted restricted etale cohomology maps; it does not identify a derived sequence unit with a strict augmentation.

lem-sf-sequence-tensor-augmentation-unit vs lem-sbc-restricted-derived-sections-single: The existing statement transports an etale section/Leray transformation on a single sheaf complex, without the strict semilinear coefficient sequence and its total limit.

lem-sf-sequence-tensor-augmentation-unit vs lem-sbc-restricted-derived-evaluation-pullback: The existing statement transports a represented etale cohomology morphism under scheme pullback; it contains no sequence-site augmentation identity.

lem-sf-sequence-tensor-augmentation-unit vs lem-sbc-restricted-derived-sections-shift-transport: The existing statement is shift coherence for restricted derived sections and an arbitrary derived map, without a strict tensor tower or its unit.

lem-sf-sequence-tensor-augmentation-unit vs lem-coef-enriched-sequence-projection-formula: The existing statement computes finite projections of an enriched internal-Hom comparison on normalized inputs; it does not equate the whole sequence adjunction unit with the strict tensor augmentation for arbitrary rings and inputs.

lem-sf-sequence-tensor-augmentation-unit vs lem-coef-scalar-hom-zero-compatibility: The existing statement compares H^0 of an internal scalar-Hom map with the external adjunction for one ring map, without strict systems or total inverse limit.

lem-sf-sequence-tensor-augmentation-unit vs def-coef-compact-support-tensor-comparison: The existing node defines single-ring tensor presentations and a compact-support coefficient map; it asserts no sequence-derived unit normalization theorem.

lem-sf-sequence-tensor-augmentation-unit vs def-sf-ringed-derived-adjoint-lift-data: The existing node defines witnesses and normalization data for a ringed-topos derived adjoint lift; it asserts no existence or equality for sequence tensor augmentation.

lem-sf-regular-roos-koszul-unit vs lem-sf-open-quotient-koszul-completeness: The parent fixes completed finite-extension DVR coefficients and also proves the arithmetic datum and open preservation. The new statement is the regular single-generator criterion on an arbitrary small ringed site, without Noetherian, finite-quotient, or geometric hypotheses; it contains neither the semilinear actual-unit comparison nor the open result.

lem-sf-regular-roos-koszul-unit vs lem-sfb-ringed-complete-triangulated: The existing statement is exactness and shift/triangle closure of the locally complete locus; it does not relate an existential quotient Roos triangle to the canonical augmentation.

lem-sf-regular-roos-koszul-unit vs lem-weil-pbc-ringed-cech-completion-unit-idempotence: The existing statement proves idempotence of the actual Cech units, without regular quotient towers or an existential Roos criterion.

lem-sf-regular-roos-koszul-unit vs lem-weil-pbc-ringed-cech-completion-restriction: The existing statement normalizes Cech completion under slice restriction; it contains no quotient Roos triangle equivalence.

lem-sf-regular-roos-koszul-unit vs lem-weil-pbc-ringed-localization-rhom-calculus: The existing statement proves slice/localization internal-Hom comparison for bounded localization complexes; it contains no quotient tower completeness criterion.

lem-sf-regular-roos-koszul-unit vs lem-weil-pbc-extended-cech-reflector-core: The existing statement supplies the Cech reflector universal property under a local Cech-description hypothesis; it does not compare quotient and Koszul towers or detect an existential Roos triangle.

lem-sf-regular-roos-koszul-unit vs lem-weil-pbc-ringed-koszul-completion-reflector: The existing statement supplies local completeness and universality of Koszul completion for an arbitrary finite list; it contains no quotient Roos triangle or its comparison with the canonical quotient unit. The new criterion needs the separate regular-quotient reconstruction and triangle-transport arguments.

lem-sf-regular-roos-koszul-unit vs lem-weil-pbc-ringed-cech-completion-hom-injective: The existing statement is cancellation by the Cech unit between completed objects; it gives no quotient/Koszul tower comparison or existential Roos criterion.

lem-sf-regular-roos-koszul-unit vs lem-pur-integral-principal-cone-quotient-comparison: The existing statement compares explicit strict product-cone complexes for actual completed local-field coefficients; the new criterion uses total derived products on an arbitrary ringed site and additionally treats an existential Roos triangle.

lem-sf-regular-roos-koszul-unit vs lem-pur-integral-principal-cone-local-criterion: The existing statement is the local-vanishing test for a principal cone model on a scheme pro-etale site; it contains no quotient Roos existence criterion, and its completed-integral coefficient hypothesis cannot be specialized to an arbitrary ringed site.

lem-sf-regular-roos-koszul-unit vs lem-sf-completion-finite-reduction: The existing statement says finite reduction inverts completion units in a complete coefficient datum; it does not assert an equivalence with an existential Roos triangle for arbitrary ringed coefficients.

lem-sf-regular-roos-koszul-unit vs lem-pur-integral-principal-cone-quotient-augmentation: The existing statement supplies compatible quotient chain quasi-isomorphisms for actual completed integral coefficients; it gives no generic existential-Roos/canonical-unit criterion.

lem-sf-sequence-tensor-augmentation-unit vs lem-coef-sequence-projection-derived-adjunction: This supplies the derived sequence adjunction, its ordinary Hom formula and K-flat computation, but no equality with the derived constant/limit strict augmentation. The new node proves this additional whole-map normalization.

lem-sf-sequence-tensor-augmentation-unit vs lem-coef-sequence-pushforward-limit-projections: This supplies Rp_* = total restricted limit and projection/counit equations. It does not identify the whole unit with the strict augmentation, which is stronger than matching projections.

lem-sf-sequence-tensor-augmentation-unit vs lem-coef-derived-system-evaluation-calculus: This is specialized to completed finite-extension DVR coefficients and states the actual unit projection identities, without the whole strict-augmentation equality.

lem-sf-sequence-tensor-augmentation-unit vs lem-weil-pbc-completed-quotient-unit-normalization: This concerns the completed coefficient datum and the ordinary/derived constant-tower unit comparison, without identifying the separate semilinear sequence-adjunction unit; the new generic ringed sequence statement identifies that unit as well.

lem-sf-sequence-tensor-augmentation-unit vs lem-pur-strict-quotient-diagonal-normalization: This treats Noetherian constant coefficient quotient towers and their completion reflector, without the arbitrary ring-sheaf sequence adjunction or its actual transported unit.

lem-sf-sequence-tensor-augmentation-unit vs lem-pe-kflat-scalar-tower-realization: This normalizes finite reduction units and quotient transitions on one K-flat representative, without the total derived sequence-adjunction unit.

lem-sf-regular-roos-koszul-unit vs lem-pur-regular-quotient-completion-unit: This assumes exact countable products of module sheaves and uses a literal product-cone model. The new statement has no exact-product hypothesis and uses total derived limit and products in D, so it cannot be obtained by specializing this node.

lem-sf-regular-roos-koszul-unit vs lem-pur-roos-intrinsic-completeness-equivalence: This fixes completed finite-extension DVR coefficient sheaves on scheme pro-etale sites with an adic datum. The new node permits any ringed small site and regular global section, including non-Noetherian, nonfinite coefficient rings and nonexact products.

lem-sf-regular-roos-koszul-unit vs lem-pur-derived-complete-koszul-reconstruction: This gives a unit-compatible strict tower comparison and existence of some P = C_t(P) when a Roos triangle exists, but does not infer invertibility of the canonical unit or prove the converse. The reflector argument is the additional work.

lem-sf-regular-roos-koszul-unit vs lem-sf-open-roos-unit-adjunction: This assumes finite-type schemes over an algebraic closure of a finite field, includes open restriction/extension, and fixes completed DVR coefficients; the new ringed-site criterion has none of those hypotheses or geometric conclusions.

lem-sf-regular-roos-koszul-unit vs lem-weil-completed-integral-principal-unit-criterion: This uses actual completed integral coefficient sheaves on a scheme pro-etale site and a specified quotient completion Model; it does not cover arbitrary ringed-site coefficients.

lem-sf-regular-roos-koszul-unit vs def-pur-principal-cone-tower: The existing node defines a literal chain product-cone tower for an endomorphism, with no derived comparison or completeness theorem. The new statement is a canonical-unit criterion using total derived limit for arbitrary regular ringed-site coefficients.

lem-sf-regular-roos-koszul-unit vs lem-fix-scalar-completion-associator: The existing statement proves associativity and unit coherence of scalar extension along a tower of finite local fields. It has no generic regular ringed-site Roos-triangle criterion.

lem-sf-sequence-tensor-augmentation-unit vs def-pd-section-derived-realization: The existing definition specifies section-equivalence realization and independently derived ringed operations for condensed coefficients; it asserts no sequence tensor augmentation equality.

lem-sf-sequence-tensor-augmentation-unit vs def-pd-section-derived-tensor-data: The existing definition constructs section-equivalence conjugate derived tensors and pullback/pushforward for condensed coefficients. It does not assert the sequence-derived unit equals a strict augmentation.

lem-sf-sequence-tensor-augmentation-unit vs lem-pd-module-ringed-topos-derived-comparison: The existing theorem compares internal condensed module operations with section-ring operations for scheme morphisms. It does not identify the whole sequence-site unit or its ordinary-limit augmentation.

lem-sf-sequence-tensor-augmentation-unit vs lem-pd-section-derived-pushpull-normalization: The existing theorem transports derived push-pull through a fixed section equivalence for condensed coefficients and scheme maps; the new node treats arbitrary ring-sheaf sequences and their strict augmentation.

lem-sf-sequence-tensor-augmentation-unit vs def-pbc-successive-derived-scalar-normalization-data: The existing node defines data and equations for successive scalar-extension adjunctions without claiming existence. It gives no total sequence-limit unit theorem.

lem-sf-sequence-tensor-augmentation-unit vs def-weil-pbc-derived-direct-image-composition: The existing node defines composition of bounded-below etale abelian direct images by adjunction conjugates, without strict ring sequences or tensor quotient augmentation.

lem-sf-sequence-tensor-augmentation-unit vs def-weil-pbc-derived-normalization-arrows: The existing node defines constant-sheaf scalar normalization arrows and coefficient inverse-image mates, without total inverse limits of strict tensor systems.

lem-sf-sequence-tensor-augmentation-unit vs def-weil-pbc-ringed-slice-derived-data: The existing node packages derived ringed functors and their slice-comparison normalization as data; it does not prove the sequence unit is the strict tensor augmentation.

lem-sf-sequence-tensor-augmentation-unit vs def-weil-pbc-successive-derived-quotient-data: The existing node defines presentations and normalized successive-extension data, leaving existence separate. It asserts no strict-system augmentation/total-limit identity.

lem-sf-sequence-tensor-augmentation-unit vs lem-pbc-normalized-derived-adjunction-transport: The existing statement transports a normalized adjunction through additive equivalences with exact right adjoints. The sequence direct image is a limit and need not be exact, and this theorem does not identify its unit with the strict tensor augmentation.

lem-sf-sequence-tensor-augmentation-unit vs lem-weil-pbc-cohomology-pullback-derived-unit: The existing theorem identifies bounded-below etale cohomology pullback with global sections of a scheme-map unit followed by Leray. It has no semilinear sequence tensor system or whole augmentation identity.

lem-sf-sequence-tensor-augmentation-unit vs lem-weil-pbc-derived-adjunction-shift: The existing statement proves shift compatibility of a ringed-topos derived adjunction, without comparing its unit to any strict tensor/limit augmentation.

## Earlier blocked attempt (retained)

## Worker report

The sandbox contains an unchanged reading copy of dag/nodes/sec-six-functors/lem-sf-open-quotient-koszul-completeness.json. No new nodes, no Mathlib leaves, and no stage-1 changes are proposed.

Attachments: none. The existing Sheaf theorem WeilConjectures.openQuotientKoszulCompleteness at lean/Sheaf/SixFunctors/OpenQuotientKoszulCompleteness.lean:351 has a sorry proof, so it is not an attachment.

WANTED: none.

The assignment is superseded by the live repository: status is split and reviewed.result is pass, dated 2026-10-21, group NN, reviewer NT-cc-NN-60c49ba51. A reviewed_lean pass is also already present. The standing brief says live split-and-reviewed nodes win and must never be split again. There is no return entry authorizing repair of this reviewed split in the task prompt.

I did not alter the item, create a replacement split, or claim that its Lean proof is complete. The required dry run tests whether this unchanged assignment can be delivered; no push is appropriate for a report-only duplicate.

## Review by Q85

I read the item's eight-step split and its existing independent mathematical review, checked the live split/review metadata, and compared the recorded Lean declaration with the source, whose proof is sorry. The existing review covers the arithmetic datum, strict augmentation and derived unit, Koszul comparison, Roos equivalence, and quasi-compact open extension. This report does not claim a fresh mathematical review of those sources: the live reviewed split takes precedence before new stage-1 work. The item and its logged Mathlib searches are retained verbatim. citations.json quotes each cited statement verbatim as context for the unchanged copy. No new statement, hypothesis change, or unrun search is recorded.

## Delivery gate outcome

The required dry run exited 1. Server preflight refused the delivery for two reasons: (1) "the item's node file is unchanged"; (2) "re-split (the human, 2026-10-21): the item's proof in words is still 7363 characters; split further until it is at most 3000 characters (each non-elementary argument a new statement-only node the step cites)". Nothing was pushed.

This gate requires re-splitting a live split-and-reviewed node, whereas the explicit worker brief says "Live finished/mathlib/merged/split-and-reviewed nodes win; never split one." No return entry overriding that instruction was supplied. I report this assignment/gate conflict as BLOCKED and retain the unchanged node for inspection, rather than invent a change or bypass the delivery gate.
