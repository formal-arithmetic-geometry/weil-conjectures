# Stage-1 repair: lem-sfb-generic-dvr-properness-criterion

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-generic-dvr-properness-criterion.json: unchanged statement; seven assembly steps, 2846 characters total.
- dag/nodes/sec-six-functors-basics/lem-sfb-integral-chow-envelope-compactification.json: new statement-only lemma, status unsplit, no Mathlib match; carries the integral-envelope and reduced-projective-closure arguments of original steps 2 and 3.
- dag/nodes/sec-six-functors-basics/lem-sfb-nongeneric-point-same-field-dvr.json: new statement-only lemma, status unsplit, no Mathlib match; carries the local-domain and same-field trait argument of original step 4.
- citations.json: every step/node citation backed by its exact statement.

The sandbox initially contained only dispatcher brief markers, not a retained split or searches.jsonl. I copied the current repository node and preserved its earlier Mathlib records. I read the merged NR stage-1 report, retained its full text as retained-report-NR.md, and retained the complete original eight proof steps as retained-proof.json. The mathematical arguments extracted below are also reproduced in this delivery report, so they reach the next workers. No repository, launcher, Lean, chapter or unit file was written. No git, compiler, Lake, or build tool was run directly.

## Attachments

None. The exact blueprint tag and generic-DVR notions were searched in lean/WeilConjectures. The item's existing declaration AlgebraicGeometry.isProper_iff_generic_dvr_extensions in lean/Sheaf/AlgebraicGeometry/Morphisms/GenericDvrPropernessCriterion.lean:81 ends in sorry at line 102. ChowModification's statements do not assert the integral-envelope and reduced-closure conclusion. AlgebraicGeometry.exists_trait_of_strict_specializes (WeilConjectures/AlgebraicGeometry/NoetherianSpecializationTrait.lean:32) states only point images. IsLocalRing.exists_isDiscreteValuationRing (WeilConjectures/RingTheory/DiscreteValuationRing/Dominating.lean:250) states an injective local map without the same-field conclusion. Thus none is an attachment for either new node.

## WANTED

None: all sources are available in literature/stacks-project/.

## Return repaired

The single return asks for work to be spread into at least two comparable independent statement-only nodes, with an assembly of at most 3000 characters, preserving the statement and every old argument. The two nodes above are new and unsplit, have no proof or proof dependencies, and have actual logged semantic, Loogle and grep searches. Their deferred arguments are respectively 1650 and 1083 characters in the original proof; neither restates the criterion or its properness conclusion. The first is an existence theorem with no DVR hypothesis; the second applies to arbitrary integral locally Noetherian schemes without any morphism or extension hypothesis. Their statements introduce all objects independently. The original lifting contradiction, closed-immersion step, descent of universal closedness, converse and uniqueness remain in the item. Only routine open-cover/descent wording was tightened, with the same equations and hypotheses. The assembly has no step longer than 2000 characters.

There is no statement dispute, no change of unit route, and no change of the item statement. The original metadata, including the None blueprint ancestor reported by blueprint_refs.py, is preserved. Each new node prepends this item to the exact inherited via list and identifies the source proof paragraph in from.place. This is a descendant of the direct-image/alteration route, not the unit's key node, so realized fields are untouched.

## Deferred arguments, preserved in full

The following text is the mathematical work assigned to the new statement-only nodes, not a proof placed in their statements or proof fields. Other workers can take each node independently.

### lem-sfb-integral-chow-envelope-compactification

By the finite-type-over-Noetherian lemma, $R$ is Noetherian. Chow's lemma gives a proper surjection $q:X\to R$, an $S$-immersion $X\to P=\mathbf P^n_S$, and a dense open $U\subset R$ over which $q$ is an isomorphism. Let $\xi_X$ be the point corresponding to $\xi$ in $q^{-1}U$, and let $Y$ be the reduced induced closed subscheme on $\overline{\{\xi_X\}}\subset X$. This is irreducible and reduced, hence integral. Over $q^{-1}U\cong U$ its restriction is $U$: the closed subset is all of $U$, and the reduced closed structure is uniquely $U$. Consequently its generic field is identified with $L$. The map $\pi:Y\to R$ is proper, being a closed immersion followed by $q$, and its image is closed and contains $U$, so it is surjective. The composite $j:Y\to X\to P$ is an immersion by composition. This removes all possible extra components of the Chow envelope; no assertion that $X$ itself is integral is needed.

Let $Z\subset P$ be the reduced induced closed subscheme on $\overline{j(Y)}$. It is integral, since $Y$ is integral and the closure of its irreducible image is irreducible. The immersion $j$ identifies $Y$ with a dense open subscheme of $Z$: factor $j$ as a closed immersion into an open $O\subset P$. Then $\overline{j(Y)}\cap O=j(Y)$, and both $Y$ and $Z\cap O$ are reduced closed subschemes of $O$ on that subset, so uniqueness of the reduced induced structure identifies them. In particular $Z$ has generic point $j(\xi_Y)$ and function field $L$. Projective space $P\to S$ is proper, and a closed immersion followed by a proper map is proper, so $Z\to S$ is proper. The finite-type-over-Noetherian lemma now makes $Z$ Noetherian.

For the explicit Noetherianity of Y in the new statement, pi is proper, hence finite type, and f is finite type, so Y is finite type over the Noetherian S. The existing finite-type-over-Noetherian lemma supplies the conclusion. The identifications of function fields come from the common nonempty integral open U and from the dense open immersion into Z. These are induced identifications, ensuring equality of the canonical generic morphisms, not merely equality of their point images. The needed inputs are the already-existing Chow lemma, reduced induced structure and uniqueness, permanence, projective-space properness, integral-function-field and finite-type-over-Noetherian nodes; no argument depends on the properness criterion being proved.

### lem-sfb-nongeneric-point-same-field-dvr

Suppose that $j(Y)$ is not closed in $P$, and choose $z\in Z\setminus Y$. Choose a Noetherian affine neighbourhood $W=\operatorname{Spec}C$ of $z$ in $Z$; such neighbourhoods cover $Z$ by local Noetherianity. Since $Z$ is integral, $C$ is a domain with fraction field $L$ by the integral-function-field lemma. If $\mathfrak p$ represents $z$, then $\mathfrak p\ne0$: otherwise $z$ is the generic point, which belongs to $Y$. Thus $B=C_{\mathfrak p}\subset L$ is a local domain with fraction field $L$: fractions of $C$ remain fractions of $B$. A nonzero element of $\mathfrak p$ stays nonzero on localization in the domain $C$, so the maximal ideal of $B$ is nonzero and $B$ is not a field. The ring $B$ is Noetherian by localization. Apply the same-field DVR lemma to obtain $B\subseteq A\subset L$ with $A$ a DVR, $\operatorname{Frac}(A)=L$, and $\mathfrak m_A\cap B=\mathfrak m_B$. The composite $a:\operatorname{Spec}A\to\operatorname{Spec}B\to W\to Z\to P$ sends the closed point to $z$ by that maximal-ideal equality and the generic point to $j(\xi_Y)$ via the identity on $L$.

In the independent statement replace the original boundary condition by z != eta, which is precisely the condition used to ensure the nonzero prime. The final composite stops in Z; embedding into P belongs to the item's assembly. In stalk notation B is O_(Z,z), and the same maximal-ideal contraction states domination. Tag 054F(2) with the identity extension L/L confirms the exact fixed-field conclusion. The already-existing same-field DVR node, not a new duplicate of its algebraic theorem, supplies the main algebraic input.

## Searches

Before creating either node I searched the entire DAG by Stacks tags 0208, 0200, 00PH and 054F and by Chow, integral modification, projective closure, generic DVR, same fraction field, and domination. I opened the candidate statements listed below. I ran blueprint_refs.py ancestor on the item and whole-blueprint searches for Chow, boundary, valuation, integral Chow, Noetherian specialization, fraction field, 0208, 0200, 054F, generic function field and projective closure. No blueprint node states either new result. The relevant general Chow and valuation APIs are reused, not duplicated as new leaves.

For each new node I ran two distinct LeanFinder phrasings, LeanSearch, Loogle, and Mathlib grep through the prescribed Q100/item msearch.py. All ten primary queries and their exact returned records are in searches.jsonl and mathlib_searches. Two supplemental grep queries also appear in the log: exists.*(chow|birational)|compactification|chow in AlgebraicGeometry and exists.*(DVR|DiscreteValuation)|specializ.*valuation|dominat in RingTheory/Valuation. I read their hits as well. Services answered successfully. No search that was not run is recorded.

For the envelope lemma, normalization declarations assert integrality, not a proper birational modification with a projective immersion; Proj properness is only a property of an already given projective spectrum. Birational/Birational.lean defines partial isomorphisms and does not supply a Chow envelope. I read the project ChowLemma source: its documented TODO explicitly reserves the integral classical refinement, and the bundled data does not assert integrality of the modification. For the trait lemma, FunctionField.lean identifies stalk fraction fields but constructs no DVR; ord_add assumes the local ring is a DVR; Dedekind localization requires a Dedekind domain. LocalSubring.exists_le_valuationSubring constructs a valuation ring without discreteness. I read these actual source statements rather than infer matches from names. Thus both new lemmas stay unsplit, with zero Mathlib leaves.

## Not duplicates

lem-sfb-integral-chow-envelope-compactification vs lem-pc-coherent-hi: the existing node states coherence and vanishing of higher direct images; its source mentions Chow only as an input.

lem-sfb-integral-chow-envelope-compactification vs lem-sfb-semilinear-equivariant-chow-modification: the existing node assumes properness over a field and adds a finite group action; it does not apply over an arbitrary affine Noetherian base to a source whose properness is unknown.

lem-sfb-integral-chow-envelope-compactification vs lem-sfb-generic-dvr-properness-criterion: the existing node is the properness criterion being assembled; the new result is an independent construction, with no properness conclusion for R and no DVR extension assumption.

lem-sfb-integral-chow-envelope-compactification vs lem-sfb-noetherian-dvr-properness: the existing node is the full DVR valuative criterion, quantifying over arbitrary squares, not this construction.

lem-sfb-integral-chow-envelope-compactification vs prop-weil-pbc-grothendieck-existence-proper: the existing node is Grothendieck existence for coherent formal modules, not either construction here.

lem-sfb-integral-chow-envelope-compactification vs lem-weil-pbc-chow-noetherian: the existing node provides an arbitrary Chow envelope, with neither integral source of the envelope nor the reduced projective closure and its canonical function-field identifications; original steps 2-3 are the additional argument isolated here.

lem-sfb-integral-chow-envelope-compactification vs lem-weil-pbc-chow-finite-type: the existing node provides a Chow envelope over a qcqs base, without the integral-envelope and common-field reduced compactification assertions.

lem-sfb-nongeneric-point-same-field-dvr vs lem-sbc-smooth-section-component-noetherian-generalization: different hypotheses and conclusion; see the source comparison below.

lem-sfb-nongeneric-point-same-field-dvr vs lem-sbc-noetherian-specialization-trait: the existing node states only the images of two points; it does not prescribe the fraction field or the identity generic-field map.

lem-sfb-nongeneric-point-same-field-dvr vs lem-sfb-local-domain-fg-field-dvr: the existing node constructs a dominating DVR from ring data and a finitely generated field extension; it does not construct a scheme morphism with the specified canonical generic restriction and centre.

lem-sfb-nongeneric-point-same-field-dvr vs lem-sfb-local-domain-same-field-dvr: the existing algebraic node is reused in the deferred proof; it gives the DVR for an already provided Noetherian local nonfield domain, not the affine-chart reduction and the canonical trait morphism on a scheme.

lem-sfb-nongeneric-point-same-field-dvr vs lem-sfb-generic-dvr-properness-criterion: the existing node is the properness criterion being assembled; the new result is an independent construction, with no properness conclusion for R and no DVR extension assumption.

lem-sfb-nongeneric-point-same-field-dvr vs lem-sfb-noetherian-dvr-properness: the existing node is the full DVR valuative criterion, quantifying over arbitrary squares, not this construction.

lem-sfb-nongeneric-point-same-field-dvr vs lem-sfb-dense-generic-trait-selection: different hypotheses and conclusion; see the source comparison below.

lem-sfb-integral-chow-envelope-compactification vs lem-weil-pbc-integral-chow-relatively-ample: the existing result assumes a field base and asserts relative ampleness; it does not supply an arbitrary affine Noetherian base or the reduced proper closure Z. It therefore cannot supply the envelope in this item.

lem-sfb-integral-chow-envelope-compactification vs lem-fin-noetherian-chow-modification: that node assumes the source already proper. Its conclusion cannot be invoked to prove the present properness criterion.

lem-sfb-nongeneric-point-same-field-dvr vs lem-sbc-noetherian-specialization-trait: point images alone do not determine the generic field map, while this item tests only DVR subrings of the original field L with the identity generic map.

lem-sfb-nongeneric-point-same-field-dvr vs lem-sfb-noetherian-image-boundary-dvr: the latter gives a trait with unspecified fraction field and a generic map to some point of U; this lemma fixes L and the canonical generic morphism of integral Z.

## Review by Q100

I read the complete Tag 0208 statement and proof (limits-lemma-Noetherian-dvr-valuative-proper), the Tag 0200 statement and initial proof (coherent-lemma-chow-Noetherian), the entire Tag 00PH lemma-exists-dvr, and the Tag 054F statement and proof (properties-lemma-locally-Noetherian-specialization-dvr). The integral-envelope refinement keeps the reduced closure of the unique generic preimage, so it cannot accidentally select a vertical component. The first new statement has exactly the hypotheses used by original steps 2-3: affine Noetherian base, separated finite type source, integrality, and no assumed properness of f. The second has exactly the hypotheses of original step 4: integral locally Noetherian Z and a nongeneric centre, with no normality, dimension-one, excellence or field-extension assumptions. The source 054F(2) permits the identity finitely generated extension L/L and confirms its stronger field control.

I opened and read every statement used by the seven assembly steps; citations.json reproduces these statements verbatim. Specifically:

1. pqf-def-locnoeth supplies the affine cover by Noetherian rings. The properness definition supplies universal closedness after every base change. lem-pod-separated-finite-type-base-change explicitly preserves both properties. The integral and function-field definitions justify the nonempty open restrictions with field L. Factoring the extension through the inverse-image open is its universal property. The step writes the closed-image/open-cover equality, so locality is elementary from these cited definitions. Empty restrictions require no generic point.
2. lem-sfb-integral-chow-envelope-compactification explicitly provides every object used later: the integral Y, proper surjective pi, immersion j, dense open Y in integral Noetherian proper Z, common field L and a dense open isomorphism over R. None of these conclusions is borrowed from its future proof. The chosen affine base meets all its hypotheses.
3. lem-sfb-nongeneric-point-same-field-dvr explicitly supplies a subring of this same L, its fraction-field identification, the map a_Z, its closed image and canonical generic restriction. A boundary point is nongeneric because the generic point is in the dense open Y. Composing with c gives the map into P required by step 4; this is elementary composition, not factorization through set-theoretic image containment.
4. The three original APIs remain: the DVR definition includes the valuation-ring equivalence; proper valuative existence gives the lift h along pi; separated valuative uniqueness equates the two S-maps to P. Projective-space properness is stated over every S, and properness implies separatedness by the definition. The square has exactly the prescribed canonical map over L because pi is an isomorphism on U. Equality at the closed point contradicts z outside j(Y). No hypothesis is substituted with only equality of underlying point images.
5. The closed-image immersion node states exactly that a closed image upgrades j to a closed immersion. Proper permanence explicitly covers closed immersions and composition; the projective-space node gives proper P over S. Thus the claimed proper Y is obtained by these cited statements.
6. The surjectivity-base-change node covers arbitrary T, and proper permanence covers proper Y_T over T. The inverse image E is closed by continuity; surjectivity proves equality of the two images. This is the elementary topological descent argument written out, with the original separatedness and finite type concluding properness by definition.
7. Proper valuative existence applies because DVRs are valuation rings, while separated valuative uniqueness requires only the original separatedness. Thus uniqueness holds before or after proving the forward implication. The same three cited statements give exactly the converse and final uniqueness clause.

For B1-B7, the two new files contain statements only, with no hidden proof sketches or proof dependencies. All notions in their statements are defined inline or have actual definition dependencies. The sole theorem statement dependency of the envelope node is the reduced-induced structure which it explicitly names and uses to specify its output. TeX is written once, the exact source tags/labels were checked in the local .tex and tag map, and neither file is falsely called a Mathlib leaf. For C1-C5, all non-elementary assembly inputs are cited by their statements; the local-ring reduction and reduced-closure identifications are now the work of separate nodes instead of hidden inline subclaims. For D1-D5, neither new node is a clause of properness or a relabelling of the entire criterion. Their hypotheses and conclusions are independent and strictly smaller; the main lifting/descent argument remains visible in the parent.

Small cases: when R is already proper the closure boundary may be empty, and no trait is needed. For R = Spec k[t,t^-1], the compactification may be P^1 and the point t=0 yields k[t]_(t), which witnesses failure of the extension hypothesis. For Z = Spec of a field there is no nongeneric z, so the trait statement is vacuous rather than incorrectly producing a nontrivial DVR in that field. For Z = Spec k[x,y], a closed origin may have a higher-dimensional nonfield local domain: the lemma constructs a dominating DVR and never claims the local ring itself is a DVR. A singular curve also satisfies the construction without normality. The generic point is expressly excluded: the nonzero-prime argument is precisely where 00PH needs nonfieldness. Empty affine inverse images are handled in step 1. There is no assumption of a Noetherian or quasi-compact original base; only locally Noetherianity is used to reduce to affine opens.

The return required no mathematical correction to the existing proof. I checked all original arguments are retained either in the assembly or verbatim above as independently assigned work; nothing is hidden by a shorter properness API. The report of the earlier mathematical review and the original search records were retained, while the new searches are attributed to Q100. No SGA citation is introduced. The new statement-dependency edges point only to existing definition/structure nodes; neither new lemma depends on the criterion, so no cycle is created. All reused route inputs are already present in the former proof, and the two new nodes inherit its unit. There is no new off-route tool use.

## Unfinished work

The proofs of the two new statement-only nodes are deliberately left to later workers, as required by the return. No requested one-level repair remains unfinished.
