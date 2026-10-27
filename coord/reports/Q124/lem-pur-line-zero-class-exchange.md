# Repair report: lem-pur-line-zero-class-exchange

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-line-zero-class-exchange.json: existing statement, split; statement retained verbatim, proof now three assembly steps.
- dag/nodes/sec-smooth-purity/lem-pur-section-compact-source-exchange.json: statement, unsplit; no Mathlib match. A generic closed-section normalization and exchange theorem, independent of Cartier/Kummer classes.
- dag/nodes/sec-smooth-purity/lem-pur-line-kummer-field-realization.json: statement, unsplit; no Mathlib match. Ordinary etale representatives, Cartier-preserving pullbacks, finite Tor input and normalized compact realization over any field, without the compact-exchange conclusion.
- citations.json: exact statement quotations for every citation in the item's three proof steps.
- searches.jsonl: real search-command results. LeanSearch was rate limited and is recorded as unavailable, not as a negative result. Loogle, LeanFinder (two phrasings for each new statement), and local grep succeeded; returned signatures were read.

## Attachments

None. Searched lean/WeilConjectures for the blueprint id and zero-section, compact-class, exchange and Kummer terminology. The only zero-section class hits are frame-independence arguments, not this supported-class exchange with both its normalization and ordinary etale fibre realization. No finished exact declaration was found. The item's live lean_audit is none.

## WANTED

None. The blueprint sources and Stacks sources used here are present locally.

## What was wrong and what changed

The return is the human's work-spreading instruction, not a mathematical objection: the seven-step proof has 7726 characters and needs independently assignable work. The sandbox was empty on arrival; the live node agrees with the return's seven step lengths. I copied that node, retained its statement, searches, existing metadata and source references, and first ran deliver.py --no-push; it stopped because the report was missing. There was no earlier sandbox proof or search log to discard. The return head is recorded in coord/returns/Q124.md as e2a95534abdca96856ae1c3b80c5b78fb624dc06; its requested seven-step split is the baseline saved in returned-node.json and copied in full below. No repository git commands were run.

The two new statements contain separate reusable mathematical conclusions. Neither repeats the whole item: the section lemma applies to any closed section and has no Kummer class or fibre claim; the realization lemma has no compact-support exchange equation and covers any field. Their statement lengths are comparable (about 2500 and 3400 characters). Each is delivered with empty proof, empty proof_deps, null proof_origin and status unsplit. Other workers are to prove them. The complete former arguments are preserved below, rather than compressed or discarded. The item itself is a 1994-character assembly, below the 3000-character limit.

Old steps 3--4 (proper/open computation, mate-pasting identity, counit-normalized site comparison, arbitrary-base-change source normalization) belong to lem-pur-section-compact-source-exchange. Its source-comparison clause also carries the final source normalization of old step 7. Old steps 1--2 (Cartier pullback, annihilating exponent, ordinary etale witness, exactness of the supported direct image), the finite-Tor and twist input of step 6, and the roots-projection/compact-realization argument of step 7 belong to lem-pur-line-kummer-field-realization. The fibre-basis compatibility in old step 6 is explicitly in its statement. The elementary substitution of old step 5 is retained as assembly step 2. The application of compact-fibre comparison in old step 6 and the specialization of old step 7 over Omega form assembly step 3. Thus every old argument has a destination; none is replaced by a vague transport assertion.

The field generality is necessary: the existing fixed-k realization statement cannot be applied literally over an arbitrary geometric fibre field Omega. We therefore state the extracted result for any field K_0 with ell invertible, and its argument uses the finite-type hypothesis over that field, not over the original k. No target, item statement, unit or chapter route was changed. No SGA source or trace/purity shortcut was used.

## Not duplicates

lem-pur-section-compact-source-exchange vs lem-cbc-proper-open-interchange-coherence: the existing lemma states an interchange square and its exchange equation, not the closed-section compact-source identification and identity after composition with h and transport between sites.
lem-pur-section-compact-source-exchange vs lem-sp-finite-compact-site-coherence: the existing lemma states refinement/composition comparison equations on Noetherian schemes; it does not give the source equation for arbitrary B' after a section support, or specify that normalization on a pulled-back model.
lem-pur-section-compact-source-exchange vs thm-sf-comp-composition: composition exists and is normalized, but its statement does not assert base-change compatibility or identity source exchange.
lem-pur-section-compact-source-exchange vs lem-pur-supported-constant-exchange-normalization: the existing lemma normalizes inverse image of a supported constant sheaf, not compact direct image and its exchange under the section retraction.
lem-pur-line-kummer-field-realization vs lem-pur-line-zero-class-etale-realization: the existing statement fixes k as the algebraic closure of a finite field, includes comparison with the relative divisor class and a local sign; it does not permit reapplication over any geometric fibre field Omega. The new lemma introduces its arbitrary field, and extracts only the witness, pullback, Tor and compact-realization arguments needed here.
lem-pur-line-kummer-field-realization vs lem-amb-cartier-kummer-map: this supplies the supported morphism and its witness, not its normalized compact image, finite Tor amplitude, or zero-section Cartier geometry.
lem-pur-line-kummer-field-realization vs lem-sf-class-compact-support-comparison: the existing theorem gives natural comparison of compact targets for a supplied witness; it does not supply the Kummer witness, identify its roots-projection twist, or identify the source under the zero-section normalization.
lem-pur-line-kummer-field-realization vs lem-pur-origin-class-projective-comparison: that lemma identifies the image of the origin class in the projective-line cohomology with a Chern class, on the ordinary etale site; our lemma compares the actual compact morphism across sites and does not compute its projective image.

Whole-DAG and blueprint searches were made before creation: blueprint_refs ancestor for the item, blueprint_refs search for source exchange, supported compact, section, Kummer, Kummer realization, supported section, origin class, zero-section and compact source; rg over all dag/nodes for the section/exchange and Kummer/realization concepts and Stacks tags 0F7B, 0F7F, 0D6E, 0E46, 0E47. Candidate statements above were opened, not judged by names. None states either new result. Both new source fields cite the blueprint extraction place rather than claiming an exact Stacks theorem; the report gives the Stacks tags underlying the retained arguments.

## Review by Q124

I read the unit sk-prop-an and chapter sec-smooth-purity, then the current main-20261015 thm-pur-rank-one-thom.proof.md Step 3 and Step 2 first paragraph. They prescribe class pullback and compact-fibre identification, without a supported-to-compact isomorphism. I also read main-20261015 lem-amb-cartier-kummer-map.proof.md in sec-six-functors-basics/sk-lem-geo-cartier (relative line bundle with complement trivialization, Kummer boundary, supported Hom, scalar extension) and lem-sf-class-compact-support-comparison.proof.md in sk-prop-sf-existence (open comparison then proper comparison, natural in witness). For the source lemma I read Stacks more-etale.tex Tag 0F7B, lemma-shriek-proper-and-open, and Tag 0F7F, lemma-shriek-proper-and-open-base-change; and sites-cohomology.tex Tag 0D6E, lemma-derived-pushforward-composition, Tags 0E46/0E47, remark-compose-base-change and remark-compose-base-change-horizontal. These are the same normalization and pasting arguments as the retained proof, not another purity route.

Assembly step 1 cites only the new field-realization statement. I checked that it explicitly supplies every input used: M's ordinary supported witness, K's L_E witness and specified twist, Cartier pullback for all B', equality of actual supported maps, exact supported direct images, and bounded constructibility plus finite Tor amplitude. This covers old steps 1--2 and the input check of old step 6. The node introduces K_0, ell, F, A, B, E, z, N, both sites and both compact-support functors, so its meaning does not depend on the parent statement. Its vector-bundle definition is the Noetherian arbitrary-base definition: B is finite type over a field, hence Noetherian, so it applies. For an arbitrary B' the statement concerns the pulled-back local R'[t] model, not a fresh invocation of that Noetherian definition.

Assembly step 2 cites the new section statement and the two existing compact-base-change theorems. I opened all three statements. The section lemma states the exact source equation with beta and a,a' used here; it also identifies etale and pro-etale normalized source comparisons. It is a lemma about arbitrary closed sections, independently of a Kummer map. The statement thm-cbc-finite-torsion explicitly says natural in K: this is essential, since thm-cbc-finite-level-proetale alone only specifies transport and witness independence. The latter statement identifies the pro-etale exchange with transport of the etale exchange through proper/open and pullback comparisons; naturality in the witnessed map follows from that construction. The equation then follows by substituting v^{-1}c=c'beta and composing with g^{-1}a. I checked the domains and order of every composite. No non-Noetherian application of site coherence is hidden: original diagrams are Noetherian over K_0; the primed source normalization is the one transported along the specified pulled-back compactification, as the parent requires.

Assembly step 3 cites lem-pur-cfiber-stalk and the new field-realization statement. I read the former: it requires D^b_ctf and gives the canonical compact-fibre comparison. Step 1 supplies D^b_ctf, and the zero-section line bundle is separated finite type. Step 2 applied to g=bar b identifies the actual stalk map; the new realization lemma explicitly includes isomorphisms of Cartier pairs, so a chosen fibre basis sends the supported map to c_0. The same lemma over K_0=Omega identifies the compact image with the ordinary etale tau_X^e, including source and twist, and no claim that Spec Omega is finite type over k is made. Both are finite type over Omega itself. No stalk group is substituted for a derived-object comparison; the final equation concerns the morphism in the derived category.

I separately opened all 23 dependency statements in the retained proof, including the actual proper/open square equation, both direct-image composition and mate-pasting identities, the counit normalization for site comparison, open comparison, Noetherian hypothesis of finite compact-site coherence, finite direct-image exactness, pro-etale closed exactness, the roots-projection comparison, finite etale twist-line flatness, and finite-Tor definition. The proof plans for the new nodes below allocate these dependencies to the extracted arguments; they are not proof_deps of the still-unsplit nodes. Generic scheme exactness and coherence tools remain material for the workers who split those new nodes.

Small cases checked: empty B makes all displayed maps the unique zero-object maps. Identity g gives the normalized identity, not an unspecified rank-one automorphism. Over R'=k[epsilon]/(epsilon^2), t remains a nonzerodivisor, so nonflatness does not invalidate the Cartier input. Over a non-quasi-compact B' the pulled-back compactification is used and only local polynomial charts establish the section properties. For n=1 and ramification e>1, ell=unit*varpi^e still implies ell^n A=0; no coefficient-flatness over Z/ell^n is assumed. Flatness needed to replace the derived tensor L_T by an ordinary one is flatness of the roots sheaf, as stated in lem-asd-finite-etale-twist-line. Locally free rank one makes A(1)[2] have Tor amplitude [-2,-2], including on the empty scheme where only containment is asserted. Finally Omega need not be algebraic or finite type over k; reapplying the arbitrary-field lemma handles it.

I checked delivery-errors B--E: new statements are self-contained with definition dependencies and single TeX escapes; no proof sketch is in either statement, and no proof steps are assigned to unsplit nodes. Searches are genuine and unavailable service results are distinguished. The new lemmas are separate arguments of comparable size, not clauses obtained by relabelling the item, and all long original arguments are preserved below. Every current assembly citation has a literal quotation in citations.json. No step exceeds 2000 characters, so there is no unexamined long inline sublemma. Parent statement text is byte-for-byte equal to the baseline. The two new blueprint fields use nearest ancestor thm-pur-rank-one-thom and via [lem-pur-line-zero-class-exchange], with exact source places and no unsupported same_as entry.

## Unfinished work

The two new nodes are deliberately statement-only and unsplit, as requested by the return. Their proofs have not been certified by this delivery. Nothing in Lean was written or compiled.

## Preserved argument and allocation to new work items

The following are the seven full proof steps of the returned/live node, verbatim. They are worker handoff material for proving the two new statements, not proof steps attached to the new unsplit nodes.

### Former step 1

Allocated to: lem-pur-line-kummer-field-realization (Cartier pullback geometry).

Check the pulled-back pair. On a trivializing affine $U=\operatorname{Spec}R$ the bundle and section are $\operatorname{Spec}R[t]$ and $V(t)$. After any affine base change $\operatorname{Spec}R'\to U$ these are $\operatorname{Spec}R'[t]$ and $V(t)$. Multiplication by $t$ is injective, since the coefficient of $t^{i+1}$ in $t\sum a_it^i$ is $a_i$. Thus $D'=z'(B')$ is Cartier even for nonflat $g$. This argument is local on both bases and so covers arbitrary $B'$. The augmentation $t\mapsto0$ and projection still compose to the identity. These are the zero-section data of [def-pur-vector-bundle-zero-section].

Cited statements: def-pur-vector-bundle-zero-section.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/thm-pur-rank-one-thom.proof.md; Step 3, checking the Cartier hypothesis for arbitrary pullback.

### Former step 2

Allocated to: lem-pur-line-kummer-field-realization (annihilator, witnesses, supported exactness and pullback).

Put $K=A_E(1)[2]$ and $M=z_*A_B$. Since $\ell$ is a unit times $\varpi_F^e$ with $e\geq1$, $\ell^nA=0$. Apply [lem-amb-cartier-kummer-map] with annihilating exponent $r=n$. It supplies an ordinary etale supported morphism $c^e: Rz_*A_B\to L_E[2]$ whose pro-etale realization is $c=c_{D,A}$, where $L_E=\mu^{\mathrm{et}}_{\ell^n,E}\otimes^L_{\mathbf Z/\ell^n}A$. The same statement identifies the pullback of $c$ with $c'=c_{D',A}$ using the supported-constant and prescribed-twist comparisons; Step 1 checks its only extra geometric hypothesis. On the etale side [lem-asd-ordinary-supported-kummer] supplies the same supported morphism and its pullback identity. Finite direct image is exact by [lemma-weil-pbc-finite-direct-image-exact]; the module version follows because forgetting scalar action commutes with underived direct image and detects exact sequences. Thus $Rz_*=z_*$ here. On the pro-etale side [lem-exc-proetale-closed-exact] gives this equality: the zero-section complement is quasi-compact locally, since it is $D(t)\subset\operatorname{Spec}R[t]$. The primed assertions follow by the same local calculation.

Cited statements: lem-amb-cartier-kummer-map, lem-asd-ordinary-supported-kummer, lemma-weil-pbc-finite-direct-image-exact, lem-exc-proetale-closed-exact.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/thm-pur-rank-one-thom.proof.md; Step 3, supported Kummer pullback; Cartier source construction detailed in lem-amb-cartier-kummer-map.proof.md.

### Former step 3

Allocated to: lem-pur-section-compact-source-exchange (compactified section and source comparison).

Compute the source comparison on a compactification $E\xrightarrow j\bar E\xrightarrow pB$. Let $s=jz$; since $ps=1_B$ and $p$ is separated, [lem-weil-pbc-section-separated-closed-immersion] makes $s$ closed. Both $z$ and $s$ are proper by [lem-weil-pbc-closed-immersion-proper]. Apply [lem-cbc-proper-open-interchange-coherence] to the square with top open $1_B$, bottom open $j$, left proper map $z$ and right proper map $s$. It gives $j_!Rz_*\cong Rs_*$. Therefore, using the normalized direct-image comparison of [lem-cbc-etale-derived-direct-image-coherence],
$$R\pi_!^eRz_*A_B=Rp_*j_!Rz_*A_B\cong Rp_*Rs_*A_B\cong R(ps)_*A_B\cong A_B.$$
All maps used are the normalized proper/open and direct-image maps, so this is the compactification construction of the source comparison in [thm-sf-comp-composition], with $\pi z=1$. The primed comparison is computed by the pulled-back diagram. Its construction uses only the given proper/open model; it makes sense for arbitrary $B'$ and invokes no finite-type-over-$k$ theorem on $B'$.

Cited statements: lem-weil-pbc-section-separated-closed-immersion, lem-weil-pbc-closed-immersion-proper, lem-cbc-proper-open-interchange-coherence, lem-cbc-etale-derived-direct-image-coherence, thm-sf-comp-composition.

Source: literature/stacks-project/more-etale.tex; Tag 0F7B, lemma-shriek-proper-and-open; sites-cohomology.tex Tag 0D6E, lemma-derived-pushforward-composition; blueprint Step 3.

### Former step 4

Allocated to: lem-pur-section-compact-source-exchange (identity exchange, mate and site normalization).

The source exchange is the identity, not just an automorphism of a rank-one object. Work first on the ordinary etale models. The last displayed base-change equation of [lem-cbc-proper-open-interchange-coherence], for the square in Step 3, identifies exchange on $Rp_*j_!Rz_*A_B$ with the successive proper exchanges for $p$ and $s$ on $A_B$. The exchange is the specified unit--square--counit map of [def-cbc-exchange-map]. Part (2) of [lem-weil-pbc-mate-pasting] identifies these successive exchanges, under the direct-image compositors of [lem-cbc-etale-derived-direct-image-coherence], with exchange for $ps=1_B$. Part (4) says this mate is the identity. Thus under the comparisons of Step 3 the source exchange is $1_{A_{B'}}$. For the pro-etale functors use [thm-cbc-finite-level-proetale]: its exchange is exactly this etale exchange transported through the proper/open and pullback comparisons. On the original diagram these comparisons identify the source normalization by [lem-sp-finite-compact-site-coherence], including its identity and composition equations: the proper comparison is the counit-normalized mate of [lem-weil-pbc-comparison-direct-image-canonical-mate], the open comparison is [lem-cbc-proetale-extension-zero-comparison], and part (2) of the mate-pasting lemma identifies their proper composite for $ps$ with the identity comparison. All original schemes are Noetherian by [lem-weil-pbc-finite-type-over-noetherian] (a field has only two ideals). On arbitrary $B'$, use the transported source comparison of the pulled-back proper/open model stipulated in the statement, not a new application of the Noetherian coherence theorem. The transported identity is therefore $1_{A_{B'}}$.

Cited statements: lem-cbc-proper-open-interchange-coherence, def-cbc-exchange-map, lem-weil-pbc-mate-pasting, lem-cbc-etale-derived-direct-image-coherence, thm-cbc-finite-level-proetale, lem-weil-pbc-comparison-direct-image-canonical-mate, lem-cbc-proetale-extension-zero-comparison, lem-sp-finite-compact-site-coherence, lem-weil-pbc-finite-type-over-noetherian.

Source: literature/stacks-project/more-etale.tex; Tag 0F7F, lemma-shriek-proper-and-open-base-change; sites-cohomology.tex Tags 0E46/0E47, remark-compose-base-change / remark-compose-base-change-horizontal; blueprint Step 3.

### Former step 5

Allocated to: item assembly step 2 (explicit naturality and substitution).

Write $a:A_B\xrightarrow{\sim}R\pi_!M$ and $a':A_{B'}\xrightarrow{\sim}R\pi'_!M'$ for the inverse source comparisons, and $\beta:v^{-1}M\xrightarrow{\sim}M'=z'_*A_{B'}$. Step 4 says $R\pi'_!(\beta)C_{\pi,g}(M)g^{-1}a=a'$. Step 2 gives $c$ the etale witness $c^e$. The etale exchange is natural in its argument by [thm-cbc-finite-torsion], and the exchange of [thm-cbc-finite-level-proetale] is that etale exchange transported through the natural proper/open and pullback comparisons and conjugated by the witness isomorphisms, independently of the witness. Hence, applied to $c:M\to K$, it is natural:
$$C_{\pi,g}(K)g^{-1}(R\pi_!c)=R\pi'_!(v^{-1}c)C_{\pi,g}(M).$$
Step 2 gives $v^{-1}c=c'\beta$ after the target twist comparison. Compose the displayed equality with $g^{-1}a$, and substitute the source equality. Its right side becomes $R\pi'_!(c')a'=\tau_{E'}$ and its left side is $C_{\pi,g}(K)g^{-1}\tau_E$. This proves the equality of the actual morphisms for every $g$, with exactly the source identification in the statement.

Cited statements: thm-cbc-finite-level-proetale, thm-cbc-finite-torsion, lem-amb-cartier-kummer-map.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/thm-pur-rank-one-thom.proof.md; Step 3, explicit naturality square and its source normalization.

### Former step 6

Allocated to: lem-pur-line-kummer-field-realization (Tor input and Cartier-pair invariance), then item assembly step 3 (compact-fibre comparison).

The input $K=A_E(1)[2]$ satisfies the finite-Tor hypothesis of [lem-pur-cfiber-stalk]. Indeed [lem-pur-twist-sheaf-locally-free](3)--(4) makes $A_E(1)$ a finite locally constant, locally free rank-one sheaf. Tensoring locally with it is tensoring with $A$, so it is exact. Hence $K\otimes_A^LM$ is concentrated in degree $-2$ for any sheaf $M$; this is the interval $[-2,-2]$ in [def-weil-finite-tor-amplitude]. Apply [lem-pur-cfiber-stalk] at $\bar b$. Its canonical comparison is the compact-fibre exchange, so Step 5 with $g=\bar b$ identifies the stalk morphism of $\tau_E$ with the compact image of $c_{D_{\bar b},A}$. The chosen fibre basis carries $D_{\bar b}$ to $0\subset X=\mathbf A^1_\Omega$. Apply [lem-amb-cartier-kummer-map] to this isomorphism of Cartier pairs: the supported morphism becomes $c_{0,A}$ with the same prescribed twist.

Cited statements: lem-pur-twist-sheaf-locally-free, def-weil-finite-tor-amplitude, lem-pur-cfiber-stalk, lem-amb-cartier-kummer-map.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/thm-pur-rank-one-thom.proof.md; Step 2, first paragraph: finite-Tor compact-fibre comparison and the class of the origin.

### Former step 7

Allocated to: lem-pur-line-kummer-field-realization (roots projection and compact realization); lem-pur-section-compact-source-exchange (source normalization); item assembly step 3 (specialization over Omega).

Finally [lem-asd-finite-etale-twist-line] makes $\mu^{\mathrm{et}}_{\ell^n,X}$ locally free over $\mathbf Z/\ell^n$, so the derived tensor defining $L_X$ agrees with its ordinary tensor. The root projection comparison [lem-amb-tate-root-projection-reduction], with $r=n$, and [lem-amb-cartier-kummer-map] identify $\nu_X^*L_X$ with the prescribed $A_X(1)$ and identify $\nu_X^*c^e_{0,A}$ with $c_{0,A}$. Apply [lem-sf-class-compact-support-comparison] over the field $\Omega$ to $X\to\operatorname{Spec}\Omega$ and the morphism $c^e_{0,A}$. Both schemes and the compactification are finite type over $\Omega$, hence Noetherian by [lem-weil-pbc-finite-type-over-noetherian], even when $\Omega$ is not finite type over $k$. Naturality in the witness identifies its compact image with $\nu_\Omega^*(R\Gamma_c(X_{\mathrm{et}},c^e_{0,A}))$. On the source supported at the origin the comparison is the identity-normalized one: compute with the closed section in a compactification as in Steps 3--4, and use the counit normalization of [lem-weil-pbc-comparison-direct-image-canonical-mate] and the composition rule of [lem-weil-pbc-mate-pasting]. Thus the source is $A$, and the resulting morphism is precisely the realization of $\tau_X^e$. This proves the asserted identification of morphisms; no assertion equating supported cohomology and compact cohomology has been used.

Cited statements: lem-asd-finite-etale-twist-line, lem-amb-tate-root-projection-reduction, lem-amb-cartier-kummer-map, lem-sf-class-compact-support-comparison, lem-weil-pbc-comparison-direct-image-canonical-mate, lem-weil-pbc-mate-pasting, lem-sp-finite-compact-site-coherence, lem-weil-pbc-finite-type-over-noetherian.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/thm-pur-rank-one-thom.proof.md; Step 2, first paragraph: ordinary etale realization of the geometric-fibre morphism.
