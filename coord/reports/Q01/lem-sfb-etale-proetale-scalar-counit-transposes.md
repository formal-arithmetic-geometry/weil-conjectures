## Worker report

Q01, 2026-10-21. Stage 1 only; repair of the human's 2026-10-21 re-split request for `lem-sfb-etale-proetale-scalar-counit-transposes`.

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-etale-proetale-scalar-counit-transposes.json`: existing statement, unchanged; split into three assembly steps, 1450 characters total.
- `dag/nodes/sec-six-functors-basics/lem-sfb-pasted-mates-counit-normalization.json`: new statement-only categorical lemma, status `unsplit`, no Mathlib match, empty proof and proof dependencies. It isolates the computation for ONE path of two mates with arbitrary input and output arrows, and is used twice.
- `citations.json`: verbatim statement quotes for the new node cited by parent steps 1 and 3.
- `report.md`: this report. The sandbox also retains the search log and sandbox-local generation scripts.

Attachments: none. The library's `AlgebraicGeometry.ProEtale.etaleProEtale_scalar_counit_transposes`, `lean/Sheaf/Paper/EtaleProEtaleScalarCounitTransposes.lean`, ends in `sorry`. No declaration tagged with the item was found under `lean/WeilConjectures/`; the project's existing statement is not an attachment. Related formal helpers in `FiniteCoefficientDirectImage.lean` and `HorizontalRectangleInverseMateFixedTransport.lean` state different conclusions; no exact project declaration for the child was found.

WANTED: none. The categorical assertion is agent-formulated, rather than attributed as a theorem to a Stacks tag.

What was wrong: the live node's seven-step proof was correct but exceeded the human's granularity requirement (3036 characters). There were no item node, report, citations or older search log in this sandbox at startup, only dispatcher marker files. I therefore copied the current live node, including all its inherited research and Lean/review metadata, and continued from that version. The item statement, statement dependencies, Lean record, proof-origin record and all inherited searches are retained; only the proof, proof dependencies and split report change. There is no statement dispute or route change.

What remains: the new child is deliberately unsplit so another worker can claim its proof independently; the parent can be proved as soon as that lemma is available. No Lean was written and no compiler, Lake or local DAG/preflight checker was run. Required server checks and the direct delivery are run through the authorized launcher commands.

## Repair of the return

The delivery adds one independently claimable unsplit node, rather than only shortening prose. Its hypotheses and conclusion are self-contained and categorical; it does not assume or prove a comparison cube, mention the two site/scalar paths, assert their equality, or identify their common geometric normal form. Therefore the parent still performs a substantive application of its cube hypothesis; its whole claim has not been moved into the child.

The original proof's repeated arguments are allocated as follows:

- Old step 1 (output-counit naturality followed by the outer mate identity) and old step 2 (naturality of the outer square followed by the inner mate identity) are exactly the child's four normalization identities, specialized in new parent step 1 to $(l_A,p_A,p_B)$ and squares $(d_A,c^p)$. Here the output arrow is $t=\delta_{X,J}$ and the input arrow is the identity.
- Old steps 4, 5 and 6 are the SAME child argument specialized in new parent step 3 to $(l_A,l_B,p_B)$ and squares $(c^e,d_B)$. Here $t$ is the identity and the input arrow is $b=\delta_{Y,P}$. In particular the child's naturality square for $\alpha_2$ is precisely the old naturality square for $d_B$ at $\gamma^e_J$, and its inner-mate identity is precisely old step 6 for $\gamma^e_J$.
- Old step 3 is the explicit elementary assembly in new parent step 2: one naturality identity for $\delta_X$ and substitution of the stated cube. This argument remains written out, rather than hidden in a new node for an elementary fact.
- Old step 7 is retained at the end of new parent step 3: every map is in $D(X_{\mathrm{proet}},B)$ with the stated endpoints, so is $B$-linear, and the child uses no inverses or extra hypotheses.

Thus every argument is preserved, with the repeated non-elementary calculations delegated to the new node. The parent has 1450 characters of proof, each of its three steps is shorter than 2000 characters, and the independently claimable child represents the shared multi-step argument, rather than a copied clause of the parent. One lemma used twice avoids manufacturing two duplicate nodes for its two substitutions.

## Sources and search evidence

For both the item and child I read `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-scalar-six/det-prop-scalar-six-direct-image.proof.md`: Formal properties, especially the sentence about composition of mates and units/counits; and Finite rings, transport of the canonical comparison through $\nu^*$. I also read the chapter record and the entire unit record `sk-prop-scalar-six`, whose ordinary direct-image step is the route. The new node implements the formal part of that step, without changing the coefficient layers or claiming a direct-image comparison is invertible on all unbounded objects.

I checked the mate orientation against `literature/stacks-project/sites-cohomology.tex`, Tag 07A7, `remark-base-change`, lines 4033–4057: the base-change map is adjoint to pullback of the source counit after the inverse-image identification. That remark does not itself state the new abstract two-mate formula, and the child's source is consequently the agent-written blueprint interface, not a false attribution to 07A7. No SGA source is used.

Before creating the node I searched the whole DAG for mate composition, pasting, counit and transpose statements, and the entire imported blueprint with `tools/blueprint_refs.py search` for `mate`, `counit`, `pasting`, `counit transpose`, `two squares` and `counit normalization`. I read the relevant existing candidates below. The ancestor command returns `det-prop-scalar-six-direct-image`; the child uses this ancestor, a specific proof place, and via-list `[lem-sfb-etale-proetale-scalar-counit-transposes, lem-sfb-etale-proetale-scalar-mate]`. No blueprint statement matches the new lemma, so `same_as` is empty. I also checked the candidate id did not occur in the DAG or upstream Lean source.

Eight NEW searches were actually run with the required `msearch.py Q01 lem-sfb-etale-proetale-scalar-counit-transposes` command: two each of LeanFinder, LeanSearch, Loogle and grep. Their exact queries and unedited result summaries are copied from `searches.jsonl` into the child's `mathlib_searches`. Both natural-language services answered successfully. The second natural-language phrasing includes all three adjunctions and the complete component formula. I did not invent searches or repeat inherited ones.

I read Mathlib `CategoryTheory/Adjunction/Mates.lean`, particularly `mateEquiv_counit` at line 123 and `mateEquiv_vcomp` at line 170, and `CategoryTheory/Adjunction/Basic.lean`, `homEquiv_naturality_left_symm` at line 226 and `homEquiv_naturality_right_symm` at line 243. The former mate identity concerns one square; the pasting theorem identifies transformations, not this component transpose with arbitrary input/output arrows; the two Hom equivalence laws are separate boundary naturality identities. None states the full new formula or specializes to it in one line. They are material for the child's future proof, whose multi-step argument is written below for preservation only; the child itself is statement-only.

## Not duplicates

lem-sfb-pasted-mates-counit-normalization vs lem-weil-pbc-mate-pasting: the existing Mathlib leaf asserts equalities of pasted mate transformations, with several pasting conventions. The new lemma asserts an explicit component counit transpose for one path, including arbitrary arrows $b$ and $t$; it requires both mate normalization and naturality, not just specialization of the pasting statement.

lem-sfb-pasted-mates-counit-normalization vs lem-weil-pbc-mate-whisker: that statement changes a single square by natural transformations on its boundary functors and identifies its mate; the new statement composes two mates and evaluates their counit transpose with arbitrary object morphisms, which need not extend to boundary natural transformations.

lem-sfb-pasted-mates-counit-normalization vs lem-amb-mate-unit-counit: that leaf is the counit identity for one mate, with no input/output arrows and no second square. The child must also commute the second square past the first mate and normalize the remaining inner counit.

lem-sfb-pasted-mates-counit-normalization vs new-integral-residue-mate-pasting: that node compares inverse mates under composite extension/restriction-square isomorphisms; it does not assert the forward mates' boundary-arrow counit formula.

lem-sfb-pasted-mates-counit-normalization vs lem-coef-dg-mate-pasting: that statement concerns enhanced transformation objects and coherent parameter homotopies, and asserts pasting of mates. The new node concerns ordinary categories and a component transpose at arbitrary object arrows, without enhanced data or a coherent-pasting conclusion.

lem-sfb-pasted-mates-counit-normalization vs lem-coef-dg-mate-transpose: that enhanced single-square transposition theorem has neither two composable squares nor the boundary-arrow normal form in ordinary categories.

lem-sfb-pasted-mates-counit-normalization vs lem-weil-pbc-exchange-mate-cube: that node assumes a commutative inverse-image cube and concludes the corresponding cube for mates, whereas the child treats one two-square path and assumes no cube.

lem-sfb-pasted-mates-counit-normalization vs lem-pe-direct-image-mate-compatibility: that lemma gives the unit/counit equations for one bounded-below site-comparison mate, not the general boundary-arrow two-mate calculation.

lem-sfb-pasted-mates-counit-normalization vs lem-sp-flat-coefficient-chain-transpose: that lemma identifies a K-flat chain model and its derived adjunct on the etale site. The new lemma has no complexes or model comparison and concerns ordinary categorical pasting.

lem-sfb-pasted-mates-counit-normalization vs det-sp-tower-exceptional-bc: the blueprint search hit concerns exceptional base change for finite and completed coefficient towers and their reduction compatibility, not the ordinary categorical two-mate formula.

lem-sfb-pasted-mates-counit-normalization vs lem-sfb-etale-proetale-scalar-counit-transposes: the parent compares two different paths via a cube and specifies their common geometric normal form. The child computes only one generic path before that cube substitution; it is strictly smaller work and is reused for both paths.

## Preserved argument for the new unsplit node

This is handoff material in the report, NOT proof steps or proof dependencies in the new node. Put $h=\beta_{1,J}$ and expand $q$ with functoriality of $L_2$. First use naturality of $\varepsilon_2$ at $t$:
$$\varepsilon_{2,K}L_2R_2(t)=t\varepsilon_{2,H_2H_1J}.$$
The outer mate-counit identity gives
$$\varepsilon_{2,H_2H_1J}L_2(\beta_{2,H_1J})=H_2(\varepsilon_{1,H_1J})\alpha_{2,R_1H_1J}.$$
Next use naturality of $\alpha_2$ at $h:G_1R_0J\to R_1H_1J$:
$$\alpha_{2,R_1H_1J}L_2G_2(h)=H_2L_1(h)\alpha_{2,G_1R_0J}.$$
Thus the transpose becomes
$$t\,H_2(\varepsilon_{1,H_1J})\,H_2L_1(h)\,\alpha_{2,G_1R_0J}\,L_2(b).$$
Functoriality combines the two adjacent $H_2$ images. The inner mate-counit identity is
$$\varepsilon_{1,H_1J}L_1(h)=H_1(\varepsilon_{0,J})\alpha_{1,R_0J}.$$
Substitute and distribute $H_2$ over this composite to obtain exactly
$$t\,H_2H_1(\varepsilon_{0,J})\,H_2(\alpha_{1,R_0J})\,\alpha_{2,G_1R_0J}\,L_2(b).$$
All compositions here are right to left, and the final arrow is $L_2Q\to K$. The two mate-counit identities are the statement of the existing Mathlib leaf `lem-amb-mate-unit-counit`, whose statement I opened. The remaining displayed equations are explicit naturality squares; all omitted parentheses are associativity. No claim about the two geometric paths or their cube occurs in this argument.

## Review by Q01

I reviewed B–E of `coord/delivery-errors.md` with the node files and source text open. The child's statement introduces six categories, all adjunctions and functors, the two squares, their mate convention, all objects and both boundary arrows; categories and mates cite the actual definition nodes `def-nagata-category` and `def-weil-pbc-adjunction-mate`, whose statements I read. The component formula for a mate is written explicitly so its orientation can be checked without external convention. The child has empty proof, proof dependencies and proof origin; its handoff argument lives only in this report. TeX is written once and the source place identifies the blueprint's actual sentence rather than an unstable numbering. The human specifically requested extracting this repeated multi-step normalization as separately claimable work. I kept the single naturality/cube substitution elementary instead of creating a trivial cube-substitution node.

For parent step 1 I opened the child's entire statement and substituted the three adjunctions $(l_A,r_A),(p_A,s_A),(p_B,s_B)$. The square types become $p_AC_Y^A\to C_X^Al_A$ and $p_BT_Y^p\to T_X^pp_A$. Their mates are precisely $\beta^A$ and $\gamma^p$ by the parent's own definitions. $Q=T_Y^pC_Y^AP$, $K=C_X^BT_X^eJ$, $b$ is the identity and $t=\delta_{X,J}$ has source $T_X^pC_X^AJ$ and that target. The child's displayed conclusion therefore says exactly the raw $U^\flat$ equation used by this step. No child proof is used.

For parent step 2, there is no non-elementary citation: the displayed equality is the naturality square for the given natural transformation $\delta_X$ on the already-typed arrow $E:l_AP\to J$, followed by direct substitution of the cube assumed in the statement. The last operation is $C_X^B$ preserving composition. There is no unstated comparison identification, cancellation, or existence result hidden here.

For parent step 3 I again opened the child statement. The three adjunctions are $(l_A,r_A),(l_B,r_B),(p_B,s_B)$ and its squares are $c^e,d_B$, so its mates are $\gamma^e,\beta^B$. Here $Q=T_Y^pC_Y^AP$, $b=\delta_{Y,P}:Q\to C_Y^BT_Y^eP$, $K=C_X^BT_X^eJ$ and $t$ is its identity. The child's exact formula is the four-factor equation written for $V^\flat$. Combining the first two images under $C_X^B$ yields the parent's claimed normal form; the output category is already a derived module category over $B$, establishing linearity. I wrote a verbatim quote of the child's conclusion for BOTH applications in `citations.json` and checked both are actual substrings of its statement. These are the only proof citations and their union equals `proof_deps`.

I checked edge cases of the child, rather than assuming transposition makes it true. With all three adjunctions identity it reduces to associativity of $t\alpha_2\alpha_1b$; with $b$ or $t$ zero in an additive category both sides vanish; with identity squares and boundary arrows it reduces to the single ordinary counit. If one category is empty there are no specified $J,Q,K$ and no ill-defined evaluation. For a noninvertible square, take all functors identity on abelian groups, $\alpha_1=2\mathrm{id}$, $\alpha_2=3\mathrm{id}$; both transposes equal $t\,6\mathrm{id}\,b$, without cancellation of 2 or 3. This tests the absence of isomorphism hypotheses. For the parent I checked $f=\mathrm{id}$, $a=\mathrm{id}$, $J=0$ and a nonflat coefficient change $\mathbf Z\to\mathbf Z/2$: the substitutions only use ambient adjunctions, not t-exactness, boundedness or flatness. The cube is required exactly at $P=r_AJ$ and nowhere else.

The checks corrected granularity and work allocation, not any mathematical statement. All nodes lie in the same unit except the already existing definition dependencies; no off-unit proof tool approval is needed. I found no cycle: the new node only depends on category and mate definitions, neither of which depends on the parent. The elementary parent step is below the long-step threshold and the two non-elementary steps are direct specializations with every parameter specified. There is no SGA route, no target change, and no Lean or repository write.

## Original live proof retained verbatim

The following is the full seven-step proof read at startup, for comparison and to preserve every original argument across retries.

### Original step 1

Put $E=\varepsilon^e_{A,J}:l_AP\to J$, $K=C_X^AJ$, $h=\beta^A_J:C_Y^AP\to s_AK$, and $D=\delta_{X,J}$. Expand $U$ and use functoriality of $p_B$. Naturality of the counit $\varepsilon^p_B$ at $D:T_X^pK\to C_X^BT_X^eJ$ says $\varepsilon^p_{B,C_X^BT_X^eJ}\circ p_Bs_B(D)=D\circ\varepsilon^p_{B,T_X^pK}$. Apply [lem-amb-mate-unit-counit] to $\gamma^p$ with $(L_1,R_1,L_2,R_2,G,H)=(p_A,s_A,p_B,s_B,T_Y^p,T_X^p)$ at $K$. Substitution gives
$$U^\flat=D\circ T_X^p(\varepsilon^p_{A,K})\circ c^p_{s_AK}\circ p_BT_Y^p(h).$$

Uses: lem-amb-mate-unit-counit.

### Original step 2

Naturality of $c^p:p_BT_Y^p\to T_X^pp_A$ at $h$ gives $c^p_{s_AK}\circ p_BT_Y^p(h)=T_X^pp_A(h)\circ c^p_{C_Y^AP}$. The mate-counit identity [lem-amb-mate-unit-counit], with $(L_1,R_1,L_2,R_2,G,H)=(l_A,r_A,p_A,s_A,C_Y^A,C_X^A)$ at $J$, gives $\varepsilon^p_{A,K}\circ p_A(h)=C_X^A(E)\circ d_{A,P}$. Functoriality of $T_X^p$ in the preceding step therefore yields
$$U^\flat=D\circ T_X^pC_X^A(E)\circ T_X^p(d_{A,P})\circ c^p_{C_Y^AP}.$$

Uses: lem-amb-mate-unit-counit.

### Original step 3

The natural transformation $\delta_X:T_X^pC_X^A\to C_X^BT_X^e$, evaluated on $E:l_AP\to J$, satisfies $D\circ T_X^pC_X^A(E)=C_X^BT_X^e(E)\circ\delta_{X,l_AP}$. Replace the first two factors in Step 2 by this equality. The cube identity assumed in the statement replaces the remaining three factors $\delta_{X,l_AP}\circ T_X^p(d_{A,P})\circ c^p_{C_Y^AP}$ by $C_X^B(c^e_P)\circ d_{B,T_Y^eP}\circ p_B(\delta_{Y,P})$. Combining the two adjacent images under $C_X^B$ gives
$$U^\flat=C_X^B\bigl(T_X^e(E)\circ c^e_P\bigr)\circ d_{B,T_Y^eP}\circ p_B(\delta_{Y,P}).$$

Uses: .

### Original step 4

Put $g=\gamma^e_J:T_Y^eP\to r_BT_X^eJ$. Expanding $V$ and its transpose gives
$$V^\flat=\varepsilon^p_{B,C_X^BT_X^eJ}\circ p_B(\beta^B_{T_X^eJ})\circ p_BC_Y^B(g)\circ p_B(\delta_{Y,P}).$$
Apply [lem-amb-mate-unit-counit] to $\beta^B$, with $(L_1,R_1,L_2,R_2,G,H)=(l_B,r_B,p_B,s_B,C_Y^B,C_X^B)$ at $T_X^eJ$. Thus
$$V^\flat=C_X^B(\varepsilon^e_{B,T_X^eJ})\circ d_{B,r_BT_X^eJ}\circ p_BC_Y^B(g)\circ p_B(\delta_{Y,P}).$$

Uses: lem-amb-mate-unit-counit.

### Original step 5

Naturality of $d_B:p_BC_Y^B\to C_X^Bl_B$ at $g:T_Y^eP\to r_BT_X^eJ$ is
$$d_{B,r_BT_X^eJ}\circ p_BC_Y^B(g)=C_X^Bl_B(g)\circ d_{B,T_Y^eP}.$$
Substitute this in Step 4 and combine the adjacent images under $C_X^B$:
$$V^\flat=C_X^B\bigl(\varepsilon^e_{B,T_X^eJ}\circ l_B(g)\bigr)\circ d_{B,T_Y^eP}\circ p_B(\delta_{Y,P}).$$

Uses: .

### Original step 6

Apply [lem-amb-mate-unit-counit] to $\gamma^e$, with $(L_1,R_1,L_2,R_2,G,H)=(l_A,r_A,l_B,r_B,T_Y^e,T_X^e)$ at $J$. Its equation is $\varepsilon^e_{B,T_X^eJ}\circ l_B(g)=T_X^e(E)\circ c^e_P$. Substitute in Step 5. The resulting expression for $V^\flat$ is exactly the expression for $U^\flat$ in Step 3, with $E=\varepsilon^e_{A,J}$, proving both required equalities.

Uses: lem-amb-mate-unit-counit.

### Original step 7

All the displayed composites are in $D(X_{\mathrm{proet}},B)$: their source is $p_BT_Y^pC_Y^AP$ and their target is $C_X^BT_X^eJ$. In particular they are $B$-linear derived module morphisms. Every equality above is functoriality, a naturality square, a mate-counit identity, or the assumed cube identity. None cancels a direct-image mate or uses its invertibility, and none invokes boundedness, geometric finiteness, or flatness.

Uses: .
