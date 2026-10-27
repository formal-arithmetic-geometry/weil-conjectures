# Q76 stage-1 repair: lem-pur-integral-realization-shift-coherence

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-integral-realization-shift-coherence.json: repaired item, statement unchanged, four assembly steps (1788 characters).
- dag/nodes/sec-smooth-purity/lem-pur-realization-adjunction-insertion-shift.json: statement, unsplit; no Mathlib match after LeanFinder, Loogle, source grep, LeanSearch and a second semantic phrasing.
- dag/nodes/sec-smooth-purity/lem-pur-realization-tree-shift-transport.json: statement, unsplit; no Mathlib match after LeanFinder, Loogle, source grep, LeanSearch and a second semantic phrasing.
- dag/nodes/sec-smooth-purity/lem-pur-system-adjunction-open-map-shift.json: statement, unsplit; no Mathlib match after LeanFinder, Loogle, source grep, LeanSearch and a second semantic phrasing.
- dag/nodes/sec-smooth-purity/lem-pur-system-proper-open-projection-shift.json: statement, unsplit; no Mathlib match after LeanFinder, Loogle, source grep, LeanSearch and a second semantic phrasing.
- dag/nodes/sec-smooth-purity/lem-pur-compact-support-strict-roos-shift-model.json: statement, unsplit; no Mathlib match after LeanFinder, Loogle, source grep, LeanSearch and a second semantic phrasing.
- citations.json: verbatim statement quotations for every item-step citation.
- report.md: this report, including all original proof arguments and their destinations.

## Attachments

None. The exact blueprint-tag and concept searches in lean/WeilConjectures found only the different adic/rational purity realization results in EtaleCohomology/Purity/Smooth/Adic.lean and Rational.lean. The item's recorded declaration in lean/Sheaf/SixFunctors/IntegralRealizationShiftCoherence.lean is a theorem with `sorry` at line 174, so it is not an attachment. No Lean was written or compiled.

## WANTED

None. The blueprint source, source node statements and Stacks derived-limit background are present locally. These are agent-formulated shift obligations: the blueprint itself does not prove their shift assertions.

## Fault and repair

The released stage-1 repair note dated 2026-10-22 requires at least three statement-only nodes and an assembly of at most 3000 characters, keeping the statement and every old argument. The sandbox initially held dispatcher briefs only, with no node, report, search log or delivery process. I recovered the returned 11-step proof from the live node and retained it verbatim below. No previous split was overwritten, and no already completed delivery was repeated. The statement, statement dependencies, source, imported/maintainer fields and existing Lean records are retained. Five new independent obligations partition the work; none states the whole item. Their proof and proof_deps fields are empty, proof_origin is null, status is unsplit. They can be claimed separately: the tree lemma assumes local squares, the proper/open lemma assumes primitive and adjunction/open squares, and the other three have their own system constructions.

The original 10614-character argument becomes a four-step 1788-character assembly. No assembly step exceeds 2000 characters. The five new statements have self-contained coefficient, scheme, category and amplitude hypotheses, and identify the actual comparisons instead of arbitrary endpoint isomorphisms. The signed second tensor slot, independent repeated occurrences, intrinsic system equalities, noncartesian refinement case and exact strict compact-support tower are retained. No statement dispute was found, no source route was changed, and no SGA source is used.

## Review by Q76

I read master sk-thm-purity-transport/_section.md Step 2, main-20261015 sk-thm-sf-package/fix-prop-coherence.proof.md in full, the sec-smooth-purity chapter record and the current sk-thm-sf-compatibility unit. The unit's coefficient clause uses actual comparisons and adjunction maps. Neither blueprint text supplies shift coherence by itself: the old proof's agent-origin label is retained and each new source explicitly identifies the argument being extracted rather than attributing it to a nonexistent source theorem.

For each new node I read the same blueprint passages and its specific existing statement interfaces. For the insertion node I read integral-realization-recursion, generator-reduction-coherence, integral-basic-operation-shift and reduction-limit-shift-adjunction. The recursion states the actual inverse-unit and inverse-counit formulas, and the shift statements include the actual adjunction maps and d_A; therefore the new assertion concerns those maps, not an alternative selected family. The normalization hypotheses make the inverses meaningful. For the tree/transport node I read the full recursion and realization statements and all three definitions of independent occurrences, operation shift data and synchronized canonical maps. I made its assertion explicitly conditional on insertion/generator squares, preserving its strict separation from the original theorem's local work.

For the system adjunction/open node I read system-primitive-comparison-shift, derived-adjunction-shift, open-adjunction-shift, reduction-limit-shift-adjunction and open-tensor-normalization. The latter really states the two inverse-open-map adjunct normalizations for ringed diagram topoi; it is not being used for an unstated shift assertion. The typed mate formula is included in the statement and its argument is retained below. The open unit is distinguished from the reduction unit. For the proper/open/projection node I read semilinear-proper-open-mate-pasting, the primitive statement, the full realization statement and def-exchange-projection. The first gives exactly lambda_Q, alpha_Q, Gamma_Q, the clopen lift and noncartesian refinement scope. The realization statement explicitly extends the exchange/projection composite formulas to systems; this avoids applying a finite-ring theorem to an integral ring. The new node assumes prior primitive/adjunction/open shift squares and proves the remaining composites, not their coefficient normalization.

For the compact-support model node I read compact-support-restriction-of-scalars, def-weil-integral-rational-qbar-compact-support, the realization statement, operation-shift-data, ringed-strict-tower-homotopy-limit and injective-tower-roos-shifts. I also read Stacks 08TC (derived.tex, definition-derived-limit) and 0941 (sites-cohomology.tex, lemma-derived-limit-is-ok, including its K-injective proof). A derived-category cone alone is noncanonical; the obligation retains the actual strict tower, its scalar-restriction transitions and the shifted-cone comparison. The Stacks results are background, not a claim that they already state the compact-support identification.

Assembly step 1 cites the insertion statement for the local square, the recursion for the actual c_V identities, and the conditional tree statement for the tree conclusion. I checked each cited statement: none silently supplies the induction hypothesis. Their coefficient categories, normalized input conditions, etale origins, common cohomological/Tor intervals and completed operations agree with the item. A leaf gives inverse u, a unary vertex uses A_int(c)a_A and a binary vertex uses disjoint leaf sets and the signed side.

Assembly step 2 cites the system adjunction/open statement for the primitive, unit/counit, compositor, beta and gamma squares, and the proper/open/projection statement for lambda_Q, Gamma_Q and the four exchange/projection composites. The proper vertical and quasi-compact open horizontal hypotheses match the actual compactifications; the lambda factors and clopen component are exactly the normalized ones. The maps are compared before evaluation, so no faithfulness of derived evaluations is assumed.

Assembly step 3 uses the realization theorem's stated intertwining of canonical system maps with integral maps, including contexts, and the conditional tree lemma's transport clause. Since c_V and c_T are isomorphisms, the intertwining square rearranges to tau_int=c_T L(tau)c_V^{-1}; it is not read out of that theorem's proof. Pasting with the known c and system squares is precisely the conditional conclusion. Synchronized generators retain their actual parameters and intermediate domain witnesses.

Assembly step 4 uses the model node's statement about the exact tower, transitions, structural maps and shift. Its quasi-compact open/proper compactification is the one fixed in the item. Termwise/K-injective functorial shifts, not an arbitrary derived-category cone, give the required comparison. The preceding steps then specialize to S_pJ_j.

I tested the new assertions at r=0, r=1 and r=-1, the zero input, a point, identity maps, the empty open, and a repeated input at two tensor leaves. The inverse square identity preserves the direction: s2 h'=h[r] s1 implies s1 (h')^{-1}=h[r]^{-1} s2. In the second tensor slot the coefficient is (-1)^{ri} on first degree i; fixing the other leaf does not duplicate that shift. The Roos shifted component changes by (-1)^r with the unshifted component unchanged; negative shifts use inverse comparisons. Identity and empty-open maps reduce to identity or zero and satisfy the same equations. A finite shift translates finite cohomological/Tor intervals and retains compatible etale origins; finite tree induction terminates at strictly smaller subexpressions.

Against delivery-errors B-E: all unsplit nodes contain statements only; all data are introduced, formulas are TeX with single decoded backslashes, sources are honest and precise, searches were actually run, blueprint ancestry and via are filled. I checked the complete statements cited by the four steps (verbatim quotations in citations.json), not their proof internals. Every non-elementary assembly claim is covered by a cited result, the new statements carry the extracted independent arguments, proof_deps equals the union of uses, and the statements retain the old hypotheses. The generic composition/whiskering Mathlib leaf remains available to the future proofs; it is not mistaken for the local result. No off-unit theorem is used directly by the assembly.

## Not duplicates

Searches ran across the whole DAG by concept and the proposed ids, and blueprint_refs.py searched realization, shift, adjunction shift, realization shift, proper open shift, Roos, expression tree, normalized open and counit insertion. The proposed ids do not exist in the repository. The blueprint returned no exact statement; the Roos hits concern derived limits generally, not this normalized compact-support strict-system identification.

lem-pur-realization-adjunction-insertion-shift vs lem-pur-integral-realization-recursion: the existing node gives identities and explicitly asserts no shift compatibility; the new node proves the local insertion squares.

lem-pur-realization-adjunction-insertion-shift vs lem-pur-integral-basic-operation-shift: basic d_A squares alone do not state the inverse-counit insertion a_A or two-input a_tensor squares.

lem-pur-realization-adjunction-insertion-shift vs lem-pur-completed-tensor-unit-insertion: the existing node concerns completion-reflector units and tensor coherence, not the reduction/total-limit counit insertion or its shifts.

lem-pur-realization-tree-shift-transport vs lem-pur-integral-realization-shift-coherence: the new lemma is conditional on local insertion and system generator shift squares; it carries the tree/context induction, while the item must establish those local hypotheses and identify the compact-support model.

lem-pur-realization-tree-shift-transport vs lem-pur-integral-realization-recursion: non-shift recursion versus the conditional induction and conjugation of shift squares.

lem-pur-system-adjunction-open-map-shift vs lem-pur-system-primitive-comparison-shift: the existing node excludes normalized open adjunct maps and supplies no general derived adjunction/mate calculation.

lem-pur-system-adjunction-open-map-shift vs lem-sf-open-tensor-normalization: normalization formulas without shifts versus their shift compatibility in the actual system adjunctions.

lem-pur-system-proper-open-projection-shift vs lem-sf-semilinear-proper-open-mate-pasting: the existing node gives intrinsic normalization and pasting, not integer-shift squares for those maps and projection/exchange.

lem-pur-system-proper-open-projection-shift vs lem-weil-pbc-ringed-projection-mate-exact: the existing node gives one generic projection square in its second argument; the new obligation covers the proper/open lambda/Gamma factors, both tensor inputs and compactification exchange/projection and refinements.

lem-pur-system-proper-open-projection-shift vs lem-sf-finite-exchange-projection-commshift: finite coefficients versus intrinsic semilinear systems and their noncartesian proper/open refinements.

lem-pur-system-proper-open-projection-shift vs lem-sf-open-interchange-reduction-squares: coefficient reduction squares versus integer-shift squares; neither implies the other.

lem-pur-compact-support-strict-roos-shift-model vs lem-pur-injective-tower-roos-shifts: general strict-tower cone/limit shift formula versus agreement of the specific U S_p J_j reduction tower, quotient transitions and canonical compact-support realization with that model.

lem-pur-compact-support-strict-roos-shift-model vs lem-pur-compact-support-scalar-shift-normalization: scalar extension between two coefficient fields versus a single-field system-realization and the specified compact-support shift model.

lem-pur-compact-support-strict-roos-shift-model vs lem-pur-compact-support-coefficient-models: constant/completed coefficient identifications across a field extension versus the specific semilinear compact-support tower and its shift normalization.

lem-pur-compact-support-strict-roos-shift-model vs lem-weil-pbc-ringed-strict-tower-homotopy-limit: arbitrary tower existence and Roos triangle versus normalized compact-support transitions and actual shift comparison.

lem-pur-compact-support-strict-roos-shift-model vs lem-pur-integral-ambient-operation-models: ambient completed pullback and tensor towers, not the proper/open compact-support tower.

## Search evidence

search-plan.json specifies each node's own queries; searches.jsonl is the msearch.py execution log and search-results/ retains the unabridged returned hits. I read all hits. Each new node has five actual query records: LeanFinder, Loogle, source grep, LeanSearch, and a second LeanFinder phrasing. The generic NatTrans.CommShift composition/inverse lemmas in Mathlib/CategoryTheory/Shift/CommShift.lean and the unit/counit formulas in Shift/Adjunction.lean are useful proof tools, not a one-line match to the concrete system normalizations or c_V recursion. The homological-complex shift and derived-exact-functor declarations likewise do not identify the required strict compact-support tower. No unavailable search was recorded as an absence result, and no searches were invented. No new node is a Mathlib leaf.

## Original argument coverage and retained proof material

The new nodes are statement-only as required; this section is their future workers' proof material. Every old argument appears verbatim below, with its destination, original source and dependencies. The partition is:

- lem-pur-realization-adjunction-insertion-shift: old steps 1, 2, 3.
- lem-pur-realization-tree-shift-transport: old steps 4, 5, 10.
- lem-pur-system-adjunction-open-map-shift: old steps 6, 7.
- lem-pur-system-proper-open-projection-shift: old steps 8, 9.
- lem-pur-compact-support-strict-roos-shift-model: old steps 11.

This is a partition of all eleven steps. It preserves the construction choices, recursive formulas, inverse-square argument, unary and binary induction, three adjunctions and explicit mate formula, normalized inverse-open adjuncts, proper/open factorizations, projection/exchange composites, context transport and strict-tower transitions/Roos shifts.

### Proof material for lem-pur-realization-adjunction-insertion-shift

Original step 1; source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md; Maps-used and coefficient-comparison sentences: fix the operation and total-limit shift structures; agent-written shift calculation.

Write $\chi_H:H(M[r])\to H(M)[r]$ for a comparison in one designated input occurrence, with all others fixed. The basic-operation statement supplies the natural, coherent comparisons on $P_v,S_p,J_j,\otimes^L$, their integral counterparts, and $d_A$; it specifies the signed second tensor slot. The reduction/total-limit statement supplies those on $\mathcal R,\mathcal L$ and the actual $u,e$. Use the K-injective strict-tower Roos model of [lem-weil-pbc-ringed-strict-tower-homotopy-limit] for $\mathcal L$. Its derived products and $1-s$ are functorial on strict tower maps; the shifted-cone comparison fixes the sign. This specifies every shift comparison used below; no tensor/pullback lemma without a shift clause is being cited for one.

Cited statements: lem-pur-integral-basic-operation-shift, lem-pur-reduction-limit-shift-adjunction, lem-weil-pbc-ringed-strict-tower-homotopy-limit.

Original step 2; source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md; Coefficient-comparison construction: expose the canonical recursion and state the induction claim; agent-written shift calculation.

Use the recursive-characterization statement [lem-pur-integral-realization-recursion], not formulas extracted without citation from a proof of the realization theorem. It states for the actual canonical comparisons that $c_{K_i}=u_{K_i}^{-1}$,
$$a_A(M)=d_A(\mathcal LM)(\mathcal LA(e_M))^{-1},\qquad a_\otimes(M,N)=d_\otimes(\mathcal LM,\mathcal LN)(\mathcal L(e_M\otimes^Le_N))^{-1},$$
and
$$c_{AV}=A_{\rm int}(c_V)a_A(M),\qquad c_{V\otimes T}=(c_V\widehat\otimes^Lc_T)a_\otimes(M,N).$$
Here $M=V(\mathcal RK_i)$, $N=T(\mathcal RK_i)$; $u,e$ are invertible on the complete/normalized domains. The $d_A$ are exactly those specified by [lem-sf-generator-reduction-coherence]. Thus we prove a property of the given $c_V$, rather than choosing a different family. The induction claim for a tree $V$ is $\chi_{V_{\rm int}}c_{V^{(i,r)}}=c_V[r]\chi_{\mathcal LV\mathcal R}$ for each of its independent leaf slots.

Cited statements: lem-pur-integral-realization-recursion, lem-sf-generator-reduction-coherence.

Original step 3; source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md; Coefficient-comparison sentence: shift squares of the adjunction insertions; agent-written shift calculation.

The unit square from [lem-pur-reduction-limit-shift-adjunction] gives the induction base for $c_{K_i}=u_{K_i}^{-1}$ by multiplying that square by the inverse units. For $a_A$, the square for $e_M$ remains a square after applying $\mathcal LA$, by composition/whiskering [lem-weil-pbc-commshift-nattrans-comp-whisker]. The square for $d_A$ and naturality in $\mathcal LM$ give a square for $d_A(\mathcal LM)$. An invertible square remains commutative on inverting its horizontal maps: from $s_2h'=h[r]s_1$ one obtains $s_1(h')^{-1}=h[r]^{-1}s_2$. Composing these two squares gives the square for $a_A$. For $a_\otimes$, apply this argument to $e_M\otimes1$ and $1\otimes e_N$ separately and use bifunctoriality; the signed comparisons and naturality are part of the basic-operation statement.

Cited statements: lem-pur-integral-realization-recursion, lem-pur-reduction-limit-shift-adjunction, lem-pur-integral-basic-operation-shift, lem-weil-pbc-commshift-nattrans-comp-whisker.

### Proof material for lem-pur-realization-tree-shift-transport

Original step 4; source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md; Coefficient-comparison sentence: unary expression-tree induction; agent-written shift calculation.

Suppose the induction claim holds for $V$ and put $M=V(\mathcal RK_i)$. Applying $A_{\rm int}$ to that square gives the square for $A_{\rm int}(c_V)$ with the composite comparisons: this is precisely whiskering clause (ii) of [lem-weil-pbc-commshift-nattrans-comp-whisker], using the natural shift comparison of the integral operation supplied by [lem-pur-integral-basic-operation-shift]. In formulas, with the inner comparison denoted $s$, the equation is
$$\chi_{A_{\rm int}V_{\rm int}}\,A_{\rm int}(c_{V^{(i,r)}})=A_{\rm int}(c_V)[r]\,\chi_{A_{\rm int}\mathcal LV\mathcal R}.$$
Paste this with the square for $a_A(M)$ in step 3 and substitute $c_{AV}=A_{\rm int}(c_V)a_A(M)$ from [lem-pur-integral-realization-recursion]. The middle comparisons cancel, yielding the induction claim for $AV$. Every invocation decreases the number of tree nodes.

Cited statements: lem-pur-integral-realization-recursion, lem-pur-integral-basic-operation-shift, lem-weil-pbc-commshift-nattrans-comp-whisker.

Original step 5; source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md; Coefficient-comparison sentence: binary expression-tree induction; agent-written shift calculation.

At a tensor node the designated occurrence lies in exactly one of the two independent leaf sets. If it lies in $V$, tensor its induction square with $c_T$ and use naturality of the completed tensor comparison in the other factor; if it lies in $T$, do the same with $c_V$ fixed. Paste with the corresponding slot square for $a_\otimes$ from step 3. The tensor recursion of [lem-pur-integral-realization-recursion] then gives the claim for $V\otimes T$. In the second case the comparison is the signed one of [lem-pur-integral-basic-operation-shift]; it is not the unsigned identification of graded objects. These unary and binary cases exhaust the finite tree. All intermediate systems remain in the explicitly assumed normalized and bounded domains; an integer shift translates a finite interval to a finite interval.

Cited statements: lem-pur-integral-realization-recursion, lem-pur-integral-basic-operation-shift, lem-weil-pbc-commshift-nattrans-comp-whisker.

Original step 10; source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md; Coefficient-comparison sentence: conjugation by the given realization maps and arbitrary contexts; agent-written shift calculation.

Any allowed system map $\tau:V\to T$, including an allowed expression context around a generator, is a composite and whiskering of the preceding maps. Clause (ii)/(iii) and composition in [lem-weil-pbc-commshift-nattrans-comp-whisker] give its shift square. For a tensor context fix the other input and apply that clause; for several changing occurrences factor into single-slot maps by bifunctoriality. The realization statement gives the actual intertwining equation
$$\tau_{\rm int}=c_T\,\mathcal L(\tau)\,c_V^{-1}.$$
Both $c$ squares were proved by tree induction and $\mathcal L$ has its fixed comparison. Paste their squares with the square for $\mathcal L(\tau)$, using the inverse-square identity in step 3. The result is exactly the shift square for the corresponding integral map, together with the compatible realization square. No equality is detected after evaluating systems: all equations used here hold before evaluation.

Cited statements: lem-sf-integral-compactification-system-realization, lem-pur-reduction-limit-shift-adjunction, lem-weil-pbc-commshift-nattrans-comp-whisker.

### Proof material for lem-pur-system-adjunction-open-map-shift

Original step 6; source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md; Maps-used sentence: system primitives and the three actual adjunctions; agent-written shift calculation.

For system structural maps start with the primitive squares of [lem-pur-system-primitive-comparison-shift], covering pullback compositors, pullback/tensor comparisons, tensor reassociation/unit/symmetry, open composition and the specified restriction/clopen maps. For $P_v\dashv S_v$ use [lem-weil-pbc-derived-adjunction-shift] on the small ringed diagram topoi whose module categories realize $\mathscr S$; these are the canonical derived inverse/direct-image adjunctions of [lem-sf-integral-compactification-system-realization]. For $J_j\dashv P_j$ use [lem-pur-open-adjunction-shift], and for $\mathcal R\dashv\mathcal L$ use [lem-pur-reduction-limit-shift-adjunction]. Thus their units and counits have shift squares before evaluation. More generally an adjunct of $h:FX\to Y$ is $G(h)\eta_X$, and a mate of $\alpha:F_2H\to TF_1$ is $G_2(T\varepsilon_1)G_2(\alpha G_1)\eta_2HG_1$. Every factor has a shift square when $\alpha$ does; composition/whiskering pastes them. In particular the direct-image compositors, conjugate to pullback compositors by the realization statement, have shift squares. This is an explicit finite-composite argument, not an assumption that mates automatically preserve the chosen shifts.

Cited statements: lem-pur-system-primitive-comparison-shift, lem-weil-pbc-derived-adjunction-shift, lem-pur-open-adjunction-shift, lem-pur-reduction-limit-shift-adjunction, lem-sf-integral-compactification-system-realization, lem-weil-pbc-commshift-nattrans-comp-whisker.

Original step 7; source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md; Maps-used sentence: open base-change and open tensor normalization; agent-written shift calculation.

Let $\beta:P_gJ_j\cong J_{j'}P_{g_U}$ and $\gamma:J_jM\otimes^LN\cong J_j(M\otimes^LP_jN)$ be the open maps of [lem-sf-open-tensor-normalization], whose statement also applies to the ringed diagram topoi of systems. Its normalization specifies $\beta^{-1}$ as the open adjunct of $P_{g_U}u_M$ followed by the inverse pullback compositor, and $\gamma^{-1}$ as the open adjunct of $u_M\otimes1$ under restriction/tensor comparison. Here $u_M:M\to P_jJ_jM$ is the open unit, not the reduction unit. The unit squares are [lem-pur-open-adjunction-shift]; the compositor and tensor squares are [lem-pur-system-primitive-comparison-shift]. Applying the adjunct formula in step 6 proves the shift square for each inverse map, in either tensor input. Inverting those squares proves it for $\beta,\gamma$. Hence the actual normalized open maps are covered, rather than maps chosen by checking their finite evaluations.

Cited statements: lem-sf-open-tensor-normalization, lem-pur-open-adjunction-shift, lem-pur-system-primitive-comparison-shift, lem-weil-pbc-commshift-nattrans-comp-whisker.

### Proof material for lem-pur-system-proper-open-projection-shift

Original step 8; source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md; Maps-used sentence: intrinsic open restriction and proper/open mate; agent-written shift calculation.

For the proper/open square $Q$ of [lem-sf-semilinear-proper-open-mate-pasting], its hypotheses are exactly the proper vertical arrows and quasi-compact open horizontal arrows in the realization statement. In its notation
$$\lambda_Q:P_iS_pJ_k\cong S_qP_bJ_k\cong S_qJ_s\cong S_qS_s\cong S_r.$$
The first arrow is conjugate to the normalized cartesian open comparison, so its square follows from steps 6-7. The next two arrows use $P_bJ_k\cong J_s$ and $J_s\cong S_s$ for the clopen $s$, covered by [lem-pur-system-primitive-comparison-shift]. The last is the direct-image compositor from step 6. Pasting gives the square for this specified $\lambda_Q$. The same proper/open statement identifies $\Gamma_Q$ as the open adjunct of $\lambda_Q^{-1}$; explicitly
$$\Gamma_Q=S_pJ_k\varepsilon_r\circ S_p\alpha_QS_r\circ\eta_pJ_iS_r,\quad \alpha_Q=(J_bJ_sP_sP_q\cong J_kP_r)\circ J_b\pi_sP_q\circ\beta_{i,p}.$$
The normalized $\beta$, clopen projection $\pi_s$, compositors and proper units/counits all have the squares already established. This displayed factorization proves the square for $\Gamma_Q$ by pasting in the semilinear derived category. It also handles noncartesian refinement squares allowed by the cited statement.

Cited statements: lem-sf-semilinear-proper-open-mate-pasting, lem-pur-system-primitive-comparison-shift, lem-sf-open-tensor-normalization, lem-pur-open-adjunction-shift, lem-weil-pbc-derived-adjunction-shift, lem-weil-pbc-commshift-nattrans-comp-whisker.

Original step 9; source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md; Maps-used sentence: write the projection and exchange composites; agent-written shift calculation.

The realization statement specifies system exchange and projection maps by the composites of [def-exchange-projection]. In system notation their factors are
$$\operatorname{Ex}_*=S_{f'}P_{g'}\varepsilon_f\circ S_{f'}\theta S_f\circ\eta_{f'}P_gS_f,\qquad \pi_{p;M,N}=S_p((\varepsilon_{p,M}\otimes1)\mu_p)\circ\eta_{p,S_pM\otimes N}.$$
The compact-support exchange is $S_{p'}\beta\circ\operatorname{Ex}_{*,p}J_j$; the compact-support projection is $S_p\gamma\circ\pi_{p;J_jM,N}$, with the pullback compositor inserted in $\gamma$ as in the definition. Each displayed factor is a primitive square, an adjunction square or a normalized open square from steps 6-7. Composition/whiskering therefore proves these four shift equations, separately in each projection input. The proper/open squares from step 8 and direct-image/open compositors give all compactification composition and refinement maps by the same finite pasting. This uses the stated system composite formulas, not a finite-coefficient theorem applied to an integral coefficient ring.

Cited statements: lem-sf-integral-compactification-system-realization, def-exchange-projection, lem-weil-pbc-commshift-nattrans-comp-whisker.

### Proof material for lem-pur-compact-support-strict-roos-shift-model

Original step 11; source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md; Unit Step 2 (adic transport): strict compact-support tower and its fixed Roos shift; agent-written shift calculation.

For $f=pj$ take a K-flat strict reduction model for $\mathcal RK$ and simultaneous direct-image/open models. Their termwise scalar restriction $U_WS_pJ_j\mathcal RK$ is the strict tower chosen in the statement. The restriction-of-scalars comparison of [lem-sf-compact-support-restriction-of-scalars] identifies its transition from $m$ to $n$ with $Rp_{*,m}j_!$ of the reduction map followed by the coefficient-restriction isomorphism. These are exactly the transitions written in [def-weil-integral-rational-qbar-compact-support]. The realization statement identifies $c_{S_pJ_j}$ with this integral compact-support functor, including its maps. Use the natural total-limit Roos model [lem-weil-pbc-ringed-strict-tower-homotopy-limit] of this strict tower, not a cone assigned to an incoherent diagram of objects in a derived category. Its termwise shift and shifted-cone comparison define the completed integral shift fixed in the statement. Consequently the already proved case $V=S_pJ_j$ is the required compact-support square for that model. The identity shift, positive iterations and inverse comparisons for negative integers give the same equations for every $r\in\mathbf Z$.

Cited statements: lem-sf-integral-compactification-system-realization, lem-sf-compact-support-restriction-of-scalars, def-weil-integral-rational-qbar-compact-support, lem-weil-pbc-ringed-strict-tower-homotopy-limit, lem-pur-integral-basic-operation-shift, lem-weil-pbc-commshift-nattrans-comp-whisker.

## Unfinished work

Only the five new obligations' proofs are deliberately left for independently dispatched stage-1 workers, as the human's re-split order requires. They have complete statements and genuine search records. There is no missing part of this item's assembly, no source request, and no Lean/build activity.

## Validation

Server dry run exited 0: `OK (not pushed) deliver/Q76/lem-pur-integral-realization-shift-coherence at dfcc429be2a: preflight passed`. This includes server preflight, check_dag and review_split. Local shape checks also confirm byte-identical item statement and statement dependencies, proof_deps equal to uses, 1788 assembly characters, and five statement-only unsplit nodes with five genuine searches each. No compiler or Lake command was run. A final dry run of this report revision is required before push.
