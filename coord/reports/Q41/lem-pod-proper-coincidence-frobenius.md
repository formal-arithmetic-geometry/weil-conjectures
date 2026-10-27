# Worker report — Q41

## Files written

- `dag/nodes/sec-poincare-duality/lem-pod-proper-coincidence-frobenius.json`: repaired item, unchanged statement; 2073-character assembly proof.
- `dag/nodes/sec-poincare-duality/lem-pod-identity-compactification-system-mate.json`: statement, unsplit; no Mathlib match. Canonical identity-open normalization at finite and strict-system levels, its specified open/direct-image mate equation, and quotient-transition tower cancellation.
- `dag/nodes/sec-poincare-duality/lem-pod-identity-compactification-limit-comparisons.json`: statement, unsplit; no Mathlib match. Compatibility of the actual alpha/beta total-limit operation comparisons with the proper comparison, including the prescribed coefficient passage.
- `citations.json`: one verbatim statement quotation for every use in every step.

## Attachments

None. Searched `lean/WeilConjectures/` by blueprint tag and coincidence/Frobenius notions; there is no complete project declaration stating this item. Read `lean/Sheaf/Paper/ProperCoincidenceFrobenius.lean`: `properCoincidenceFrobeniusFinite`, `properCoincidenceFrobeniusIntegral`, `properCoincidenceFrobeniusRational`, and `properCoincidenceFrobenius` still have `sorry`. The source and target common-stage normalization existence theorems also have `sorry`. Existing definitions and sorried theorem interfaces are not attachments.

## WANTED

None. Both blueprint snapshots and Deligne Weil I are locally available. No SGA source was used.

## Fault repaired

The released stage-1 repair note requires at least two comparable new statement-only nodes and an assembly of at most 3000 characters. The original four-step argument had 4175 characters, including an integral comparison normalization requiring separate work. This repair leaves the statement and statement dependencies unchanged and creates two separately provable interfaces of 2543 and 2491 characters. Both have empty proof and proof_deps, null proof_origin, status unsplit, full sources and logged searches. The first does not assert the total-limit Frobenius transport theorem; the second asserts only the normalization of the two operation comparison maps, without proving the exchange or point-cohomology equations. Neither restates the whole item.

The named sandbox initially contained only dispatcher marker files, not a retained node/report/search file. I copied the current read-clone item as the baseline. The released repair note explicitly reopens this item despite its historical split/review records. The current source provides the complete old proof; it is copied verbatim below, with the allocation of each argument. No repository, launcher, Lean source, compiler, Lake or git command was used to change the shared read clone.

## Argument allocation (no argument discarded)

Old step 1: the unique factorization through the identity open, presheaf/sheafification identification on objects and morphisms, and finite proper comparison are the finite part of the system-mate node. The normalized open-square map is its finite open-mate assertion. The item now substitutes that assertion into the explicit two-arrow exchange definition. This retains the specified source and target comparisons, rather than choosing an arbitrary isomorphism.

Old step 2, first part: equality of the strict coefficient towers, the quotient-induced transitions, and the restriction-of-scalars comparison are included in the system-mate node. The underlying tower identification is already available in `lem-sf-package-compactified-tower-comparisons` and can be reused when the child is split; it is not presented as a novel standalone fact. Identity system extension, its actual unit and counit, and the open mate identity are also stated in that child. The equation there includes naturality of the ordinary mate: after cancelling identity extension, the two pre-limit exchange composites agree.

Old step 2, second part: the assertion that the actual alpha_!, beta_! agree with alpha_*, beta_* is the limit-comparisons node. Its two equations retain the canonical identity-open comparison on every system source and target. The assembly applies the total-limit functor to the whole-system equation, inserts those two comparison equations, and gives the explicit composite calculation. Scalar localization and a common finite coefficient field then preserve the equality as required by the exchange definition; these operations are also identified in the child statement. Finite evaluations are never used to detect equality of morphisms.

Old step 3: remains the explicit elementary composition calculation in item step 3. The cited existing naturality theorem supplies its only substantive premise, so no new node is made for a two-line functoriality consequence. The exact roles of N_!, N_*, G, F and the pulled object M' are retained.

Old step 4: remains the cohomology-functor application in item step 4, with every integer degree included. There is no separate per-degree identification replacing a derived equality: the actual equality in the derived point category is established first.

## Searches

Before creating the children I searched the whole DAG for identity-open/identity-compactification, strict systems, alpha_!/beta_!, and Frobenius exchange, and ran `tools/blueprint_refs.py search` for proper coincidence, identity open, strict coefficient, restriction scalars, Frobenius exchange, proper compact, identity compactification, semilinear, identity adjunction, and operation comparisons. The ancestor command returns `prop-cohomological-finiteness`; both children have that ancestor with via `[lem-pod-proper-coincidence-frobenius]`, a precise proper-case Step 6 location, and same_as [].

All Mathlib searches in the new JSON files were actually run with the prescribed msearch command and are in searches.jsonl. The two semantic phrasings per argument were read. Tower searches returned ordinary inverse systems, compactly supported functions and integration, not pro-etale derived coefficient systems. Open-mate searches returned abstract adjunction triangles, conjugateEquiv, derived adjunction component identities and condensed adjunctions. The Loogle searches returned generic identity adjunctions and mates. I read Mathlib/CategoryTheory/Adjunction/Mates.lean; its adjunction identities do not identify the project-specific extension-by-zero, quotient-transition, or total-limit operation comparisons in one line. Source grep found no geometric strict-system identity-compactification exchange; the semilinear grep's four hits concern Presburger sets. Hence neither child is a Mathlib leaf. No unavailable search was recorded as no-match, and no old search was invented or overwritten.

## Not duplicates

lem-pod-identity-compactification-system-mate vs lem-sf-open-tensor-normalization: the existing statement gives general normalized open pullback/tensor maps, including diagram topoi; the new node combines the actual identity-open adjunction cancellation with the ordinary direct-image mate word on the specified quotient-transition system and its finite form. It states the pre-limit naturality square with F_a(u), not merely an open-base-change isomorphism.

lem-pod-identity-compactification-system-mate vs lem-sf-package-compactified-tower-comparisons: the latter identifies proper towers and completed exchange on the constructible domain, but does not state the actual identity-open system unit/counit normalization or the displayed equality involving e_a^c before inverse limit. The tower clause is reused context for this stronger pre-limit normalization, not a second tower-identification node.

lem-pod-identity-compactification-system-mate vs cor-cbc-proper-coincidence: the existing pro-etale clause only gives the finite comparison isomorphism; its exchange equation is stated for bounded-below etale coefficients. The new node specifies the pro-etale open/system mate and its equality before total inverse limit.

lem-pod-identity-compactification-system-mate vs lem-sf-semilinear-proper-open-mate-pasting: that lemma concerns proper/open interchange for refinement squares and its pasting, not normalization of the identity compactification's Frobenius system exchange using F_a(u).

lem-pod-identity-compactification-limit-comparisons vs lem-sf-package-compactified-tower-comparisons: this child fixes alpha_!, beta_!, alpha_*, beta_* of the Frobenius definition individually, with the named h_S, h_T, and the pullback of kappa in their two equations. Agreement of the final exchange or of the output towers does not by itself assert these two specified comparison equations.

lem-pod-identity-compactification-limit-comparisons vs lem-sf-integral-basic-realization: the existing statement constructs primitive/compactification realization maps and whole transition towers; the child is their identity-open normalization with the specific pulled source and target alpha/beta maps of the Frobenius definition.

lem-pod-identity-compactification-limit-comparisons vs lem-sf-integral-expression-recursion: the recursion supplies comparisons under its primitive identities; the child concerns the specified identity-open comparisons of the Frobenius definition itself. No equation about these alpha/beta morphisms is given by that node's statement.

lem-pod-identity-compactification-limit-comparisons vs lem-pur-isomorphism-strict-integral-exchange-normalization: the existing node identifies reindexing for the completed-exchange construction and its H/H' maps. The child specifies the alpha/beta morphisms of the different explicitly semilinear-system Frobenius definition and the identity compactification's comparison. No identification of the two constructions is assumed silently.

Both children vs lem-pod-proper-coincidence-frobenius: neither states its all-coefficient exchange-and-point-transport conclusion. The first controls actual pre-limit system maps; the second controls only the surrounding comparison maps. The item must combine them, localize/descend, and apply point naturality and cohomology.

## Review by Q41

I read the ancestor's master blueprint Step 6 and its surrounding Steps 1–7, and the corresponding main-20261015 statement (the newer file retains the proper Frobenius-equivariance assertion without that proof expansion). I also read Deligne Weil I (1.3), printed p. 274, which explicitly asserts coincidence for proper schemes. Deligne does not supply the detailed semilinear normalization; that is correctly recorded as an agent expansion in the child sources and the item's proof_origin. For each new node I checked the construction against the full statements of def-weil-frobenius-square-exchange, lem-coef-semilinear-derived-sections, def-weil-derived-direct-image, def-weil-integral-rational-qbar-compact-support and def-weil-extension-by-zero, plus the normalized open exchange and restriction-of-scalars statements. These are locally available sources for the actual operations, not an appeal to an unspecified six-functor formalism.

Step 1 cites the system-mate child's finite assertion and the exchange definition. The former supplies the actual canonical open cancellation and the normalized finite exchange; the latter really gives the two-arrow formula. The proper identity compactification in the statement is the one used in both. The child finite statement permits its pro-etale domain; I did not use the etale-only exchange clause of cor-cbc-proper-coincidence as a pro-etale theorem.

Step 2 cites the system-mate equality with all transitions, the limit-comparisons child's two exact equations, and the exchange definition. With composition read right to left, L(h_S) alpha_! = alpha_* G(kappa) and kappa' beta_! = beta_* L(h_T) have the required types. Functoriality of L then yields the displayed equality, without a faithfulness assumption on evaluation. The hypotheses are integral bounded constructible input, proper a, the same identity compactification at every level, and Frobenius scheme isomorphisms; all are present. Scalar localization is applied only after the integral equality, and the algebraic-closure case uses a common finite extension stage, not reduction of a rational object.

Step 3 cites exactly clause 2 of lem-weil-frobenius-point-transport-natural, which is natural for every morphism in the bounded constructible point category at all four coefficient stages, including common-stage scalar compatibility. Its morphism is kappa_M, not an unmentioned Weil structure on M. The statement already supplies the proper outputs on this domain. I read def-weil-finite-coefficient-point for the functor F, and def-weil-frobenius-cohomology-transport for both composites. The only remaining operations are functorial composition and substitution of step 2, written explicitly. Step 4 cites the cohomology definition for the meanings of H^i and H_c^i; preservation of composition gives the result for all i. Every use has a literal statement quotation in citations.json.

I checked B–E individually: new nodes are self-contained statement-only JSON, every operation has its defining node or an explicit description, all inherited blueprint/import fields are preserved, and proof_deps is exactly the union of step uses. No extra hypothesis on M, smoothness, geometric connectedness, finite flatness of coefficient quotients, k-linearity of Frobenius, or evaluation faithfulness has entered. Testing Y empty, Y=Spec k, M=0, n=1 and negative degrees gives the same identities; the system statement also permits non-flat quotient transitions. Both new arguments have independent inputs and conclusions, and neither depends on the parent. The finite and point calculations remain elementary because the new statements/the existing naturality theorem supply their substantive assertions. No item step exceeds 2000 characters. The two children are comparable in scope and size and do not hide their arguments as proof steps inside a statement.

## Unfinished work

No part of the requested stage-1 repair is intentionally omitted. The two child proofs are deliberately deferred as statement-only unsplit nodes under the human's spreading-work order. No Lean work is authorized.

## Original proof retained verbatim

Original step 1:

*Step 1 (finite coefficients).* Use the identity compactification fixed in the statement. By [def-weil-extension-by-zero], for $j=\operatorname{id}_Y$ every object factors through $j$, so $P_M=M$ and $j_!M=M$, on objects and morphisms. Thus [def-compact-support-direct-image-detailed] gives $Ra_{Y!,n}=Ra_{Y*,n}$; the proper comparison $\kappa$ of [prop-weil-proper-compact-coincidence] is this identification. In [lem-trf-open-square-exchange] put $U'=Y'=U=Y$ and $j'=j=\operatorname{id}_Y$. Its restriction-to-$U'$ clause now says that the entire open-square map $b_{g_Y}$ is the identity under the pullback identifications. Consequently the two arrows defining $\operatorname{FrEx}_{Y,!}$ in [def-weil-frobenius-square-exchange] (2) are $\operatorname{FrEx}_{Y,*}(M)$ followed by $Ra_{Y*}(\operatorname{id})$. This proves clause 1 at $\Lambda=A_{E,n}$, including the specified identifications $Lg_s^*\kappa_M$ on the source and $\kappa_{Lg_Y^*M}$ on the target.

Original step 2:

*Step 2 (integral and field coefficients).* Use the same identity compactification at every level. The formulas in [def-weil-derived-direct-image] and [def-weil-integral-rational-qbar-compact-support] give the same strict coefficient tower for $Ra_{Y!}M$ and $Ra_{Y*}M$: at level $m$ both are $\operatorname{Res}_mRa_{Y*,m}(M\otimes^L A_{E,m})$, with the same quotient-induced transitions. Indeed, [lem-sf-compact-support-restriction-of-scalars] specifies the compact-support restriction comparison as the direct-image restriction comparison composed with $j_!\operatorname{Res}=\operatorname{Res}j_!$; for $j=\operatorname{id}$ the latter identification is the identity. On the simultaneous section models of [lem-coef-semilinear-derived-sections], extension by zero along the identity is the identity functor, with identity adjunction unit and counit. Its open-adjunction mate $b$ is therefore the identity system map. In the notation of [def-weil-frobenius-square-exchange], $\mathcal J_{\operatorname{id}}=\operatorname{id}$, $p=a_Y$, and $e_{a_Y}^{c}=\mathcal F_{a_Y}(\operatorname{id})\circ e_{a_Y}=e_{a_Y}$ as system maps. Under $\kappa$, the canonical comparisons $\alpha_!,\beta_!$ in that definition are $\alpha_*,\beta_*$: their source and target system operations and their defining units and counits coincide. Thus the two integral exchange composites are the same $\beta_*\circ\mathcal L_s(e_{a_Y})\circ\alpha_*$, proving clause 1 for $\mathcal O_E$. Applying the scalar-localization functor to this equality proves it for $E$; representing an object and these equal morphisms at a common finite field stage proves it for $\Qlb$, exactly as prescribed in [def-weil-frobenius-square-exchange]. This uses equality of specified system maps before $R\varprojlim$, rather than inferring equality from their finite evaluations.

Original step 3:

*Step 3 (point complexes).* Write $F=\operatorname{Fib}_s$, $G=Lg_s^*$, $N_!=Ra_{Y!}M$, $N_*=Ra_{Y*}M$, and $M'=Lg_Y^*M$. Naturality of the point transport [lem-weil-frobenius-point-transport-natural] (2), applied to $\kappa_M:N_!\to N_*$, says $\iota_{N_*}\circ F(\kappa_M)=F(G\kappa_M)\circ\iota_{N_!}$. Clause 1 and functoriality of $F$ [def-weil-finite-coefficient-point] now give
$$
\begin{aligned}
\tau_M\circ F(\kappa_M)
&=F(\operatorname{FrEx}_{Y,*}(M))\circ\iota_{N_*}\circ F(\kappa_M)\\
&=F(\operatorname{FrEx}_{Y,*}(M))\circ F(G\kappa_M)\circ\iota_{N_!}\\
&=F(\kappa_{M'})\circ F(\operatorname{FrEx}_{Y,!}(M))\circ\iota_{N_!}\\
&=F(\kappa_{M'})\circ\tau_{c,M}.
\end{aligned}
$$
The first and last equalities are the two transport composites of [def-weil-frobenius-cohomology-transport]. Their source and target are the cohomology complexes of [def-weil-ordinary-compact-cohomology]. This is clause 2 at the complex level.

Original step 4:

*Step 4 (cohomology).* Applying $\mathrm H^i$ to the point-complex equality of Step 3 gives, for every integer $i$, $\mathrm H^i(\tau_M)\circ\mathrm H^i(\operatorname{Fib}_s\kappa_M)=\mathrm H^i(\operatorname{Fib}_s\kappa_{Lg_Y^*M})\circ\mathrm H^i(\tau_{c,M})$ on $H_c^i(Y,M)$, using the definitions of ordinary and compact-support cohomology in [def-weil-ordinary-compact-cohomology] and preservation of composition by the cohomology functor.
