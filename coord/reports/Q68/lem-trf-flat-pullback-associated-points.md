# Repair of lem-trf-flat-pullback-associated-points

1. Files written: the item JSON (statement unchanged; three assembly steps); lem-trf-flat-association-stalk-dictionary.json (statement, unsplit, no Mathlib match); lem-trf-flat-local-maximal-associated-tensor.json (statement, unsplit, no Mathlib match). Both new files are in dag/nodes/sec-trace-formula/. citations.json records a verbatim statement quote for every assembly citation. Searches are retained in searches.jsonl.
2. Attachments: none. The project declaration associatedPoints_tensorPullback_of_flat in Sheaf/AlgebraicGeometry/FlatPullbackAssociatedPoints.lean still ends in sorry. Searching the whole WeilConjectures tree by the item tag and declaration name found no attachment. TensorPullbackStalk and AnnihilatorAssociatedPrimesFlatBaseChange supply existing ingredients, not the item.
3. WANTED: none.
4. The return required spreading a 4340-character proof over at least two new tasks, not a shorter paraphrase. The sandbox initially contained only .brief markers, not the asserted retained files; the required first dry run failed with no node files. I copied the returned proof from the shared read clone. Its statement and all non-stage-1 fields are retained. The new nodes carry the two parts of the argument separately. Neither assumes finite generation of M or Noetherianity of B. The dictionary makes no assertion that pullback association is the conjunction of base and fibre association; that assertion is obtained only by applying the separate algebra criterion.
5. Nothing unfinished in the split. The two new nodes intentionally have empty proof/proof_deps and null proof_origin so that two workers can prove them independently. No Lean files were changed and no compiler was run.

## Return repair and allocation of the complete old argument

The parent proof now has 1950 characters, below 3000. The geometric task carries old steps 1, 2 and 5 (1958 characters); the algebra task carries old steps 3 and 4 (1488 characters) and the two algebraic implications in old step 6. The remainder of step 6 is the parent's elementary pointwise-to-union assembly. These are comparable tasks, with no new node stating the entire parent or one direction of its geometric union formula. Here is the returned argument verbatim, retained as proof guidance rather than hidden in the statement-only nodes:

### Old step 1: lem-trf-flat-association-stalk-dictionary

Fix $y\in Y$ and put $z=h(y)$, $A=\mathcal O_{Z,z}$, $B=\mathcal O_{Y,y}$, $M=\mathcal G_z$, with maximal ideals $\mathfrak m_A,\mathfrak m_B$. The stalk homomorphism $\varphi:A\to B$ is local and $B$ is flat over $A$ by [def-weil-flat-morphism]. Choose a Noetherian affine neighbourhood of $z$ from [pqf-def-locnoeth]. By [lem-weil-pbc-affine-open-stalk-localization](c), $A$ is a prime localization of its coordinate ring; [lem-weil-pbc-localization-noetherian] makes $A$ Noetherian. No assertion about Noetherianity of $B$ or finiteness of $M$ has been made.

Cited ingredients retained as guidance: def-weil-flat-morphism, pqf-def-locnoeth, lem-weil-pbc-affine-open-stalk-localization, lem-weil-pbc-localization-noetherian.

### Old step 2: lem-trf-flat-association-stalk-dictionary

By [lem-weil-pbc-module-stalk-pullback], $(h^*\mathcal G)_y\cong M\otimes_A B$ as $B$-modules. An isomorphism preserves the annihilator of each element, so [def-trf-relative-assassin] identifies $y\in\operatorname{Ass}_Y(h^*\mathcal G)$ with $\mathfrak m_B\in\operatorname{Ass}_B(M\otimes_A B)$, always using exact element-annihilators. By [lem-sbc-scheme-fibre-stalk-quotient], the unique point $y_z$ of $Y_z$ above $y$ has local ring $C=B/\mathfrak m_A B$, compatibly with the quotient map. Since $\varphi$ is local, $\mathfrak m_A B\subseteq\mathfrak m_B$, and the maximal ideal of $C$ is $\mathfrak m_B/\mathfrak m_A B$. Thus the fibre association condition is that this ideal is the annihilator of an element of $C$.

Cited ingredients retained as guidance: lem-weil-pbc-module-stalk-pullback, def-trf-relative-assassin, lem-sbc-scheme-fibre-stalk-quotient.

### Old step 3: lem-trf-flat-local-maximal-associated-tensor

Apply the equality clause of [lem-weil-pbc-associated-primes-flat-base-change] with $R=A$, $S=B$, and $N=B$. Step 1 verifies both hypotheses, and its statement allows arbitrary $M$ and arbitrary $B$. Hence
$$\mathfrak m_B\in\operatorname{Ass}_B(M\otimes_A B)\quad\Longleftrightarrow\quad
\text{there is }\mathfrak p\in\operatorname{Ass}_A(M)\text{ with }\mathfrak m_B\in\operatorname{Ass}_B(B/\mathfrak pB).$$
We next identify which $\mathfrak p$ can occur, rather than assuming it equals $\mathfrak m_A$.

Cited ingredients retained as guidance: lem-weil-pbc-associated-primes-flat-base-change.

### Old step 4: lem-trf-flat-local-maximal-associated-tensor

Suppose $\mathfrak m_B=\operatorname{Ann}_B(v)$ for $v\in B/\mathfrak pB$, where $\mathfrak p$ is prime in $A$. The element $v$ is nonzero because $\mathfrak m_B$ is proper. For $a\notin\mathfrak p$, multiplication by $a$ on $A/\mathfrak p$ is injective: $ar\in\mathfrak p$ implies $r\in\mathfrak p$. By [lem-weil-pbc-flat-tensor-exact], tensoring this injection with the $A$-flat module $B$ stays injective. The isomorphism [lem-weil-pbc-tensor-over-quotient-ring](1) identifies the tensor module with $B/\mathfrak pB$ by $\bar r\otimes b\mapsto\varphi(r)b$; on these generators the tensor map is multiplication by $\varphi(a)$. Consequently $\varphi(a)$ cannot annihilate $v$. If $a\in\mathfrak m_A\setminus\mathfrak p$, locality gives $\varphi(a)\in\mathfrak m_B$, contradicting this conclusion. Hence $\mathfrak m_A\subseteq\mathfrak p$. Every proper ideal of the local ring $A$ is contained in $\mathfrak m_A$ (each element outside it is a unit), so $\mathfrak p=\mathfrak m_A$.

Cited ingredients retained as guidance: lem-weil-pbc-flat-tensor-exact, lem-weil-pbc-tensor-over-quotient-ring.

### Old step 5: lem-trf-flat-association-stalk-dictionary

For $C=B/\mathfrak m_A B$ and $v\in C$, the $B$-annihilator is the inverse image of the $C$-annihilator under the surjection $B\to C$. Therefore
$$\operatorname{Ann}_B(v)=\mathfrak m_B\quad\Longleftrightarrow\quad
\operatorname{Ann}_C(v)=\mathfrak m_B/\mathfrak m_A B.$$
Indeed the preimage of the displayed quotient ideal is $\mathfrak m_B$, and surjectivity makes ideals of $C$ equal when their preimages are equal. By the definition [def-trf-relative-assassin] and step 2, this proves
$$\mathfrak m_B\in\operatorname{Ass}_B(B/\mathfrak m_A B)
\quad\Longleftrightarrow\quad y_z\in\operatorname{Ass}_{Y_z}(\mathcal O_{Y_z}).$$
It holds even if $B$ and $C$ are non-Noetherian.

Cited ingredients retained as guidance: def-trf-relative-assassin.

### Old step 6: lem-trf-flat-local-maximal-associated-tensor (two algebraic implications); parent step 3 (set assembly)

Steps 3–5 give the equivalence
$$\mathfrak m_B\in\operatorname{Ass}_B(M\otimes_A B)\quad\Longleftrightarrow\quad
\bigl(\mathfrak m_A\in\operatorname{Ass}_A(M)\text{ and }y_z\in\operatorname{Ass}_{Y_z}(\mathcal O_{Y_z})\bigr).$$
For the forward implication choose $\mathfrak p$ in step 3, identify it by step 4, and apply step 5. For the reverse implication use step 5 and take $\mathfrak p=\mathfrak m_A$ in step 3. By [def-trf-relative-assassin], the first condition on the right is exactly $z\in\operatorname{Ass}_Z(\mathcal G)$. Step 2 identifies the left condition with association of $y$ to $h^*\mathcal G$. Finally [def-pc-scheme-fibre] says $j_z$ identifies the points of $Y_z$ with $h^{-1}(z)$. Thus a fixed $y$ lies in the union in the statement precisely when these two right-hand conditions hold for $z=h(y)$. Since this holds for every $y$, the required equality of subsets follows.

Cited ingredients retained as guidance: def-trf-relative-assassin, def-pc-scheme-fibre.

## Not duplicates

lem-trf-flat-association-stalk-dictionary vs lem-trf-flat-pullback-associated-points: the new statement supplies stalk models and three separate association translations; it does not identify pullback association with the conjunction of base and fibre association or assert the union equality.

lem-trf-flat-association-stalk-dictionary vs lem-trf-fibre-associated-primes-module-ring: the existing lemma compares ring-module associated primes after passage to a fibre ring; it gives neither geometric pullback stalks nor Noetherian stalks nor the geometric associated-point translations.

lem-trf-flat-association-stalk-dictionary vs lem-sbc-composite-fibre-local-models: the existing lemma assumes two locally finite type morphisms and studies three fibre local rings, not arbitrary flat h with arbitrary quasi-coherent G or associated-point translations.

lem-trf-flat-association-stalk-dictionary vs lem-sbc-scheme-fibre-stalk-quotient: the existing lemma supplies only the quotient description of the fibre stalk, not pullback module stalks, base Noetherianity and all association translations.

lem-trf-flat-local-maximal-associated-tensor vs lem-trf-associated-primes-fibre-bound: the existing lemma assumes both rings Noetherian and both coefficient modules finite and gives only fibre association of a chosen associated prime. The new criterion allows non-Noetherian B and arbitrary M and gives both implications at maximal ideals.

lem-trf-flat-local-maximal-associated-tensor vs lem-weil-pbc-associated-primes-flat-base-change: the existing general Bourbaki formula ranges over all associated primes p of A and gives Ass_B(B/pB); the new local criterion must further prove that the possible p is m_A by the nonzerodivisor and locality argument. It is not a one-line specialization.

lem-trf-flat-local-maximal-associated-tensor vs lem-weil-pbc-associated-primes-flat-quotient: the existing statement requires Noetherian B, restricts coefficients to A/I, and gives a one-way union membership, without identifying the auxiliary prime with m_A.

lem-trf-flat-local-maximal-associated-tensor vs lem-sbc-power-series-punctured-germ-detection: the existing lemma detects sections on a punctured power-series scheme using a depth hypothesis, not maximal associated primes of arbitrary flat local tensors.

lem-trf-flat-local-maximal-associated-tensor vs lem-sbc-power-series-prime-extension: the existing statement is primality of extended ideals in a power-series ring, not a maximal-associated tensor criterion.

## Review by Q68

I read Divisors Tag 05DB, label lemma-bourbaki, including its proof identifying the three association predicates and invoking Algebra 05C2. For the dictionary I also read Schemes 0HA1, label lemma-local-ring-fibre, and Algebra 05BY, label lemma-ass-quotient-ring. The latter omits its proof; old step 5 above supplies the full inverse-image-of-annihilator argument. For the algebra task I read 05C2, label lemma-bourbaki-fibres, its inputs 0312, label lemma-bourbaki, and 05C1, label lemma-post-bourbaki. The calculation in old step 4 explicitly supplies the prime-rigidity argument rather than claiming that Bourbaki already sets p=m_A.

For parent step 1 I checked the entire dictionary statement: it explicitly supplies the flat local stalk map and Noetherian A, tensor stalk, fibre quotient and each of the three association translations. The hypotheses on h,Z,G are exactly those already in the parent. For step 2 I checked the local algebra criterion statement: it has arbitrary M and arbitrary local B, with only A Noetherian, and gives precisely the displayed equivalence with the B-associated prime of C. Stalks at scheme points are nonzero local rings, so its local-ring hypotheses hold. Substitution uses the dictionary already established in step 1. For step 3 I read def-pc-scheme-fibre: its last sentence really states the homeomorphism onto h^{-1}(t). Thus the union has only the index t=h(y), and injectivity supplies its unique point. No association theorem is being taken from a definition. citations.json quotes the actual statement used by each step.

I also reopened the statements of every ingredient of the retained old proof: flat morphism, locally Noetherian scheme, affine-open stalk localization and Noetherian localization; module stalk pullback and fibre stalk quotient; arbitrary-module Bourbaki, flat tensor exactness and quotient-tensor isomorphism; associated points and scheme fibres. Each says what the retained guidance uses. In particular the quotient-tensor map sends r-bar tensor b to phi(r)b, so multiplication by a really becomes multiplication by phi(a); flatness preserves its injectivity. This forces p=m_A without a Noetherian hypothesis on B. The dictionary's quotient-annihilator comparison uses surjectivity, not a false identification of B with C.

Small cases checked: M=0 makes both sides of the algebra equivalence false; A=B a field gives the expected criterion M nonzero; the identity A=B reduces the closed fibre to the residue field, whose zero maximal ideal is an exact annihilator of 1. For A a field and B any non-Noetherian local algebra, a nonzero M is free and the tensor has an associated maximal ideal exactly when B does. For an empty scheme the parent equality is vacuous, and the dictionary only quantifies over an existing point. Locality ensures m_A B is contained in the proper ideal m_B, so the quotient C used in the dictionary is nonzero. No finite-type condition or source Noetherianity was silently introduced.

I checked delivery-errors B--E against the JSON and sources. The two new statements introduce all objects and cite the existing definitions; they contain no proof sketch, proof steps or proof dependencies. The new nodes represent geometry and local algebra arguments, not the parent equality renamed. Whole-DAG tag and keyword searches and blueprint_refs searches for associated points, Bourbaki, 05DB, 05C2, flat local, maximal ideal and stalk/annihilator yielded no existing node with either full statement. The same-tag nodes are distinguished above. Mathlib searches used msearch.py only; all logged query text is copied unchanged. Localization of associated primes, open-immersion stalk restriction, flatness and Noetherian stalk instances cover ingredients but not these statements. Loogle patterns rejected as unknown identifiers are explicitly marked unavailable. The current blueprint ancestor and the chapter/unit route are unchanged. No parent assembly step exceeds 2000 characters. There was no statement dispute or correction.


## Current-DAG landing repair, 2026-10-22

The returned delivery was approved mathematically, but its landing failed because the side completion had not been promoted to the live queue's DAG. I ran the mandatory first dry run before editing: it rebased the retained delivery through the delivery tool's worktree and passed server preflight at c6e567eaddf. This receipt is a dry-run head, not a claim of delivery. The active released stage-1 repair note still requires the two-node re-split, so the old reviewed six-step proof does not supersede this work.

I compared all three sandbox node files with the current shared read clone. Both helper nodes are absent there. The parent differs only in proof, proof_deps and split_report; its statement, statement dependencies, Lean records, reviews, blueprint ancestry and approved tool-use metadata are identical. I retained all earlier source citations, full old argument, search queries and logged results. The final delivery tool supplies the fresh base against the server rather than any worker git operation in the read-only clone.

I reopened every current statement cited by the assembly and the retained proof guidance. In particular, def-pc-scheme-fibre still explicitly identifies the fibre space with the inverse image of its base point. The stalk dictionary and local algebra criterion retain exactly the statements quoted in citations.json. I made the dictionary an explicit citation in assembly step 2 as well as step 1, since step 2 substitutes its three association equivalences, and added the corresponding verbatim citation. This is the split adjustment accompanying the rebase; it changes no mathematical hypothesis or conclusion.

## Review by Q68 — current-DAG repair

I checked the three assembly steps again against their actual current cited statements. Step 1 uses the dictionary's flat local stalk map, Noetherian base stalk, tensor stalk, quotient fibre stalk and three annihilator translations. Step 2 uses precisely the local tensor criterion's equivalence and the dictionary's translations; nonzero local stalk rings, locality, flatness and Noetherian A meet every hypothesis. Neither citation requires finite generation of G or M, nor Noetherianity of Y or B. Step 3 uses the final sentence of the current scheme-fibre definition to identify the only possible union index z=h(y) and the unique fibre point. This final step is elementary set membership and extensionality.

I read Divisors 05DB (lemma-bourbaki) and its proof again, together with Schemes 0HA1 (lemma-local-ring-fibre) and Algebra 05BY (lemma-ass-quotient-ring), 0312 (lemma-bourbaki), 05C1 (lemma-post-bourbaki) and 05C2 (lemma-bourbaki-fibres). They validate respectively the geometric dictionary and the local algebra task. The old prime-rigidity argument remains intact in this report: multiplication by a outside p is injective on A/p, stays injective after flat tensoring, and locality rules out a in m_A outside p. Thus p=m_A, with no finiteness assumption on B. The current Bourbaki, flat-tensor-exact and tensor-over-quotient-ring nodes explicitly supply the formula, preservation of injections and generator formula used in that guidance. Current module-stalk-pullback and fibre-stalk-quotient explicitly supply the geometric isomorphisms. Current annihilator-associated-primes and relative-assassin definitions use exact element annihilators, not weak association.

I reread the retained searches.jsonl results instead of repeating unchanged search questions, and reopened the localization and open-immersion restriction candidates in Mathlib. The former require localization and the latter require an open immersion, so neither covers a general flat morphism. Whole-blueprint and current DAG tag searches were repeated to check for new duplicates; the existing same-tag statements remain distinguished in Not duplicates above. The project theorem still has sorry, so it is not an attachment. The zero module, field base, identity map and empty-scheme checks still hold; properness of m_B ensures the fibre quotient is nonzero. All helper statements remain statement-only, every assembly citation has a verbatim quote, and the assembly remains below 3000 characters with no step over 2000. This repairs the landing return by refreshing the base and checking the actual current dependencies, while retaining the previously approved argument and its required allocation.


## Latest landing-return repair, 2026-10-22

The required first dry run of this retry completed successfully at 41c32cc9fb0 before any edit. The retained sandbox already contained the approved two-helper split and earlier repair notes; I continued those files rather than recreating the argument or search records. Against the current shared DAG, the helper ids are still absent, and the parent differs only in proof, proof_deps and split_report. The live parent still has the released stage-1 re-split order requiring these two new tasks despite its historical reviewed marker. Delivery is built on the current server DAG by deliver.py; no worker git operation was used.

I reopened every current assembly citation and the definition dependencies of both helpers, and also every current lemma cited in the retained six-step argument. All statements still supply their required inputs: in particular Bourbaki permits arbitrary M and non-Noetherian B, the quotient-tensor formula identifies multiplication on generators, and the scheme-fibre statement gives a homeomorphism onto the entire inverse-image subspace. I retained the helper statements and the explicit dictionary citation in step 2. To make the final assembly precise after this rebase, I rewrote step 3 with actual witnesses in both directions: y=j_t(v) forces t=h(y) and v=y_z; conversely the witness y_z gives membership through j_z(y_z)=y. Its citation remains the current def-pc-scheme-fibre and the existing quote is verbatim. This is a proof adjustment accompanying the refreshed delivery, not an unchanged re-push.

I read 05DB in divisors.tex, 0HA1 in schemes.tex, and 05BY, 0312, 05C1 and 05C2 in algebra.tex again. The geometric helper asserts only separate stalk translations, and the algebra helper proves the maximal-associated tensor criterion; neither is the geometric union equality. I reread all 15 logged searches and their recorded outcomes, including the unavailable Loogle patterns, and the localization candidate source. Since neither statement nor search question changed, the prior queries and results are retained exactly. The current project theorem in FlatPullbackAssociatedPoints.lean still ends in sorry, and the WeilConjectures tag/name search yields no attachment.

The small cases remain valid: zero M, field A, identity A=B, arbitrary non-Noetherian local B over a field, and empty Y. Locality gives m_A B contained in the proper ideal m_B, so the fibre quotient is nonzero. Source and node statements require no finite generation of M and no Noetherianity of B. I checked the whole-DAG same-tag candidates and the blueprint ancestor/search results again; the existing Not duplicates explanations still distinguish all same-source candidates. Every helper remains statement-only, all assembly citations are covered by verbatim quotes, no proof step exceeds 2000 characters, and the complete assembly has 1663 characters. The final dry run and push below use this adjusted proof and updated report.


## Landing-return repair, 2026-10-23

The first dry run of this retry passed at ff50c379740 before edits. I compared the retained three node files with the current shared DAG: the helper ids remain absent, and the only differing parent fields are proof, proof_deps and split_report. Its statement, stmt_deps, Lean records, blueprint ancestry and historical reviews are unchanged. The released repair note still explicitly requires two comparable statement-only tasks. I retained both tasks, the complete six-step old argument above, the existing citations, and all 15 logged helper searches and outcomes. The delivery tool fetches origin/sheaf-dag and constructs the new delivery on that base; I ran no git command in the read clone. The return identifies live-queue promotion as L's operation; acceptance of this refreshed delivery still needs that maintainer promotion, which a worker cannot perform by editing the live DAG.

I adjusted assembly step 2 to spell out both implications. Forward: dictionary (2) sends pullback association to the tensor-associated maximal ideal; the local criterion gives base-module and quotient-module association; dictionary (2)--(3) translates these separately to the base and fibre points. Reverse: the same dictionary sends base and fibre association to the two algebraic conditions, and the reverse criterion followed by dictionary (2) returns pullback association. This does not add a new claim or hypothesis. The current assembly is 1950 characters, with step lengths 513, 926, 511; no long step hides another lemma.

## Review by Q68 — 2026-10-23 landing repair

I reopened Divisors 05DB, lemma-bourbaki, including the entire stalkwise proof, and checked its specialization F=O_Y with arbitrary quasi-coherent G and locally Noetherian Z. For the dictionary I read Schemes 0HA1, lemma-local-ring-fibre, and Algebra 05BY, lemma-ass-quotient-ring; the latter's omitted proof is supplied by the retained inverse-image-of-annihilators calculation in old step 5. For the algebra helper I read 0312, lemma-bourbaki, 05C1, lemma-post-bourbaki, and 05C2, lemma-bourbaki-fibres. They permit arbitrary M and non-Noetherian B. The prime-rigidity calculation in old step 4 is still required: flatness carries injective multiplication on A/p to B/pB, while locality excludes an element of m_A outside p. Nothing in the source supplies p=m_A without this argument.

I read the actual current statements of every assembly citation and of all ten dictionary definition dependencies and four algebra definition dependencies. Step 1 takes precisely the dictionary's flat local map, Noetherian base stalk, tensor and quotient identifications and three association equivalences. Step 2 now explicitly applies the two directions of the criterion and dictionary; stalk rings at existing scheme points are nonzero local rings, the dictionary gives Noetherian A and flat B, and M remains arbitrary. Step 3 takes only the homeomorphism onto h^(-1)(t) from the final sentence of def-pc-scheme-fibre, then identifies the union witness t=h(y) and the unique fibre point. I checked every citations.json quote against those current statements; all four citation pairs have verbatim quotes and cover the exact facts used.

I also reread the current ingredient statements retained as guidance: affine-open stalk localization (c), localization-Noetherian, module-stalk-pullback, fibre-stalk-quotient, Bourbaki's equality, flat-tensor-exact and tensor-over-quotient-ring (1). The tensor isomorphism's generator formula still identifies tensor multiplication with multiplication by phi(a); the fibre quotient still uses the stalk map's kernel, not an identification of B with C. The current project theorem still ends in sorry. Whole-WeilConjectures concept/tag searches found no finished attachment. Whole-DAG source-tag searches and blueprint searches for associated points, Bourbaki and 05DB revealed no replacement for either helper; I reopened the same-tag candidates distinguished in Not duplicates. The existing search questions did not change, so I read and retained their logged results instead of rerunning them.

For delivery-errors B--E I checked self-contained hypotheses and inline annihilator/extended-ideal definitions, statement-only helpers with no proof sketch, exact source tags and labels, unchanged blueprint ancestry, no duplicate or parent-clause helper, and that every non-elementary assembly input has its own citation. The small cases remain M=0, identity A=B, field A with arbitrary local B, and empty Y. In the field case a nonzero M is free and the same associated maximal ideal criterion is obtained; for M=0 both algebraic sides are false. Locality gives m_A B contained in the proper ideal m_B, so the quotient C is nonzero. No finite generation of M or Noetherianity of B was introduced. No statement dispute arose. The final dry run and push will package this adjusted proof and report on the current delivery base.
