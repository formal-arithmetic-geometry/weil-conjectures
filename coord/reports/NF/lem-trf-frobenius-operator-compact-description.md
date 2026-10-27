# Repair delivery: lem-trf-frobenius-operator-compact-description

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-frobenius-operator-compact-description.json`: unchanged statement; four-step assembly, 2599 characters (previously five steps, 4444 characters).
- `dag/nodes/sec-trace-formula/lem-trf-compact-direct-power-transport-normalization.json`: statement, unsplit; no Mathlib match. Direct transport is defined and invertible on bounded constructible finite coefficients, and equals repeated transport under the specified comparisons.
- `dag/nodes/sec-trace-formula/lem-trf-compact-weil-cocycle-endomorphism-recurrence.json`: statement, unsplit; no Mathlib match. The actual Weil cocycle and direct compact-support transport yield a recurrence of derived endomorphisms.
- `citations.json`, `report.md`, and actual `searches.jsonl`; `returned-proof.json` preserves the complete original proof as read from the shared DAG. The small repair scripts are sandbox-only bookkeeping and do not enter the delivery.

## Attachments

None. I searched `lean/WeilConjectures/` for the blueprint id, the notion, compact Frobenius and its iterates. `CompactWeilDatum.lean` defines `AlgebraicGeometry.ProEtale.compactFrobenius`, and `ExtendScalars/StrictWeilComplexFrobenius.lean` defines `AlgebraicGeometry.ProEtale.StrictWeilComplex.globalFrobenius`; neither proves that the retained operator is its positive iterate with the specified point transport. They use a compactification over the identity on the base, whereas the retained definition uses the semilinear point Frobenius and its point-fiber transport. The exact theorem in `lean/Sheaf/Paper/FrobeniusOperatorCompactDescription.lean` ends with `sorry`. There is no attachment.

## WANTED

None. The main-20261015 statement and companion `.proof.md`, old master proof, the live DAG statements and the relevant source docstrings are present. Deligne's Weil II PDF is present and I read printed pp. 151-153, (1.1.7) and (1.1.10)-(1.1.14), for the geometric-Frobenius and transport-of-structure conventions. The detailed finite-coefficient comparison and recurrence arguments remain explicitly agent-written expansions of the blueprint, rather than claims that Deligne supplies these exact derived formulas.

## What was wrong and what changed

The 2026-10-22 return requires work to be distributed into at least two comparable statement-only nodes. It does not identify a mathematical error in the retained statement. The sandbox initially contained only the brief markers, with no node, report or search log; I therefore copied the current shared DAG version, whose proof has exactly the returned lengths 992, 637, 765, 1139, 911. There was no interrupted sandbox proof or logged search to discard. No git commands were run by the worker. Delivery tooling rebases the owned fields over current server main and preserves maintainer metadata, including the Lean declaration.

Old step 1 remains verbatim as parent step 1. Old steps 2 and 3 are assigned to the normalization node (1402 characters of original argument), whose statement includes the bounded-constructible domains, canonical d_r, equality with the direct power transport and invertibility. Old step 4 is assigned to the recurrence node (1139 characters of original argument), whose statement asserts the initial value and recurrence on the actual derived compact-support complex. Old step 5 remains as parent step 4, with only step references updated. The recurrence node does not assert the final power equality or identify repeated with direct transport. The normalization node has no Weil structure. Thus neither restates the whole item, and both can be worked on independently using existing inputs. The parent retains the final positive-integer induction and substitution. No previous argument was shortened into an unproved assertion in the parent's prose: the two extracted arguments are recorded in full below for their future workers.

The explicit re-split instruction calls for extracting these two arguments even though parts of them become short calculations once their non-elementary inputs are supplied. The new nodes package respectively a geometric domain/comparison application and a typed coefficient/transport recurrence, rather than isolated identity rewrites.

## What remains unfinished

Only proofs of the two new unsplit nodes, intentionally left for parallel stage-1 workers. Both have `proof: []`, `proof_deps: []`, `proof_origin: null`, sources, complete statements, precise blueprint ancestry and logged searches. No Lean was written and no compiler, Lake or build command was run.

## Not duplicates

Searches included the whole DAG for repeated/direct transport, powers, recurrence, and the exact source/id, and `tools/blueprint_refs.py ancestor` and `search` with `transport`, `compact-support base-change`, `iterated Weil`, `repeated`, `compactly supported cohomology`, `transport compact`, and `cocycle Frobenius` (including all chapters). No blueprint node states either new claim. No Stacks tag is invented for these particular Frobenius constructions; the source is the exact blueprint proof and its documented finite-coefficient expansion.

- lem-trf-compact-direct-power-transport-normalization vs lem-trf-compact-frobenius-transport-composition: the existing node defines the direct maps and their recurrence; it does not identify them with the repeated-transport expression using the actual d_r or assert this expression's domain and invertibility.
- lem-trf-compact-direct-power-transport-normalization vs lem-trf-frobenius-transport-induction: the existing node assumes all categorical comparison/coherence/domain inputs. The new node establishes its applicability to the retained geometric maps and includes invertibility on the finite constructible domain.
- lem-trf-compact-direct-power-transport-normalization vs lem-trf-frobenius-pullback-comparison-coherence: the existing node is coherence of derived pullbacks; it has no compact-support point transport or equality S_r=tau^(r).
- lem-trf-compact-direct-power-transport-normalization vs def-trf-frobenius-pullback-power-comparison: the existing node only defines the comparisons d_r and asserts no transport equality.
- lem-trf-compact-direct-power-transport-normalization vs lem-trf-integral-compact-transport-recurrence: the existing node is an integral coherent-tower realization theorem whose finite direct transports are inputs; it does not prove the new finite-level normalization/domain theorem.
- lem-trf-compact-weil-cocycle-endomorphism-recurrence vs lem-trf-iterated-weil-cocycle: the existing node is an identity between pullback coefficient maps. The new node concerns compact-support endomorphisms and needs the direct-transport composition and its naturality.
- lem-trf-compact-weil-cocycle-endomorphism-recurrence vs lem-trf-global-frobenius-iterate-formula: the existing abstract node uses strict iterates G^m and a repeated natural transformation. The new claim concerns the separately constructed direct transport along g^r and the canonical inverse pullback comparison b_r. Applying the abstract node would still require the geometric matching that the retained calculation supplies; the statement is not a one-line specialization.
- lem-trf-compact-weil-cocycle-endomorphism-recurrence vs lem-trf-rational-global-frobenius-powers: the existing node is over rationalized E-coefficients and requires the integral-model comparison interface; the new one is on the original finite coefficient complex, without changing coefficient categories.
- lem-trf-compact-weil-cocycle-endomorphism-recurrence vs lem-trf-frobenius-operator-compact-description: the new node gives a recurrence for direct composites, and leaves identification with the defined operator, the power induction and direct/repeated comparison to the parent and the other new node.
- lem-trf-compact-direct-power-transport-normalization vs lem-trf-frobenius-operator-compact-description: the new node has no coefficient Weil map or Frobenius endomorphism; it only treats the first arrow for arbitrary bounded constructible M.

## Mathlib search reading

Each new node has two distinct LeanFinder formulations, a Loogle pattern, a Mathlib grep through the required command, and a recorded LeanSearch attempt. The log is retained verbatim. LeanSearch returned rate-limit errors, recorded as unavailable. The first normalization query returned Witt isocrystals, and its second returned functorial group-cohomology cocycle/cochain comparison identities. Loogle returned categorical pullback cone isomorphisms and pullbackComparison, not composition of scheme inverse-image functors. The grep returned basic pro-etale site/ell-adic cohomology files and quasi-compact scheme pullback facts. I opened Mathlib's `AlgebraicGeometry/Sites/ElladicCohomology.lean`: it defines ordinary ell-adic cohomology, not the compact-support transports in this claim. The recurrence queries returned Witt/perfection/field Frobenius iterate identities and group-cohomology comparison identities; Loogle and the whole-Mathlib Frobenius/Weil-cocycle compact-support grep returned no hits. None states either new result or a one-line specialization with its specified geometric maps.

## Review by NF

I read the chapter `sec-trace-formula`, the unit `sk-d-weil`, both blueprint snapshots and the current companion proof file. The unit's route uses the same Weil data and geometric operator, and no chapter or unit route is changed. I compared the parent statement exactly with the current main blueprint and retained it byte for byte. The finite coefficient hypotheses are those of `def-trf-coefficient-conventions`: n>=1, ell different from p, X_0 separated and of finite type, and the chosen compactification over k_0. The semilinear g is used as a scheme automorphism, never assumed k-linear; it has base action h=Spec(gamma). A compactification c_0 already retained by the operator is fixed in parent step 1 and in both new statements, so no independence-of-compactification theorem or extra existence argument is smuggled in.

For parent step 1 I opened the complete statements of `def-trf-frobenius-operators`, `def-weil-frobenius-cohomology-transport`, `def-weil-frobenius-square-exchange` and `def-trf-coefficient-conventions`. The first explicitly says c_1=id and the first transport is tau_c; the second gives exactly point insertion followed by Fib_s of compact exchange; the third's part 2 and final paragraph specialize that exchange to a_X and the retained compactification; the last defines H as the point fiber of Ra_!. Thus the expansion uses these statements, not material hidden in their proofs. Its elementary label is appropriate for unfolding.

Parent step 2 cites the new normalization statement, whose final formulas explicitly give S_r=tau^(r) and invertibility for all bounded constructible M. The underlying complex of the given strict Weil object is in that domain. Parent step 3 cites the new recurrence statement, which explicitly introduces the same U_r and says U_1=H(phi)tau_c and U_(r+1)=U_1 U_r. Its finite datum and c_0 match step 1 and step 2; it does not assume the conclusion of the parent. Parent step 4 uses only the earlier recurrence plus clause 1 of `def-trf-frobenius-operators`, which is copied in full into its citation. I checked the base and successor of the positive-integer induction and the substitution of S_m=tau^(m). This proves equality in the derived coefficient category before cohomology. The only non-elementary parent steps are explicit applications of the two new nodes, both shorter than 2000 characters; total proof text is 2599 characters.

For the normalization node I read the sources identified in its source field: the main companion proof's scheme-variable transport sentence, the returned steps 2-3 reproduced below, and paragraphs 2-3 of the live Lean theorem's docstring. I also opened the full statements of `lem-trf-compact-frobenius-transport-composition`, `lem-trf-frobenius-pullback-comparison-coherence`, `lem-trf-frobenius-transport-induction`, `lem-weil-isomorphism-derived-pullback`, and `lem-weil-frobenius-cohomology-transport-iso`. The composition statement supplies exactly b_r and tau_(r+1)=H(b_r)tau_(1,P_r)tau_r; the comparison statement supplies d_1=id and d_(r+1)^(-1) T(d_r)=b_r; the induction node needs precisely these hypotheses and natural degree-one tau, which the transport definition explicitly gives. The isomorphism-pullback node applies because powers of g are scheme isomorphisms and ell is invertible on X. Clause 3 of the transport-isomorphism statement applies to each resulting bounded constructible object. These inputs prove the normalization and invertibility claimed. None requires finite Tor amplitude or a Weil map.

For the recurrence node I read the same main proof's coefficient-map sentence, returned step 4 reproduced below, paragraph 4 of the live theorem docstring, and the full statements of `def-trf-iterated-weil-map`, `lem-trf-iterated-weil-cocycle`, the compact-transport composition node and the transport definition. The cocycle at (1,r) gives phi^[r+1] b_r = phi P_1(phi^[r]); naturality is applied at the actual arrow u=phi^[r]:P_r K->K, not at a different power or object. Composing these with H and the stated transport recurrence has matching source/target throughout and gives the new node's recurrence. This argument does not rely on the new normalization node, so the two extracted nodes are independent work items.

Small-case checks: at r=1 the normalization formula has one transport and d_1=id; at r=2 it is H(b_1)tau_(1,T M)tau_(1,M). The recurrence at r=1 yields U_2=U_1 composed with U_1 using phi^[2] b_1=phi T(phi). No r=0 is quantified, avoiding nonexistent phi^[0] or P_0 conventions. For the zero complex every map is the unique endomorphism, which is its identity and an isomorphism; both statements therefore remain valid. For X empty the same zero-complex check applies. For n=1 the finite coefficient domain is unchanged. No statement was disputed or weakened.

I checked the B-E issues explicitly in this review: all newly introduced objects/hypotheses are written in the two statements; each used notion has its defining DAG citation; new nodes have no proof content in their JSON; TeX is encoded once; there are no invented Stacks tags; logged searches match the records and unavailable services are labelled; the duplicate distinctions above include the tempting abstract iterate formula. All parent citations are backed by verbatim statement text in citations.json. The parent's extracted subarguments are independent and neither restates its full conclusion. Every old argument is retained in the migration below. The worker wrote only in this sandbox and used only read-only searches elsewhere.

## Preserved arguments for the new-node workers

The following are the original returned arguments, unchanged. They are proof plans in this report, not proof steps attached to the new unsplit JSON nodes. Their sources and all prerequisites are identified in the review above.

### Normalization node: original steps 2-3

For $r\geq1$, the direct transport $\tau^{(r)}_{c,M}$ is defined on $D^b_c(X,A)$: the automorphism $g_\gamma$ has inverse $(g_\gamma^{-1})$, so every power is an isomorphism; $\ell\ne p$ makes $\ell$ invertible on $X$, and [lem-weil-isomorphism-derived-pullback] preserves bounded constructibility under $P_r$. [lem-trf-compact-frobenius-transport-composition] gives
$$\tau^{(r+1)}_{c,M}=H(b_{r,M})\circ\tau^{(1)}_{c,P_rM}\circ\tau^{(r)}_{c,M}.$$
By clause 3 of [lem-weil-frobenius-cohomology-transport-iso], the degree-one transports are isomorphisms on these objects; induction from $r=1$ makes every $\tau^{(r)}_{c,M}$ an isomorphism.

Write $d_{r,M}:P_rM\xrightarrow{\sim}T^rM$ for the canonical comparison (the $c_r$ of [def-trf-frobenius-operators]) and set
$$S_{r,M}=H(d_{r,M}^{-1})\circ\tau_{c,T^{r-1}M}\circ\cdots\circ\tau_{c,M}.$$
Here $P_1=T$ and $d_1=\mathrm{id}_T$ by the operator definition. The comparison coherence
$$d_{r+1,M}^{-1}\circ T(d_{r,M})=b_{r,M}$$
is [lem-trf-frobenius-pullback-comparison-coherence]. Applying the formal repeated-transport induction [lem-trf-frobenius-transport-induction] to the recurrence in the preceding step and to the naturality of $\tau_c$ from [def-weil-frobenius-cohomology-transport] gives $S_{r,M}=\tau^{(r)}_{c,M}$ for every $r$. Thus the repeated arrow in the current operator definition is the direct compact-support transport along $g_\gamma^r$.

### Recurrence node: original step 4

Define $T_r=H(\varphi^{[r]})\circ\tau^{(r)}_{c,K}$ for $r\geq1$. By [def-trf-iterated-weil-map], $\varphi^{[1]}=\varphi$, so step 1 gives $T_1=F_{c,K}$. Write $u=\varphi^{[r]}:P_rK\to K$. The cocycle of [lem-trf-iterated-weil-cocycle] with indices $1,r$ reads
$$\varphi^{[r+1]}\circ b_{r,K}=\varphi\circ P_1(u).$$
Naturality of the degree-one transport, stated in [def-weil-frobenius-cohomology-transport], applied to this particular morphism $u$, reads
$$H(P_1u)\circ\tau^{(1)}_{c,P_rK}=\tau^{(1)}_{c,K}\circ H(u).$$
Substituting these two identities and the composition identity of [lem-trf-compact-frobenius-transport-composition], and using functoriality of $H$, gives the explicit calculation
$$\begin{aligned}
T_{r+1}&=H(\varphi^{[r+1]})H(b_{r,K})\tau^{(1)}_{c,P_rK}\tau^{(r)}_{c,K}\\
&=H(\varphi)H(P_1u)\tau^{(1)}_{c,P_rK}\tau^{(r)}_{c,K}\\
&=H(\varphi)\tau^{(1)}_{c,K}H(u)\tau^{(r)}_{c,K}=T_1\circ T_r.
\end{aligned}$$
All products in this display are compositions, with the rightmost map applied first. The canonical pullback comparison is displayed as $b_{r,K}$, so no coherence map is suppressed at the coefficient substitution.

### Parent assembly: retained original steps 1 and 5

Work at $A=A_{E,n}$, let $m\geq1$, and put $H=R\Gamma_c(X,-)$, $P_r=L(g_\gamma^r)^*$ and $T=P_1$. Clause 1 of the current [def-trf-frobenius-operators], at $m=1$, defines
$$F_{c,K}=H(\varphi)\circ\tau_{c,K}.$$
The transport here is exactly the composite of [def-weil-frobenius-cohomology-transport]:
$$H(K)\xrightarrow{\ \iota_{Ra_{X!}K}\ }\operatorname{Fib}_s(Lh^*Ra_{X!}K)\xrightarrow{\ \operatorname{Fib}_s(\operatorname{FrEx}_{X,!}(K))\ }H(TK),$$
where $h=\operatorname{Spec}(\gamma)$ and $\operatorname{FrEx}_{X,!}$ is part 2 of [def-weil-frobenius-square-exchange] for $f_0=a_{X_0}$. Fix its compactification over $k_0$ throughout. By [def-trf-coefficient-conventions], applying the point fiber to $Ra_{X!}(\varphi)$ is $H(\varphi)$. Thus, writing $\tau^{(1)}_{c,K}=\tau_{c,K}$ as in the transport-composition lemma below, we have $F_{c,K}=H(\varphi)\tau^{(1)}_{c,K}$. This is a direct expansion of the current finite-A definition, with no appeal to a separate pair-action construction.

Induct on the positive integer $r$. The base $T_1=F_{c,K}$ was proved in step 4. If $T_r=(F_{c,K})^r$, that step gives $T_{r+1}=T_1\circ T_r=F_{c,K}\circ(F_{c,K})^r=(F_{c,K})^{r+1}$. Clause 1 of [def-trf-frobenius-operators] defines its notation $F_{c,K}^{\,m}$ as $H(\varphi^{[m]})\circ S_{m,K}$, where $S_{m,K}$ is the repeated-transport composite written in step 3. That step proves $S_{m,K}=\tau^{(m)}_{c,K}$, the direct transport along $g_\gamma^m$. Substituting yields
$$F_{c,K}^{\,m}=H(\varphi^{[m]})\tau^{(m)}_{c,K}=T_m=(F_{c,K})^m.$$
Thus the definition's notation really is the m-th power, and its first arrow is the direct compact-support base-change isomorphism, rather than merely a formally repeated arrow. With the notation of the statement this is
$$F_{c,K}^{\,m}=R\Gamma_c(X,\varphi^{[m]})\circ g_{\gamma,c}^{m,*}.$$
This equality holds on the compact-support complex, before taking cohomology.
