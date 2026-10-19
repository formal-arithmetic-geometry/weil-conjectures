Files written:

- `dag/nodes/sec-trace-formula/lem-trf-completion-kahler-differential-comparison.json`: seven proof steps, unchanged statement; no new nodes and no new Mathlib leaves.
- `citations.json`: eighteen verbatim statement quotations, one per cited node per proof step. Its full contents are reproduced below so that the delivery commit contains the citation evidence.

Attachments:

- None. Read-only searches by the item id, blueprint tag and completion/differential keywords in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found no project declaration stating the comparison. The reference master source also has no matching declaration. No attachment is claimed from an upstream sorry declaration.

WANTED:

- None. All source passages used are present locally.

What was wrong or incomplete:

- The original unsplit item left the completion-to-continuous-differentials argument unstated. The retained delivery supplied that argument but omitted the Noetherianity and finite-generation hypotheses required by its completion citations and mishandled the shift in the inverse-limit composite check.
- The statement is unchanged. Finite separability kills the differential of the chosen coefficient field; a section is an assumption, so no existence theorem for the section is used in the proof.
- Curves 0C4D supplies the Jacobian-completion context, not a verbatim proof of this general comparison. Accordingly the expanded proof remains marked `proof_origin.by = agent`.

What could not be finished:

- Nothing in this stage-1 split. No Lean was written and no compiler, Lake or build tool was run.

## Repair of return 46564afece

1. Step 1 now proves directly that the field k is Noetherian (its ideals are zero or the unit ideal), applies the existing Mathlib leaves `lem-weil-pbc-finite-type-algebra-noetherian` and `lem-weil-pbc-localization-noetherian` to obtain S and A Noetherian, and applies `def-weil-pbc-noetherian-ring` to obtain finite generation of m. Only then does it use the finite-module completion/tensor lemma and the finitely-generated-ideal completeness lemma. No missing hypothesis is silently inferred from a definition of flatness or completion.
2. Steps 4–6 define Q_r=N/m^rN, D_r=Omega_{B_r/F}, alpha_r:Q_r->D_r, beta_r:D_{r+1}->Q_r, and their transitions. The reverse map has component (Psi(z))_r=beta_r(z_{r+1}) for every r>=1. Its compatibility is q_r beta_{r+1}=beta_r t_{r+1}. Both identities beta_r alpha_{r+1}=q_r and alpha_r beta_r=t_r are proved on differential symbols with their domains written down; applying these identities gives both composites at the same level r, including r=1. Step 7 proves compatibility with the extended derivation directly on quotient coordinates. The erroneous beta_{r-1} formula and the cofinal-index justification have been removed.
3. `citations.json` is present and regenerated for all eighteen citations. The standard delivery script checks this file but packages node JSON files and report.md only. To repair the absent-packet evidence without changing that script, this report includes the complete JSON verbatim in the appendix below, in addition to retaining the required standalone sandbox file.

I continued the retained node and report rather than starting over. I compared them with the current shared repository: its item is still unsplit, with the same statement and source/search records. The retained blueprint ancestry had inserted the item itself into its `via` list; I restored the current repository's historical ancestry. Existing recorded search results were retained, read, and reused. The retained supplemental Noetherian searches found `Algebra.FiniteType.isNoetherianRing` and `Algebra.EssFiniteType.isNoetherianRing`; whole-DAG searches found the more precise existing finite-type and localization leaves, so no node was created. A second semantic phrasing for the item returned square-zero derivation/lift equivalences, universal derivations and formally smooth lifts into completions, with no statement of this continuous-differential comparison; the executed query is recorded in the item and searches.jsonl.

## Review by NE

I read the retained split, the return entry, the current item, the chapter and unit records, and the current blueprint unit and ancestor proof. This item remains the existing algebraic tool beneath the Jacobian/Fitting comparison; no chapter or unit route was changed. I read Curves 0C4D (`lemma-nodal`), in particular the Jacobian presentation and completion paragraph and the arbitrary-field discussion; Algebra 00FM (`section-Noetherian`), 00FN (`lemma-Noetherian-permanence`), 00RT (`lemma-differentials-localize`), 00MA (`lemma-completion-tensor`), 05GG (`lemma-hathat-finitely-generated`), the Kähler definition/construction and universal property (07BK/00RO), and 090W (`lemma-characterize-separable-algebraic-field-extensions`). I also read More Algebra 0C34 (`lemma-lift-residue-field`): it explains the coefficient-section context, but our proof assumes the section already chosen. The earlier reading of 00RS/00RU/00RX remains source context, not an extra uncited theorem in the repaired steps.

For Step 1 I opened each of its seven cited node statements. The Noetherian definition says every ideal is finitely generated, the finite-type lemma applies over any Noetherian base ring, and the localization lemma accepts precisely localization at the multiplicative set S minus p. These yield all ring/ideal hypotheses used subsequently. The Kähler symbol presentation gives finite generation by differentiating finite algebra generators, and the localization statement identifies their localized differentials with Omega_{A/k}. The tensor-completion statement requires A Noetherian and M finite; both have just been established. The completion-completeness statement requires only m finitely generated and applies separately to the module M and the ring A. It states both the quotient identifications and the completeness/separatedness assertions used here. All are existing generic tools; no new node or duplicate is needed.

For Step 2 I checked the derivative estimate on a product of r+1 ideal elements, including sums and multiplication by arbitrary ring elements. The extra term from differentiating a coefficient still has r+1 ideal factors, so lies in m^rM. This makes delta_r independent of its chosen lift modulo m^{r+1}. The derivation identities and transition compatibility are componentwise consequences of the symbol definition and the canonical quotients. Completeness supplies the resulting element of N, while separatedness and continuity give uniqueness. This is the elementary quotient-coordinate construction written out, with no extension-of-derivations theorem assumed.

For Step 3 the finite-separable vanishing node states exactly Omega_{F/k}=0. The Kähler universal property applies to the k-derivation d-hat composed with sigma and the F-module structure induced by sigma, so d-hat kills F. No perfection or algebraic-closure hypothesis is introduced.

For Step 4 the same universal property gives alpha_r because D_r is a B_r-module and therefore kills m^rM. The completion node supplies Q_r=M/m^rM. Equality on the symbols da proves t_r alpha_{r+1}=alpha_r q_r; the symbol presentation ensures they generate. This proves the inverse-limit map without assuming a comparison theorem.

For Step 5 the reverse level map starts on D_{r+1} and lands on Q_r. The derivative estimate kills m^{r+1}, and Step 3 kills the coefficient field, so the universal property has exactly the required hypotheses. I checked q_r beta_{r+1}=beta_r t_{r+1} on symbols of D_{r+2}; it yields compatibility of beta_r(z_{r+1}) in Q_r for every r>=1. Completeness identifies this sequence with an element of N. All scalar actions factor through the displayed quotients, so Psi is A-hat-linear.

For Step 6 I checked both finite-level composite identities separately. The first is a map Q_{r+1}->Q_r and is tested on da. The second is a map D_{r+1}->D_r; every b in B_{r+1} lifts to A by Step 1, so it can be tested on db using such a lift. The symbol presentation in the cited Kähler definition justifies generation, and the completion node justifies equality in N from all quotient components. The resulting two inverse-limit identities use beta_r, never beta_{r-1}.

For Step 7 I checked the equality on an arbitrary x in A-hat, choosing a lift only modulo m^{r+1}; the same derivative estimate makes its r-th coordinate equal the required differential. Uniqueness is algebraic because the da tensor 1 generate the source over A-hat; it does not rely on a topology on the inverse-limit target. Its only cited node is the actual symbol presentation, not a definition being used as an unstated theorem.

I checked B–E against the repaired files and source statements. No new node is introduced, so there are no new self-containedness, duplication, or hidden-clause issues. Every proof citation has an exact statement quotation below and in citations.json; proof_deps is exactly their union. Every step is below 2000 characters. The non-elementary inputs are all cited existing nodes; the remaining symbol, lift and coordinate calculations are explicit. The generic tools outside the unit are declared for maintainer review. I tested the indexing at r=1 (beta_1:D_2->Q_1 and both composites still hold), the field case m=0 (both differential modules vanish by finite separability), and the smooth model A=k[t]_(t). In characteristic p, differentiating t^p may give zero, but the containment d(m^{r+1}) subset m^rM and both composite identities still hold; no division by an integer occurs. The repaired proof imposes no new characteristic or regularity hypothesis.

## Citation evidence (contents of citations.json)

The standalone file is required by the sandbox check. This identical copy is included in the delivered report so that the independent reviewer receives it in the packet.

```json
[
 {
  "step": 1,
  "node": "def-weil-pbc-noetherian-ring",
  "quote": "A commutative ring $R$ is *Noetherian* if every ideal of $R$ is finitely generated."
 },
 {
  "step": 1,
  "node": "lem-weil-pbc-finite-type-algebra-noetherian",
  "quote": "Let $R$ be a Noetherian ring [def-weil-pbc-noetherian-ring] and $R\\to S$ a ring map of commutative rings of finite type, i.e. $S\\cong R[x_1,\\dots,x_n]/\\mathfrak a$ as $R$-algebras for some $n\\ge0$ and some ideal $\\mathfrak a$. Then $S$ is a Noetherian ring."
 },
 {
  "step": 1,
  "node": "lem-weil-pbc-localization-noetherian",
  "quote": "Let $R$ be a Noetherian ring [def-weil-pbc-noetherian-ring] and $S\\subseteq R$ a multiplicative subset ($1\\in S$, $st\\in S$ for $s,t\\in S$). Let $\\varphi:R\\to R'$ be a homomorphism of commutative rings that is a localization of $R$ at $S$: (a) $\\varphi(s)$ is a unit of $R'$ for every $s\\in S$; (b) every element of $R'$ is $\\varphi(r)\\varphi(s)^{-1}$ for some $r\\in R$, $s\\in S$; (c) $\\varphi(r)=0$ implies $sr=0$ for some $s\\in S$ (for instance $R'=S^{-1}R$, the ring of fractions $r/s$, with $r\\mapsto r/1$). Then $R'$ is a Noetherian ring."
 },
 {
  "step": 1,
  "node": "def-weil-pbc-kahler-differentials",
  "quote": "Let $\\varphi:R\\to A$ be a homomorphism of commutative rings. For an $A$-module $M$, an *$R$-derivation* $D:A\\to M$ is an additive map with $D(fg)=f\\,D(g)+g\\,D(f)$ for $f,g\\in A$ and $D(\\varphi(r))=0$ for $r\\in R$. The *module of Kähler differentials* of $A$ over $R$ is the pair $(\\Omega_{A/R},\\mathrm d)$ of an $A$-module $\\Omega_{A/R}$ and an $R$-derivation $\\mathrm d:A\\to\\Omega_{A/R}$ that is universal: for every $A$-module $M$, composition with $\\mathrm d$ is a bijection $\\operatorname{Hom}_A(\\Omega_{A/R},M)\\to\\{R\\text{-derivations }A\\to M\\}$. It exists and is unique up to unique isomorphism: $\\Omega_{A/R}$ is the quotient of the free $A$-module on symbols $[a]$, $a\\in A$, by the submodule generated by $[a+b]-[a]-[b]$, $[fg]-f[g]-g[f]$ and $[\\varphi(r)]$, with $\\mathrm da$ the class of $[a]$."
 },
 {
  "step": 1,
  "node": "lem-weil-pbc-kahler-differentials-localization",
  "quote": "Let $A\\to B$ be a homomorphism of commutative rings, $S\\subset B$ a multiplicative subset and $S^{-1}B$ the localization, an $A$-algebra via $A\\to B\\to S^{-1}B$. Then the $S^{-1}B$-linear map $S^{-1}\\Omega_{B/A}\\to\\Omega_{S^{-1}B/A}$, $\\mathrm db/s\\mapsto(1/s)\\,\\mathrm d(b/1)$, induced by the map $\\Omega_{B/A}\\to\\Omega_{S^{-1}B/A}$ of $B\\to S^{-1}B$ ($\\Omega$ and $\\mathrm d$ as in [def-weil-pbc-kahler-differentials]), is an isomorphism. In particular, for $g\\in B$, $\\Omega_{B_g/A}\\cong(\\Omega_{B/A})_g$."
 },
 {
  "step": 1,
  "node": "lem-weil-pbc-completion-finite-module-tensor",
  "quote": "Let $A$ be a Noetherian ring [def-weil-pbc-noetherian-ring], $I\\subseteq A$ an ideal and $A^\\wedge=\\varprojlim_nA/I^n$ the $I$-adic completion [def-weil-pbc-adic-completion]. For an $A$-module $P$ let $P^\\wedge=\\varprojlim_nP/I^nP$ (compatible sequences, an $A^\\wedge$-module by $(a_n)_n\\cdot(x_n)_n=(a_nx_n)_n$), with the $A$-linear map $\\iota_P:P\\to P^\\wedge$, $x\\mapsto(x\\bmod I^nP)_n$, and for an $A$-linear $u:P\\to Q$ let $u^\\wedge:P^\\wedge\\to Q^\\wedge$, $(x_n)_n\\mapsto(u(x_n))_n$. Let $c_P:A^\\wedge\\otimes_AP\\to P^\\wedge$ be the $A^\\wedge$-linear map with $c_P(a\\otimes x)=a\\cdot\\iota_P(x)$ (the tensor product as in [def-weil-module-base-change], with $A^\\wedge$ written on the left). Then (1) $c$ is natural: $u^\\wedge\\circ c_P=c_Q\\circ(\\mathrm{id}_{A^\\wedge}\\otimes u)$ for every $A$-linear $u:P\\to Q$; (2) if $P$ is a finitely generated $A$-module [def-weil-finitely-generated-module], then $c_P$ is bijective, so $P^\\wedge\\cong A^\\wedge\\otimes_AP$ as $A^\\wedge$-modules."
 },
 {
  "step": 1,
  "node": "lem-weil-pbc-module-completion-complete",
  "quote": "Let $A$ be a commutative ring, $I\\subseteq A$ a finitely generated ideal and $M$ an $A$-module. Let $M^\\wedge=\\varprojlim_nM/I^nM$ (compatible sequences, componentwise $A$-module structure) with projections $p_n:M^\\wedge\\to M/I^nM$, $(x_k)_k\\mapsto x_n$. Then (1) $M^\\wedge$ is $I$-adically complete as an $A$-module: the canonical map $M^\\wedge\\to\\varprojlim_nM^\\wedge/I^nM^\\wedge$ is bijective; in particular $\\bigcap_{n\\ge1}I^nM^\\wedge=0$; (2) for every $n\\ge1$, $p_n$ is surjective with kernel $I^nM^\\wedge$ (the $A$-submodule generated by the $ay$, $a\\in I^n$, $y\\in M^\\wedge$), so $p_n$ induces an $A$-linear isomorphism $M^\\wedge/I^nM^\\wedge\\cong M/I^nM$."
 },
 {
  "step": 2,
  "node": "def-weil-pbc-kahler-differentials",
  "quote": "Let $\\varphi:R\\to A$ be a homomorphism of commutative rings. For an $A$-module $M$, an *$R$-derivation* $D:A\\to M$ is an additive map with $D(fg)=f\\,D(g)+g\\,D(f)$ for $f,g\\in A$ and $D(\\varphi(r))=0$ for $r\\in R$. The *module of Kähler differentials* of $A$ over $R$ is the pair $(\\Omega_{A/R},\\mathrm d)$ of an $A$-module $\\Omega_{A/R}$ and an $R$-derivation $\\mathrm d:A\\to\\Omega_{A/R}$ that is universal: for every $A$-module $M$, composition with $\\mathrm d$ is a bijection $\\operatorname{Hom}_A(\\Omega_{A/R},M)\\to\\{R\\text{-derivations }A\\to M\\}$. It exists and is unique up to unique isomorphism: $\\Omega_{A/R}$ is the quotient of the free $A$-module on symbols $[a]$, $a\\in A$, by the submodule generated by $[a+b]-[a]-[b]$, $[fg]-f[g]-g[f]$ and $[\\varphi(r)]$, with $\\mathrm da$ the class of $[a]$."
 },
 {
  "step": 2,
  "node": "lem-weil-pbc-module-completion-complete",
  "quote": "Let $A$ be a commutative ring, $I\\subseteq A$ a finitely generated ideal and $M$ an $A$-module. Let $M^\\wedge=\\varprojlim_nM/I^nM$ (compatible sequences, componentwise $A$-module structure) with projections $p_n:M^\\wedge\\to M/I^nM$, $(x_k)_k\\mapsto x_n$. Then (1) $M^\\wedge$ is $I$-adically complete as an $A$-module: the canonical map $M^\\wedge\\to\\varprojlim_nM^\\wedge/I^nM^\\wedge$ is bijective; in particular $\\bigcap_{n\\ge1}I^nM^\\wedge=0$; (2) for every $n\\ge1$, $p_n$ is surjective with kernel $I^nM^\\wedge$ (the $A$-submodule generated by the $ay$, $a\\in I^n$, $y\\in M^\\wedge$), so $p_n$ induces an $A$-linear isomorphism $M^\\wedge/I^nM^\\wedge\\cong M/I^nM$."
 },
 {
  "step": 3,
  "node": "def-weil-pbc-kahler-differentials",
  "quote": "Let $\\varphi:R\\to A$ be a homomorphism of commutative rings. For an $A$-module $M$, an *$R$-derivation* $D:A\\to M$ is an additive map with $D(fg)=f\\,D(g)+g\\,D(f)$ for $f,g\\in A$ and $D(\\varphi(r))=0$ for $r\\in R$. The *module of Kähler differentials* of $A$ over $R$ is the pair $(\\Omega_{A/R},\\mathrm d)$ of an $A$-module $\\Omega_{A/R}$ and an $R$-derivation $\\mathrm d:A\\to\\Omega_{A/R}$ that is universal: for every $A$-module $M$, composition with $\\mathrm d$ is a bijection $\\operatorname{Hom}_A(\\Omega_{A/R},M)\\to\\{R\\text{-derivations }A\\to M\\}$. It exists and is unique up to unique isomorphism: $\\Omega_{A/R}$ is the quotient of the free $A$-module on symbols $[a]$, $a\\in A$, by the submodule generated by $[a+b]-[a]-[b]$, $[fg]-f[g]-g[f]$ and $[\\varphi(r)]$, with $\\mathrm da$ the class of $[a]$."
 },
 {
  "step": 3,
  "node": "lem-trf-separable-field-differentials-vanish",
  "quote": "If F/k is a finite separable extension of fields, then \\Omega_{F/k}=0 (equivalently, the universal k-derivation F\\to\\Omega_{F/k} is zero), with \\Omega as in [def-weil-pbc-kahler-differentials]."
 },
 {
  "step": 4,
  "node": "def-weil-pbc-kahler-differentials",
  "quote": "Let $\\varphi:R\\to A$ be a homomorphism of commutative rings. For an $A$-module $M$, an *$R$-derivation* $D:A\\to M$ is an additive map with $D(fg)=f\\,D(g)+g\\,D(f)$ for $f,g\\in A$ and $D(\\varphi(r))=0$ for $r\\in R$. The *module of Kähler differentials* of $A$ over $R$ is the pair $(\\Omega_{A/R},\\mathrm d)$ of an $A$-module $\\Omega_{A/R}$ and an $R$-derivation $\\mathrm d:A\\to\\Omega_{A/R}$ that is universal: for every $A$-module $M$, composition with $\\mathrm d$ is a bijection $\\operatorname{Hom}_A(\\Omega_{A/R},M)\\to\\{R\\text{-derivations }A\\to M\\}$. It exists and is unique up to unique isomorphism: $\\Omega_{A/R}$ is the quotient of the free $A$-module on symbols $[a]$, $a\\in A$, by the submodule generated by $[a+b]-[a]-[b]$, $[fg]-f[g]-g[f]$ and $[\\varphi(r)]$, with $\\mathrm da$ the class of $[a]$."
 },
 {
  "step": 4,
  "node": "lem-weil-pbc-module-completion-complete",
  "quote": "Let $A$ be a commutative ring, $I\\subseteq A$ a finitely generated ideal and $M$ an $A$-module. Let $M^\\wedge=\\varprojlim_nM/I^nM$ (compatible sequences, componentwise $A$-module structure) with projections $p_n:M^\\wedge\\to M/I^nM$, $(x_k)_k\\mapsto x_n$. Then (1) $M^\\wedge$ is $I$-adically complete as an $A$-module: the canonical map $M^\\wedge\\to\\varprojlim_nM^\\wedge/I^nM^\\wedge$ is bijective; in particular $\\bigcap_{n\\ge1}I^nM^\\wedge=0$; (2) for every $n\\ge1$, $p_n$ is surjective with kernel $I^nM^\\wedge$ (the $A$-submodule generated by the $ay$, $a\\in I^n$, $y\\in M^\\wedge$), so $p_n$ induces an $A$-linear isomorphism $M^\\wedge/I^nM^\\wedge\\cong M/I^nM$."
 },
 {
  "step": 5,
  "node": "def-weil-pbc-kahler-differentials",
  "quote": "Let $\\varphi:R\\to A$ be a homomorphism of commutative rings. For an $A$-module $M$, an *$R$-derivation* $D:A\\to M$ is an additive map with $D(fg)=f\\,D(g)+g\\,D(f)$ for $f,g\\in A$ and $D(\\varphi(r))=0$ for $r\\in R$. The *module of Kähler differentials* of $A$ over $R$ is the pair $(\\Omega_{A/R},\\mathrm d)$ of an $A$-module $\\Omega_{A/R}$ and an $R$-derivation $\\mathrm d:A\\to\\Omega_{A/R}$ that is universal: for every $A$-module $M$, composition with $\\mathrm d$ is a bijection $\\operatorname{Hom}_A(\\Omega_{A/R},M)\\to\\{R\\text{-derivations }A\\to M\\}$. It exists and is unique up to unique isomorphism: $\\Omega_{A/R}$ is the quotient of the free $A$-module on symbols $[a]$, $a\\in A$, by the submodule generated by $[a+b]-[a]-[b]$, $[fg]-f[g]-g[f]$ and $[\\varphi(r)]$, with $\\mathrm da$ the class of $[a]$."
 },
 {
  "step": 5,
  "node": "lem-weil-pbc-module-completion-complete",
  "quote": "Let $A$ be a commutative ring, $I\\subseteq A$ a finitely generated ideal and $M$ an $A$-module. Let $M^\\wedge=\\varprojlim_nM/I^nM$ (compatible sequences, componentwise $A$-module structure) with projections $p_n:M^\\wedge\\to M/I^nM$, $(x_k)_k\\mapsto x_n$. Then (1) $M^\\wedge$ is $I$-adically complete as an $A$-module: the canonical map $M^\\wedge\\to\\varprojlim_nM^\\wedge/I^nM^\\wedge$ is bijective; in particular $\\bigcap_{n\\ge1}I^nM^\\wedge=0$; (2) for every $n\\ge1$, $p_n$ is surjective with kernel $I^nM^\\wedge$ (the $A$-submodule generated by the $ay$, $a\\in I^n$, $y\\in M^\\wedge$), so $p_n$ induces an $A$-linear isomorphism $M^\\wedge/I^nM^\\wedge\\cong M/I^nM$."
 },
 {
  "step": 6,
  "node": "def-weil-pbc-kahler-differentials",
  "quote": "Let $\\varphi:R\\to A$ be a homomorphism of commutative rings. For an $A$-module $M$, an *$R$-derivation* $D:A\\to M$ is an additive map with $D(fg)=f\\,D(g)+g\\,D(f)$ for $f,g\\in A$ and $D(\\varphi(r))=0$ for $r\\in R$. The *module of Kähler differentials* of $A$ over $R$ is the pair $(\\Omega_{A/R},\\mathrm d)$ of an $A$-module $\\Omega_{A/R}$ and an $R$-derivation $\\mathrm d:A\\to\\Omega_{A/R}$ that is universal: for every $A$-module $M$, composition with $\\mathrm d$ is a bijection $\\operatorname{Hom}_A(\\Omega_{A/R},M)\\to\\{R\\text{-derivations }A\\to M\\}$. It exists and is unique up to unique isomorphism: $\\Omega_{A/R}$ is the quotient of the free $A$-module on symbols $[a]$, $a\\in A$, by the submodule generated by $[a+b]-[a]-[b]$, $[fg]-f[g]-g[f]$ and $[\\varphi(r)]$, with $\\mathrm da$ the class of $[a]$."
 },
 {
  "step": 6,
  "node": "lem-weil-pbc-module-completion-complete",
  "quote": "Let $A$ be a commutative ring, $I\\subseteq A$ a finitely generated ideal and $M$ an $A$-module. Let $M^\\wedge=\\varprojlim_nM/I^nM$ (compatible sequences, componentwise $A$-module structure) with projections $p_n:M^\\wedge\\to M/I^nM$, $(x_k)_k\\mapsto x_n$. Then (1) $M^\\wedge$ is $I$-adically complete as an $A$-module: the canonical map $M^\\wedge\\to\\varprojlim_nM^\\wedge/I^nM^\\wedge$ is bijective; in particular $\\bigcap_{n\\ge1}I^nM^\\wedge=0$; (2) for every $n\\ge1$, $p_n$ is surjective with kernel $I^nM^\\wedge$ (the $A$-submodule generated by the $ay$, $a\\in I^n$, $y\\in M^\\wedge$), so $p_n$ induces an $A$-linear isomorphism $M^\\wedge/I^nM^\\wedge\\cong M/I^nM$."
 },
 {
  "step": 7,
  "node": "def-weil-pbc-kahler-differentials",
  "quote": "Let $\\varphi:R\\to A$ be a homomorphism of commutative rings. For an $A$-module $M$, an *$R$-derivation* $D:A\\to M$ is an additive map with $D(fg)=f\\,D(g)+g\\,D(f)$ for $f,g\\in A$ and $D(\\varphi(r))=0$ for $r\\in R$. The *module of Kähler differentials* of $A$ over $R$ is the pair $(\\Omega_{A/R},\\mathrm d)$ of an $A$-module $\\Omega_{A/R}$ and an $R$-derivation $\\mathrm d:A\\to\\Omega_{A/R}$ that is universal: for every $A$-module $M$, composition with $\\mathrm d$ is a bijection $\\operatorname{Hom}_A(\\Omega_{A/R},M)\\to\\{R\\text{-derivations }A\\to M\\}$. It exists and is unique up to unique isomorphism: $\\Omega_{A/R}$ is the quotient of the free $A$-module on symbols $[a]$, $a\\in A$, by the submodule generated by $[a+b]-[a]-[b]$, $[fg]-f[g]-g[f]$ and $[\\varphi(r)]$, with $\\mathrm da$ the class of $[a]$."
 }
]
```
