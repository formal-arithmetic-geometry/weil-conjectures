# Q84 repair: lem-trf-henselization-prime-ind-etale

Files delivered:

- `dag/nodes/sec-trace-formula/lem-trf-henselization-prime-ind-etale.json`: repaired split, seven proof steps, unchanged statement, no new nodes and no new Mathlib leaves.
- This report is delivered as `coord/reports/Q84/lem-trf-henselization-prime-ind-etale.md`.

Sandbox validation input: `citations.json` exists and contains verbatim statement quotations for every step/node pair. The delivery tool validates this input but does not put the standalone file in the delivery commit; its complete contents are included below so the maintainer receives the evidence. `searches.jsonl` retains all prior searches and the actual additional repair searches. No `lem-trf-prime-localization-ind-etale.json` is claimed or needed: the localization argument uses the existing general localization-colimit node. The rejected, unmerged `lem-trf-henselization-local-ind-etale.json` is removed: the existing, more general henselization-of-pairs theorem supplies the construction.

Attachments: none. Read-only searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint tag, henselization/henselisation and ind-etale terminology found no project declaration of this item. The available ind-etale API does not construct an ordinary henselization. Upstream master sorry declarations are not used as completed proofs.

WANTED: Hübner–Schmidt, *An algebraic tame site*, sentence between Theorems 6.3 and 6.4, for the historical motivation recorded by the previous attempt. That paper is not needed for this split; the proof uses the available Stacks sources.

## Repair of the return

The returned head is `0955b0a121`. I compared the retained item with the current repository node, retained its statement, localization argument, composition argument, source references, historical blueprint ancestry and search records, and restored its original Q67 creation metadata from current main. The initial required dry run passed at `d86292e543`, but this mechanical success did not repair the mathematical gap, so I rewrote the proof before the final dry run.

Error E is repaired by avoiding any identification of an arbitrary universal-property henselization with Stacks' constructed object without proof. The existing `lem-weil-pbc-pair-henselization` gives a constructed etale colimit C with a henselian maximal-ideal pair and residue field k. Step 3 proves locality explicitly, using a finite quotient algebra to show that 1-z is invertible for z in its henselian ideal. Steps 4-5 construct both local maps and prove both composites are identities. Step 6 constructs the transported coprojections and proves their colimit property against an arbitrary compatible cocone. Thus no invariance-of-ind-etaleness assertion is left implicit, and no unchanged relabelling prerequisite is delivered.

Error A is repaired by making the inventory match the actual files. The absent prime-localization node is no longer listed. The actual sandbox citation input is regenerated, and all of its contents are embedded in this report, because the installed delivery tool tracks node JSON and this report, not a standalone citations file. This is also a report upward of that packaging limitation; no launcher or project script was changed.

## Review by Q84

I read Stacks `algebra.tex`, Tag 04GN (`lemma-henselization`), including its constructed pointed-etale colimit and all four conclusions, and Tag 04GQ (`definition-henselization`). These establish the source intent, but do not justify applying the construction to an arbitrary H without comparison. I then read `more-algebra.tex`, Tag 0A02 (`lemma-henselization`) and its full construction proof, and `algebra.tex`, Tag 08HR (`lemma-map-into-henselian-colimit`), including its prescribed-residue uniqueness. The retained proposed local prerequisite is unnecessary because the DAG already states the more general pair construction. No new statement-only node remains to check or search.

For Step 1 I opened `lem-weil-pbc-localization-colimit-principal-localizations` and checked its actual statement supplies filteredness of the divisibility preorder, the ring colimit and compatibility with the structural map. Its hypotheses hold for S=A minus p because p is prime. I opened `lem-weil-pbc-etale-algebra-finite-presentation-localization`: clause (2) applied to the identity gives etaleness of each A_s; clause (1) applied again to that map gives finite presentation. This explicitly corrects the possibility of reading clause (1) only for the identity. The cited ind-etale definition then applies to exactly this filtered presentation. I read the corresponding Stacks Tags 00CR and 00U2; no localization finiteness or Noetherianity assumption is introduced.

For Step 2 I opened `lem-weil-pbc-pair-henselization`. Its statement explicitly gives essential smallness and directedness of the etale-algebra category, the henselian pair (C,mC), and the structural isomorphism k to C/mC. A small skeleton is used for its stated colimit. Finite presentation of every stage follows from clause (1) of the previously opened etale node. R=A_p is local by the fraction inverse calculation written in the step, with proper maximal ideal pR; k is a nonzero field because p is prime.

For Step 3 I opened `def-weil-pbc-henselian-terminology`. Its statement supplies unique idempotent lifting for every finite algebra, and defines a henselian local ring by its maximal-ideal pair. The quotient D=C/(1-z) is finite as a C-module, generated by 1, even if C is not Noetherian. Since z lies in J and equals 1 in D, JD=D; the equal reductions of the idempotents 0 and 1 force D=0. This proves the asserted unit fact directly from the cited definition. Because C/J is the nonzero field k, elements outside J are units and J is its maximal ideal. The residue isomorphism gives contraction of J equal to m, hence the required local structure map. This is a few-line elementary consequence, not a new lemma node.

For Step 4 I opened both `def-weil-pbc-henselization-at-prime` and `lem-weil-pbc-map-into-henselian-colimit`. The definition gives exactly H's local structure and initial local-map property. The mapping lemma applies to source C, a filtered colimit of etale R-algebras, and target H, henselian local. The chosen prime is m_C; it contracts to m, as does m_H. The residue map is tau=e_H composed with e_C inverse and is a k-algebra map. No surjectivity or isomorphism of e_H is assumed. The resulting f is local because the lemma prescribes the preimage of m_H. The reverse map g exists because C has just been proved henselian local, so it is a valid target for H's universal property.

For Step 5 I rechecked the same mapping lemma's uniqueness clause, not just existence. The residue of gf is the identity because its composite with the already known isomorphism e_C is e_C. Thus gf and id_C meet exactly the same prime and residue conditions in that lemma. The equality fg=id_H follows separately from H's universal property with target H and structural map eta_H. No assertion of residue equality for H is needed in either inference. This proves an R-algebra isomorphism over the given structural maps, rather than a bare ring isomorphism.

For Step 6 I opened `def-weil-pbc-category-colimit` and `def-weil-pbc-ind-etale-algebra`. The step uses the same small index category and etale finitely presented stages from Step 2. It gives the new coprojections f iota_i and, for every compatible cocone mu_i into T, the mediating map u g, and checks that u respects R by composing with a structural map of any stage of the nonempty diagram. The equations gf=id_C and fg=id_H prove its factorization and uniqueness exactly as written. Consequently the colimit is H with its actual R-algebra structure, and the ind-etale definition applies. This elementary cocone calculation is the missing transport argument in the returned version.

For Step 7 I opened `lem-weil-pbc-ind-etale-stability` and read the exact sentence asserting stability under composition. I also read `proetale.tex`, Tag 097K (`lemma-composition-ind-etale`). Its hypotheses are precisely the two maps proved ind-etale in Steps 1 and 6; the resulting composite is the one in the unchanged item. The three off-unit construction/localization/mapping tools and the composition tool are declared in `split_report.tool_uses`; they are generic commutative-algebra tools, not replacements of a trace-formula unit step.

I read `dag/chapters/sec-trace-formula.json` and `dag/units/sk-i-curve-zero.json`, and the current `blueprint_update` of the historical ancestor `lem-trf-local-term-locality`. The current ancestor uses contracting correspondences; this node is already in its historical auxiliary chain. This repair changes no unit record, chapter, target or ancestor proof and retains the recorded ancestry. Blueprint searches for henselization, henselian, 04GN and 08HR found no imported node directly stating the item. The ordinary and strict constructions are not conflated: a chosen separable closure is not used in this proof.

Small cases: for a field, (R,0) yields a henselian local comparison object with zero maximal ideal and the same residue field, so C is R up to the structural isomorphism; the same inverse-map proof treats any H specified by the universal property. For an already henselian local R, identity maps satisfy the universal property and the comparison reduces to an isomorphism over R. Nonreduced local rings and non-Noetherian local rings are permitted: the only finite algebra in the locality argument is a cyclic quotient. The zero ring has no prime ideal and so gives no instance of the item. None of these checks requires assuming that the initially arbitrary H is an etale colimit or has the same residue field.

I checked delivery-errors B-E point by point: the unchanged statement introduces its objects; no new node or hollow construction is added; the exact sources are by tag and label; every non-elementary fact is a cited node whose statement I opened; the inverse-map and cocone arguments are written out; the dependency list is exactly the union of step uses; every proof step is under 2000 characters. No statement dispute was found. All old search logs are retained; additional actual searches for the construction found only the HenselianLocalRing property/TFAE and a one-stage etale polynomial-factorization theorem, whose source I read. Those searches are not recorded as a new leaf or used to justify an absence claim for any new node.

What could not be finished: nothing remains of the stage-1 repair once the final dry run and push succeed. No Lean was written and no compiler, Lake or build tool was run.

## Not duplicates

No new nodes are delivered. The previous unmerged local prerequisite is replaced by the existing, more general `lem-weil-pbc-pair-henselization`. The ordinary comparison and colimit transport are steps of the item; a separate prime-localization-ind-etale node would duplicate an elementary consequence of the existing localization-colimit and etale nodes.

## Citation evidence

The following is the complete content of the actual sandbox `citations.json`, copied into the tracked report for remote review.

```json
[
 {
  "step": 1,
  "node": "lem-weil-pbc-localization-colimit-principal-localizations",
  "quote": "Let $P$ be a commutative ring and $S\\subseteq P$ a multiplicative subset. For $f\\in S$ let $P_f$ be the localization of $P$ at $\\{1,f,f^2,\\dots\\}$ [def-weil-ring-localization-away] and $S^{-1}P$ the localization at $S$ [def-weil-pbc-module-localization] (with $M=P$; fractions $a/s$, $a/s=a'/s'$ iff $u(as'-a's)=0$ for some $u\\in S$). Preorder $S$ by $f\\le g$ iff $g=fh$ for some $h\\in P$. Then: (1) this preorder is directed ($f,f'\\le ff'$), so, regarded as a category, it is filtered; (2) for $f\\le g$, $g=fh$, the map $\\rho_{fg}:P_f\\to P_g$, $a/f^e\\mapsto ah^e/g^e$, is a well defined ring homomorphism, independent of the choice of $h$, with $\\rho_{ff}=\\mathrm{id}$ and $\\rho_{gk}\\circ\\rho_{fg}=\\rho_{fk}$, so $f\\mapsto P_f$ is a functor from $S$ to commutative rings; (3) the ring maps $\\kappa_f:P_f\\to S^{-1}P$, $a/f^e\\mapsto a/f^e$, satisfy $\\kappa_g\\circ\\rho_{fg}=\\kappa_f$ and make $S^{-1}P$ a colimit of this functor in the category of commutative rings [def-weil-pbc-category-colimit]: $S^{-1}P=\\varinjlim_{f\\in S}P_f$. Moreover $\\kappa_f$ composed with $P\\to P_f$ is the localization map $P\\to S^{-1}P$."
 },
 {
  "step": 1,
  "node": "lem-weil-pbc-etale-algebra-finite-presentation-localization",
  "quote": "Let $A\\to B$ be a homomorphism of commutative rings such that $\\operatorname{Spec}B\\to\\operatorname{Spec}A$ is etale [def-weil-etale-morphism]. Then (1) $A\\to B$ is of finite presentation: $B\\cong A[x_1,\\dots,x_n]/(f_1,\\dots,f_m)$ as $A$-algebras for some $n,m\\ge0$; in particular $B$ is a finitely generated $A$-algebra; (2) for every $s\\in B$, the morphism $\\operatorname{Spec}B_s\\to\\operatorname{Spec}A$ induced by $A\\to B\\to B_s=B[1/s]$ is etale."
 },
 {
  "step": 1,
  "node": "def-weil-pbc-ind-etale-algebra",
  "quote": "Let $A$ be a commutative ring and let $B$ be an $A$-algebra. The\n$A$-algebra $B$ is *ind-etale* if it is a filtered colimit of etale\n$A$-algebras of finite presentation [def-weil-pbc-scheme-conventions]. It is\n*ind-Zariski* if such a presentation can be chosen with terms finite products\nof localizations $A_f$. The corresponding affine scheme $\\operatorname{Spec}B$\nis an inverse limit of affine etale schemes, with affine transition maps. The\nring map $A\\to B$ is *weakly etale* when the induced map\n$\\operatorname{Spec}B\\to\\operatorname{Spec}A$ is weakly etale in\n[def-weil-pbc-scheme-conventions]; equivalently, $B$ is flat as an $A$-module\nand is flat as a module over $B\\otimes_A B$ via the multiplication map\n$B\\otimes_A B\\to B$."
 },
 {
  "step": 2,
  "node": "lem-weil-pbc-pair-henselization",
  "quote": "Let $B$ be a commutative ring and $J\\subseteq B$ an ideal. Let $\\mathcal C$ be the category whose objects are the etale ring maps $B\\to C$ [def-weil-etale-morphism] (i.e. $\\operatorname{Spec}C\\to\\operatorname{Spec}B$ etale) such that the induced map $B/J\\to C/JC$ is an isomorphism, and whose morphisms are the $B$-algebra maps. Then: (1) $\\mathcal C$ is essentially small and directed (nonempty, any two objects map to a common one, any two parallel morphisms are coequalized by a morphism); (2) setting $B^h=\\varinjlim_{C\\in\\mathcal C}C$ and $J^h=JB^h$, the pair $(B^h,J^h)$ is henselian [def-weil-pbc-henselian-terminology]; (3) the map $B/J\\to B^h/J^h$ is an isomorphism. (Stacks 0A02 also states that $(B,J)\\mapsto(B^h,J^h)$ is left adjoint to the inclusion of henselian pairs into pairs; that clause is not used on the route and is not part of this node: dropped by the lead at review, 2026-10-09.)"
 },
 {
  "step": 2,
  "node": "lem-weil-pbc-etale-algebra-finite-presentation-localization",
  "quote": "Let $A\\to B$ be a homomorphism of commutative rings such that $\\operatorname{Spec}B\\to\\operatorname{Spec}A$ is etale [def-weil-etale-morphism]. Then (1) $A\\to B$ is of finite presentation: $B\\cong A[x_1,\\dots,x_n]/(f_1,\\dots,f_m)$ as $A$-algebras for some $n,m\\ge0$; in particular $B$ is a finitely generated $A$-algebra; (2) for every $s\\in B$, the morphism $\\operatorname{Spec}B_s\\to\\operatorname{Spec}A$ induced by $A\\to B\\to B_s=B[1/s]$ is etale."
 },
 {
  "step": 3,
  "node": "def-weil-pbc-henselian-terminology",
  "quote": "A pair $(A,I)$ consisting of a commutative ring and an ideal is *henselian*\nif, for every finite $A$-algebra $B$, every idempotent of $B/IB$ lifts\nuniquely to an idempotent of $B$. A local ring is *henselian* when its\nmaximal-ideal pair is henselian, and *strictly henselian* when it is\nhenselian and its residue field is separably closed. For\n$T=\\operatorname{Spec}A$ and an ideal $I$, write\n$T_0=\\operatorname{Spec}(A/I)$ [def-weil-affine-spectrum] for the closed subscheme."
 },
 {
  "step": 4,
  "node": "def-weil-pbc-henselization-at-prime",
  "quote": "Let $A$ be a commutative ring and $\\mathfrak p\\subset A$ a prime ideal. A commutative ring $H$ with an $A_{\\mathfrak p}$-algebra structure and a henselian-local-ring structure is a *henselization of $A_{\\mathfrak p}$* if the structural map $A_{\\mathfrak p}\\to H$ is local and, for every henselian local ring $T$ and every local map $g:A_{\\mathfrak p}\\to T$, there is a unique local map $h:H\\to T$ with $h\\circ(A_{\\mathfrak p}\\to H)=g$."
 },
 {
  "step": 4,
  "node": "lem-weil-pbc-map-into-henselian-colimit",
  "quote": "Let $R\\to S$ be a ring homomorphism with $S$ a henselian local ring [def-weil-pbc-henselian-terminology] with maximal ideal $\\mathfrak m_S$, and put $\\mathfrak p=$ the preimage of $\\mathfrak m_S$ in $R$. Let $A$ be an $R$-algebra which is a filtered colimit [def-weil-pbc-category-colimit] of $R$-algebras $A_i$ with $\\operatorname{Spec}A_i\\to\\operatorname{Spec}R$ etale [def-weil-etale-morphism] (in particular $A$ may be a single etale $R$-algebra), let $\\mathfrak q\\subset A$ be a prime lying over $\\mathfrak p$, and let $\\tau:\\kappa(\\mathfrak q)\\to S/\\mathfrak m_S$ be a homomorphism of $\\kappa(\\mathfrak p)$-algebras. Then there is exactly one homomorphism of $R$-algebras $f:A\\to S$ with $f^{-1}(\\mathfrak m_S)=\\mathfrak q$ and inducing $\\tau$ on residue fields (that is, $A\\to S\\to S/\\mathfrak m_S$ equals $A\\to A/\\mathfrak q\\to\\kappa(\\mathfrak q)\\xrightarrow{\\tau}S/\\mathfrak m_S$)."
 },
 {
  "step": 5,
  "node": "lem-weil-pbc-map-into-henselian-colimit",
  "quote": "Let $R\\to S$ be a ring homomorphism with $S$ a henselian local ring [def-weil-pbc-henselian-terminology] with maximal ideal $\\mathfrak m_S$, and put $\\mathfrak p=$ the preimage of $\\mathfrak m_S$ in $R$. Let $A$ be an $R$-algebra which is a filtered colimit [def-weil-pbc-category-colimit] of $R$-algebras $A_i$ with $\\operatorname{Spec}A_i\\to\\operatorname{Spec}R$ etale [def-weil-etale-morphism] (in particular $A$ may be a single etale $R$-algebra), let $\\mathfrak q\\subset A$ be a prime lying over $\\mathfrak p$, and let $\\tau:\\kappa(\\mathfrak q)\\to S/\\mathfrak m_S$ be a homomorphism of $\\kappa(\\mathfrak p)$-algebras. Then there is exactly one homomorphism of $R$-algebras $f:A\\to S$ with $f^{-1}(\\mathfrak m_S)=\\mathfrak q$ and inducing $\\tau$ on residue fields (that is, $A\\to S\\to S/\\mathfrak m_S$ equals $A\\to A/\\mathfrak q\\to\\kappa(\\mathfrak q)\\xrightarrow{\\tau}S/\\mathfrak m_S$)."
 },
 {
  "step": 5,
  "node": "def-weil-pbc-henselization-at-prime",
  "quote": "Let $A$ be a commutative ring and $\\mathfrak p\\subset A$ a prime ideal. A commutative ring $H$ with an $A_{\\mathfrak p}$-algebra structure and a henselian-local-ring structure is a *henselization of $A_{\\mathfrak p}$* if the structural map $A_{\\mathfrak p}\\to H$ is local and, for every henselian local ring $T$ and every local map $g:A_{\\mathfrak p}\\to T$, there is a unique local map $h:H\\to T$ with $h\\circ(A_{\\mathfrak p}\\to H)=g$."
 },
 {
  "step": 6,
  "node": "def-weil-pbc-category-colimit",
  "quote": "Let $I$ be a small category and $D:I\\to\\mathcal C$ a functor (a diagram). A *cocone* on $D$ is an object $L$ with morphisms $\\iota_i:D(i)\\to L$ such that $\\iota_j\\circ D(a)=\\iota_i$ for every $a:i\\to j$. A *colimit* of $D$ is a cocone $(\\varinjlim_ID,(\\iota_i))$ such that for every cocone $(M,(\\mu_i))$ there is exactly one morphism $u:\\varinjlim_ID\\to M$ with $u\\circ\\iota_i=\\mu_i$ for all $i$; it is unique up to unique isomorphism, and one is chosen when it exists. In particular a family of morphisms $\\mu_i:D(i)\\to M$ compatible with the transition maps induces the *canonical map* $\\varinjlim_ID\\to M$. The colimit is *filtered* when $I$ is a filtered category (Stacks, Categories, Definition 002V: $I$ has at least one object, every two objects map to a common object, every two parallel arrows are equalized by some arrow; a nonempty directed poset is filtered)."
 },
 {
  "step": 6,
  "node": "def-weil-pbc-ind-etale-algebra",
  "quote": "Let $A$ be a commutative ring and let $B$ be an $A$-algebra. The\n$A$-algebra $B$ is *ind-etale* if it is a filtered colimit of etale\n$A$-algebras of finite presentation [def-weil-pbc-scheme-conventions]. It is\n*ind-Zariski* if such a presentation can be chosen with terms finite products\nof localizations $A_f$. The corresponding affine scheme $\\operatorname{Spec}B$\nis an inverse limit of affine etale schemes, with affine transition maps. The\nring map $A\\to B$ is *weakly etale* when the induced map\n$\\operatorname{Spec}B\\to\\operatorname{Spec}A$ is weakly etale in\n[def-weil-pbc-scheme-conventions]; equivalently, $B$ is flat as an $A$-module\nand is flat as a module over $B\\otimes_A B$ via the multiplication map\n$B\\otimes_A B\\to B$."
 },
 {
  "step": 7,
  "node": "lem-weil-pbc-ind-etale-stability",
  "quote": "The classes of ind-etale [def-weil-pbc-ind-etale-algebra] and ind-Zariski\nmaps are stable under base change, composition, and filtered colimits. An\nind-etale map is weakly etale. If $B,C$ are ind-etale over $A$, every\n$A$-algebra map $B\\to C$ is ind-etale. Weakly etale maps are stable under\ncomposition and base change."
 }
]
```
