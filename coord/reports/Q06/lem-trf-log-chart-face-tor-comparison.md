# Worker report — Q06

1. Files written: `dag/nodes/sec-trace-formula/lem-trf-log-chart-face-tor-comparison.json` (item, split; statement unchanged), plus four statement-only nodes, each status `unsplit`, no proof steps and no proof dependencies:
   - `lem-trf-chart-face-split-coordinates` — statement; no exact Mathlib match after five logged searches (LeanFinder twice, LeanSearch, Loogle, grep).
   - `lem-trf-monoid-face-localization-ideal-tensor` — statement; no exact Mathlib match after five logged searches (LeanFinder twice, LeanSearch, Loogle, grep).
   - `lem-trf-split-unit-group-ideal-tensor` — statement; no exact Mathlib match after five logged searches (LeanFinder twice, LeanSearch, Loogle, grep).
   - `lem-trf-monoid-unit-twist-ideal-tensor` — statement; no exact Mathlib match after five logged searches (LeanFinder twice, LeanSearch, Loogle, grep).
   `citations.json` records an exact quotation from the statement of each node cited in each parent step. The other sandbox files are local reading/search material and are not delivery changes.
2. Attachments: none. I searched the upstream `lean/WeilConjectures/` by the blueprint tag, declaration and chart/Tor concepts. The existing `lean/Sheaf/TraceFormula/LogChartFaceTorComparison.lean` theorem `AlgebraicGeometry.logChart_face_tor_comparison` ends in `sorry`; its real helper definitions are not a finished proof of this item. No Lean file was edited and no compiler or build was run.
3. WANTED: none. ILO and Stacks are available locally. The explicit chart and tensor comparisons are agent algebraic expansions in the same places as the returned proof, not a claim that ILO prints these auxiliary statements verbatim.
4. The returned defect was excessive proof work in one node. The sandbox initially held only dispatcher briefs, with no item, report or searches to reuse. The required initial dry run returned `FAILED: no node files under .../dag/nodes/`. I copied the current live returned node and retained its entire statement, citations, existing Mathlib searches, blueprint ancestry and Lean/review metadata. The old eight steps are reproduced below, without shortening, so their arguments remain recoverable. The parent now assembles four independent arguments and the already existing Tor-kernel lemmas. Its proof is 2062 characters (below 3000); none of its five steps exceeds 2000 characters.
5. Nothing mathematical is left unfinished in the parent assembly. The four new proof obligations intentionally remain unsplit for other workers. No statement dispute was found. The unit/chapter route and target statements were not changed.

## Allocation of the returned argument

- Old steps 1 and 2, and the monoid-ideal part of old step 4, are now the conclusions of `lem-trf-chart-face-split-coordinates`: extension of both structural and log charts, explicit section splitting and inverse, chart-pushout coordinates, the unique unit homomorphism at the log-monoid level, surjectivity onto the sharpening, and equality of localized ideals with inverse images. This is one local monoid/chart coordinate argument, with no Tor or tensor conclusion.
- Old step 5 and the monomial-basis/extension clause of old step 4 are in `lem-trf-monoid-face-localization-ideal-tensor`. Its statement specifies the fraction inverse, independence of representatives, the extension ideal, multiplication square and coefficient naturality.
- Old step 6 is in `lem-trf-split-unit-group-ideal-tensor`. Its statement works for arbitrary monoid Q and abelian group G, records the inverse inclusion map, the extension ideal, the evaluation character and multiplication square.
- Old step 7 is in `lem-trf-monoid-unit-twist-ideal-tensor`. It explicitly includes both coefficient-extension isomorphisms and inverses, the automorphism of A[Q], evaluation identity, multiplication square, and absence of any flatness assumption.
- Old step 3 is already exactly the conjunction of the existing Tor symmetry and ideal-kernel naturality statements; it stays as their short application in parent step 5. Old step 8 is the composition and restriction to kernels in that same step. Its change-of-rings directions and fixed-choice naturality are retained. The generator formula in parent step 5 also matches the existing Lean statement.

These four statements have respectively 1932, 1525, 1471 and 1634 characters. They divide the work into comparable independent arguments, rather than moving the whole theorem into one node. No new node states the whole Tor comparison. The explicit re-split instruction supersedes the earlier decision to keep these multi-calculation arguments as elementary steps.

## Not duplicates

I searched the whole DAG statements, the whole blueprint with `tools/blueprint_refs.py search`, and the upstream project source before writing the four new files. Searches included `unit twist`, `face localization`, `chart pushout`, `sharp chart`, `group factor`, `sharp quotient`, `monomial ideal`, and `monoid ring`. Broader monoid/localization/tensor searches were read as well. No blueprint node states these four comparisons. The nearest blueprint ancestor from the tool is `lem-trf-local-term-locality`; each new node records the existing ancestry with this item prepended to `via`, and identifies the exact algebraic subargument of the ILO input. The parent keeps its already specified place and `same_as: []`.

- lem-trf-chart-face-split-coordinates vs lem-trf-fs-face-sharpening: the existing statement proves fineness, saturation and the unit subgroup of the localization/quotient; it does not compare log-chart pushouts, two chart lifts, their unit character, a chosen section or images of ideals.
- lem-trf-chart-face-split-coordinates vs lem-trf-face-localization-fs: the existing statement proves fineness, saturation and group completion of a face localization, without any charts or ideal-coordinate comparison.
- lem-trf-chart-face-split-coordinates vs lem-per-integral-monoid-unit-pushout: the existing statement gives injectivity and cancellation for an arbitrary unit pushout and its equality criterion, without the specified sharp-chart coordinate isomorphisms, section or image-ideal formula.
- lem-trf-chart-face-split-coordinates vs lem-trf-associated-log-universal-stalks: the existing statement concerns the associated log sheaf, its universal property, stalk and restriction. It does not compare two sharp coordinate systems or compute localized monoid ideals.
- lem-trf-monoid-face-localization-ideal-tensor vs lem-trf-toric-monoid-comparison: that node concerns equivariant ideals and normalized blowups over a field; this is a tensor isomorphism over arbitrary A with explicit fraction inverse and multiplication square, without a field or flatness assumption.
- lem-trf-monoid-face-localization-ideal-tensor vs lem-weil-pbc-localized-pushout-tensor: that node asserts a ring pushout followed by localization; it does not identify tensors of an arbitrary monomial ideal or give the fraction inverse.
- lem-trf-monoid-face-localization-ideal-tensor vs lem-pc-tor-localization-denominators: that node obtains denominator representatives in Tor for coefficient localization; this concerns the monomial ideal tensor and changes the base monoid ring.
- lem-trf-split-unit-group-ideal-tensor vs lem-trf-fs-face-sharpening: no tensor or group-evaluation assertion is present in the existing sharpening statement; the new tensor lemma does not require fs hypotheses.
- lem-trf-monoid-unit-twist-ideal-tensor vs lem-per-completed-invertible-kummer-monoid-extension: that node assumes a unit character and a completed local presentation to compute a Kummer extension; it does not construct the twisted ideal-tensor isomorphism or the coefficient-extension square.
- Each new node vs lem-trf-log-chart-face-tor-comparison: the existing parent states the first-Tor result. The new nodes isolate coordinate or ideal-tensor arguments strictly below it and have no dependency back to the parent.

The new nodes cite ILO contextual places and carry no new Stacks-tag source shared with another node. Stacks 00M3 and 00M6 occur in the parent only, where the existing nodes are reused.

## Mathlib searches and candidate inspection

Every new node has five actual search records with the same tool and query text as `searches.jsonl`; the full outputs are retained as `search-<id>-<index>.txt`. All twenty services/commands completed successfully; no unavailable query is presented as a no-match. Both semantic phrasings for each node were read. The inherited parent's historical searches were retained, not silently recreated or claimed as new Q06 searches.

The chart-coordinate searches returned unit homomorphisms, number-field logarithmic embeddings and general monoid pushouts, not logarithmic-chart coordinates. The localization searches returned `IsLocalization.moduleTensorEquiv`, `moduleLid`, `tensorProduct_isLocalizedModule`, `mk'_tmul` and generic base-change results. I read `Mathlib/RingTheory/Localization/BaseChange.lean`, especially the module comparison statements and localization hypotheses: they do not themselves establish the monoid-ring/monomial-ideal localization identification or its explicit fraction formula. The split-group and twist searches returned `MonoidAlgebra.tensorEquiv`, `scalarTensorEquiv`, their monomial formulas and representation-theory results. I read `Mathlib/RingTheory/TensorProduct/MonoidAlgebra.lean` (including lines 105--115 and 145--164): these compare whole monoid algebras under base change or product, not the arbitrary ideal tensors, evaluations and commuting multiplication squares in the new statements. None of the four new statements is a one-line specialization of these hits. The findings and full hit names are recorded rather than marking a generic piece of infrastructure as the whole lemma.

## Review by Q06

I read ILO Expose VI 1.1--1.2 (printed p. 69), 3.7(a) (p. 75), VIII 3.1.1--3.1.5 (pp. 98--99), and the proof of VIII 3.4.3 (p. 110). These are the source context for the item and all four new algebraic obligations. VI gives the log/characteristic notions and the unit-group splitting context; VIII gives sharpening/localization and the use of first Tor for monoid ideals. They do not explicitly print the auxiliary tensor inverses: their derivations remain agent-written and are reproduced from the returned proof below. I also read Stacks `algebra.tex`, Tag 00CX (`algebra-lemma-tensor-product`), 00M3 (`algebra-lemma-tor-left-right`) and 00M6 (`algebra-remark-Tor-ring-mod-ideal`). No SGA source is used.

For parent step 1 I checked the new coordinate statement against the actual chart definition in `def-trf-fs-log-blowup` and the complete statement of `lem-trf-fs-face-sharpening`. Fs log stalks are integral; the chart gives exactly the pushout hypothesis. The two characteristic identifications are stipulated equal by the parent, and the section is stipulated to be a monoid homomorphism. Thus the new node gives every item taken from it: the splitting, c,v,u, H_x and H_F. The unit character is unique by equality in the integral log monoid, not merely by equality c=ub in A; if b(q)=0, ring equality alone would not give uniqueness. Neither this node nor the assembly assumes log regularity or invokes a sharp-chart existence theorem.

For step 2 I read the entire localization-tensor statement. The parent has an integral P because it is fs, and alpha sends F to units by its definition. The localized ideal in this statement is exactly the H_F given by step 1; the extension-ideal clause avoids taking an unstated comparison of ideals. The inverse formula uses alpha(f) inverse, so it has the required invertibility without a nonzero-divisor assumption on other monomials. The new statement expressly gives the multiplication square and coefficient naturality.

For step 3 I checked that the group is precisely G=F^gp and the split action is c(q)v(g), not just c(q). The input ideal is H_x times the whole group, as proved by the coordinate node. The new statement gives the isomorphism, inverse inclusion and multiplication square, including the ideal extension along Q to Q times G. The inverse direction is essential when later applying change of rings; the parent now names it explicitly.

For step 4 I checked the statement of the unit-twist node against c(q)=u(q)b(q), including its coefficient-extension maps and the evaluation identity. Multiplication by u on monomials has the direction from the c-action to the b-action. Its inverse uses u inverse. The twist is over A[Q]; it would not in general be a ring automorphism of Z[Q]. The new node explicitly provides the A[K] ideal and the coefficient-extension isomorphisms, so no flatness over Z is imported implicitly.

For step 5 I reopened the full statements of `lem-weil-pbc-tor-symmetry` and `lem-weil-pbc-tor-ideal-kernel-naturality`. Symmetry gives the required order of arguments, and part (a) identifies each first Tor with exactly the multiplication kernel. Part (b) states the semilinear change-of-rings boundary identity, including the extension-ideal requirement. Those ideals are supplied in the preceding new statements. Because each factor is an invertible map over the identity of the multiplication target A, restricting the composite and its inverse gives inverse maps of kernels. The generator formula agrees with the old proof and the existing Lean statement. The naturality clauses of the new nodes specify compatible coefficient/log data, and the existing boundary identity gives the induced natural Tor comparison. This makes no independence claim for different s or b. Exact statement quotations for all six citations across the five steps are in citations.json. The two off-unit general Tor lemmas remain the already accepted tool uses, with the earlier explanations retained in split_report.

I tested the statements on H empty (zero ideal tensors and zero Tor), H=P (multiplication identifies the ideal tensors with A and Tor is zero), H meeting F (the localized and sharp ideals are whole), P a group (Q=0), P trivial, F={0}, G=0, u=1, and an arbitrary monoid Q with K empty or whole. Localization and the tensor maps also permit the zero coefficient ring. For P=N and alpha(1)=i t in C[[t]], with b(1)=t, the twist uses u(1)=i and really needs A coefficients. No statement asserts units can be cancelled in A against a vanishing b(q), and no step requires A to be flat over Z. I checked every new statement introduces all its objects and hypotheses, has no proof sketch, and cites or explicitly defines its notions. I checked all existing candidate overlaps above, the lack of cycles back to the parent, and the preservation of all old argument content. I corrected the former packaging only: the parent's mathematical statement is unchanged.

## Returned proof retained verbatim

The complete previous argument is retained here as the proof material for future workers. Its statement-only descendants specify its intermediate conclusions and formulas; they carry no proof steps themselves.

### Original step 1

Write $Q=P_x$, $G=F^{\rm gp}$. Since a product in a commutative ring is a unit exactly when both factors are units, $F$ is a face. Extend $\alpha$ to $P_F$ by $\alpha(p-f)=\alpha(p)\alpha(f)^{-1}$. The face-sharpening lemma gives $P_F^\times=G$ and the sharp fs quotient $Q$, with equality of quotient classes exactly difference by $G$. For the given section $s$, the maps $(q,g)\mapsto s(q)+g$ and $r\mapsto(\bar r,r-s(\bar r))$ are inverse monoid homomorphisms $Q\oplus G\simeq P_F$: the difference in the inverse belongs to $G$ by that equality criterion. Put $v(g)=\alpha(g)\in A^\times$ and $c(q)=\alpha(s(q))$.

Cited nodes: lem-trf-fs-face-sharpening.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; Expose VIII, 3.1.1--3.1.5, printed pp. 98--99; explicit splitting from the given section (agent).

### Original step 2

Let $M$ be the log stalk. The chart pushout is $M=P\oplus_F A^\times=P_F\oplus_G A^\times$: adjoining inverses to $F$ does not alter a pushout in which $F$ already maps to units. The given splitting thus identifies $M$ with $Q\oplus A^\times$. More particularly the sharp chart $b$, whose characteristic map is the specified identity, gives the isomorphism $(q,a)\mapsto b_M(q)a$ from $Q\oplus A^\times$ to $M$; here $b_M$ denotes the lift of the chart to $M$, not merely its image in $A$. In these coordinates the image of $s(q)$ is uniquely $(q,u(q))$. Multiplication in $M$ implies $u(q+q')=u(q)u(q')$ and $u(0)=1$. Applying the structural map to $A$ gives $c(q)=u(q)b(q)$. This uses the given charts, not an existence theorem requiring log regularity.

Cited nodes: def-trf-fs-log-blowup.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; Expose VI, 1.1--1.2, printed p. 69, and 3.7(a), printed p. 75; explicit comparison of the two chart pushouts (agent).

### Original step 3

For any commutative ring $T$, ideal $L$ and $T$-module $B$, first apply Tor symmetry and then part (a) of the ideal-kernel lemma with $M=B$, $R=T$, $I=L$. This identifies $\operatorname{Tor}_1^T(T/L,B)$ with $\ker(\mu_{T,L,B}:L\otimes_T B\to B)$, where $\mu(\ell\otimes a)=\ell a$. Part (b) says precisely that the change-of-rings maps on these kernels are the restrictions of the maps on ideal tensors induced by the ring and module maps. We shall construct invertible maps of these ideal tensors commuting with $\mu$, so their restrictions give the desired first-Tor comparison.

Cited nodes: lem-weil-pbc-tor-symmetry, lem-weil-pbc-tor-ideal-kernel-naturality.

Source: literature/stacks-project/algebra.tex; Tags 00M3 (Tor symmetry) and 00M6 (ideal-kernel description); the cited naturality node states the semilinear change-of-rings compatibility explicitly.

### Original step 4

Put $H_F=H+P_F=\{h-f:h\in H,f\in F\}$. The map $P\to Q$ is surjective, since $\overline{p-f}=\bar p$; hence the image $H_x$ is an ideal of $Q$. Moreover $H_F$ is the inverse image of $H_x$: if $\bar r=\bar h$ for $h\in H$, then $r-h\in G$, and $H_F$ is stable under addition by $G$ (both signs are units in $P_F$). The converse follows by taking quotient classes. Under step 1 this says $H_F=H_x\oplus G$. The ideals $\mathbf Z[H]$, $\mathbf Z[H_F]$ and $\mathbf Z[H_x]$ have, by definition of a monoid ring, the indicated monomials as their additive bases; these bases also describe their extension ideals.

Cited nodes: (none; elementary step).

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; Expose VIII, 3.1.1--3.1.2, printed p. 98, and proof of 3.4.3, printed p. 110; explicit ideal calculation (agent).

### Original step 5

Localization induces $\lambda:\mathbf Z[H]\otimes_{\mathbf Z[P]}A\to\mathbf Z[H_F]\otimes_{\mathbf Z[P_F]}A$, $z^h\otimes a\mapsto z^h\otimes a$. Its inverse is $z^{h-f}\otimes a\mapsto z^h\otimes\alpha(f)^{-1}a$, extended additively. If $h-f=h'-f'$, integrality of $P$ gives $h+f'=h'+f$; tensor balancing gives equality of the two proposed values by using the common denominator $\alpha(f)\alpha(f')$. Balancing a monomial $p-f'$ transfers the scalar $\alpha(p)\alpha(f')^{-1}$ on either side, so the inverse is well-defined over $\mathbf Z[P_F]$. The two displayed maps are inverse on generators, are $A$-linear, and commute with multiplication to $A$, since $\alpha(h-f)=\alpha(h)\alpha(f)^{-1}$.

Cited nodes: def-weil-pbc-module-tensor-product.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; Expose VIII, proof of 3.4.3, printed p. 110; localization comparison expanded by tensor generators and relations (agent); tensor universal property: Stacks 00CX.

### Original step 6

Using $H_F=H_x\oplus G$, the splitting induces $\sigma:\mathbf Z[H_F]\otimes_{\mathbf Z[P_F]}A\to\mathbf Z[H_x]\otimes_{\mathbf Z[Q]}A_c$, $z^{s(q)+g}\otimes a\mapsto z^q\otimes v(g)a$; $A_c$ denotes $A$ with the action $z^p\mapsto c(p)$. The inverse sends $z^q\otimes a$ to $z^{s(q)}\otimes a$. Balancing by $s(p)+g'$ on the source transfers exactly $c(p)v(g')$, while on the target balancing by $p$ transfers $c(p)$ and the formula transfers $v(g')$. Thus both maps descend; their composites are identities since $z^{s(q)+g}\otimes a=z^{s(q)}\otimes v(g)a$. The multiplication maps commute, both giving $c(q)v(g)a$.

Cited nodes: def-weil-pbc-module-tensor-product.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; Expose VI, 3.7(a), printed p. 75; explicit split group-factor elimination on ideal tensors (agent); tensor relations: Stacks 00CX.

### Original step 7

The unit twist gives $\rho:\mathbf Z[H_x]\otimes_{\mathbf Z[Q]}A_c\to\mathbf Z[H_x]\otimes_{\mathbf Z[Q]}A_b$, $z^q\otimes a\mapsto z^q\otimes u(q)a$. Indeed the balancing relation for $p\in Q$ is respected because $u(q+p)b(p)=u(q)c(p)$. Replacing $u$ by $u^{-1}$ gives the inverse, and $b(q)u(q)a=c(q)a$ proves compatibility with multiplication to $A$. To interpret this as the stated ring twist, use the generator isomorphisms $\mathbf Z[H_x]\otimes_{\mathbf Z[Q]}A_d\simeq A[H_x]\otimes_{A[Q]}A_d$ ($d=b,c$), whose inverses send $(a_0z^q)\otimes a$ to $z^q\otimes a_0a$. The automorphism $\tau_u:A[Q]\to A[Q]$, $z^q\mapsto u(q)z^q$, preserves $A[H_x]$ and satisfies $c=b\circ\tau_u$. Its ideal-tensor map is exactly $\rho$ in these presentations. The generator formulas prove these identifications without assuming $A$ flat over $\mathbf Z$.

Cited nodes: def-weil-pbc-module-tensor-product.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; Expose VI, 3.7(a), printed p. 75, and Expose VIII, proof of 3.4.3, printed p. 110; explicit coefficient extension and unit-twist calculation (agent); tensor relations: Stacks 00CX.

### Original step 8

The composite $\rho\sigma\lambda$ is an $A$-linear isomorphism of the two ideal tensors and gives the identity on their multiplication targets $A$. Restrict it to the kernels and apply step 3 at $T=\mathbf Z[P]$, $L=\mathbf Z[H]$ and at $T=\mathbf Z[Q]$, $L=\mathbf Z[H_x]$. This is the asserted Tor isomorphism, induced by localization, the splitting and the twist: for the splitting use the inverse of the change-of-rings map for $\mathbf Z[Q]\to\mathbf Z[P_F]$, while the other maps go forward. The coefficient extensions in step 7 also give isomorphisms on kernels by their explicit generator maps. Naturality follows because every displayed map is given on pure tensors by the same formulas after a compatible coefficient-ring map, and the connecting identifications are natural as stated in the ideal-kernel lemma. The choices $s,b$ are fixed throughout; no independence of these choices is asserted.

Cited nodes: lem-weil-pbc-tor-symmetry, lem-weil-pbc-tor-ideal-kernel-naturality.

Source: literature/stacks-project/algebra.tex; Tag 00M6 and the semilinear naturality in lem-weil-pbc-tor-ideal-kernel-naturality; assembly of the explicit maps (agent).
