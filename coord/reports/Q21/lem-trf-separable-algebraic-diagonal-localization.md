# Repair: lem-trf-separable-algebraic-diagonal-localization

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-separable-algebraic-diagonal-localization.json`: unchanged statement, four-step assembly, 2336 proof-text characters (below 3000).
- `dag/nodes/sec-trace-formula/lem-trf-separable-tensor-polynomial-presentation.json`: statement, unsplit; no complete Mathlib match. This is the finite-support descent and compatible polynomial presentation argument.
- `dag/nodes/sec-trace-formula/lem-trf-separable-root-polynomial-annihilator.json`: statement, unsplit; no complete Mathlib match. This is the divided-difference, nonvanishing, and evaluated annihilator argument.
- `citations.json`: one entry per step/node citation, with verbatim statement excerpts.
- `report.md`: this report, including the complete old argument and its distribution below.

## Attachments

None. The tag search and notion searches in `lean/WeilConjectures/` found no exact project declaration. `lean/Sheaf/FieldTheory/SeparableAlgebraicDiagonalLocalization.lean:50` states the parent but its proof ends in `sorry`. Its docstring carries the same seven steps as the current DAG. No Lean file was edited, and no compiler or Lake command was run.

## WANTED

None. All sources needed are present under `literature/`.

## What was wrong and what changed

The returned seven-step proof is correct but too large to be one worker's item under the human's re-split decision. The sandbox initially contained only dispatcher marker files: no node files, report, or prior searches. I read the returned proof from the current read-only repository rather than discarding an interrupted repair. I retained the parent's statement byte for byte and all its source, audit, Lean, blueprint and historical review fields. Its original Mathlib searches remain unchanged. The two new nodes have new logged searches, empty proof/proof_deps, null proof_origin and status unsplit.

The two new nodes are separate arguments, not clauses of the parent localization conclusion. The presentation node makes no localization or kernel-annihilation assertion and applies to every tensor, not just a kernel element. The annihilator node is a polynomial result in any commutative algebra over a field, with no tensor product or localization in its hypotheses. They have comparable proof workloads: old steps 2-3 plus the tensor relation P(t)=0, versus old steps 4-5 plus the evaluated product calculation of step 6. Each can be assigned to another worker independently. The remaining denominator construction and fraction isomorphism stay explicit in the parent.

## New nodes and intended arguments

For the presentation node I read Stacks `algebra.tex`, Tag 0C2X, `lemma-separable-algebraic-diagonal`, including both finite and general paragraphs. I also read `fields.tex`, Tags 09GH (`lemma-algebraic-finitely-generated`), 030N (`lemma-primitive-element`), and 09G1 (`lemma-field-extension-generated-by-one-element`). This node exposes exactly the finite support needed in the infinite extension case: choose a finite tensor sum, form E from its right factors, apply finite algebraic generation and the finite separable primitive element theorem, and use polynomial representatives in k(alpha). The evaluations F(t)=x and P(t)=0 require balancing the k-coefficients across the tensor sign. Mapping the Bezout identity UP+VP'=1 coefficientwise to L proves separability of the mapped P; this is included in the statement so the parent does not hide that change of coefficients. The finite-dimensional notion has its definition citation.

For the annihilator node I read the factorization and Q(alpha) nonzero sentence in Stacks Tag 0C2X. Its explicit divided-difference statement preserves the original worker's expansion of the source's omitted calculation: the finite geometric-sum identity gives G-G(alpha)=(T-alpha)D_G; evaluation gives D_G(alpha)=G'(alpha); evaluating the separability Bezout identity gives nonvanishing. For t with P(t)=0, the ring-homomorphism evaluation then gives Q(t)F(t)=P(t)H(t)=0. Its statement gives every identity and introduces R, its coefficient map, alpha, P, G, F and t. It assumes no domain property for R and no finiteness of the field.

## Search record and existing material

Whole-DAG searches were by Tag 0C2X, finite-support/polynomial representative, separable annihilation, divided difference, and complementary factor. I read every same-tag statement listed below. Whole-blueprint searches with `tools/blueprint_refs.py search` included `polynomial representative`, `separable polynomial`, `tensor square`, `annihilator`, `primitive element` and `separable algebraic`. No blueprint node states either new lemma. The existing finite algebraic generation, primitive-element and minimal-polynomial-quotient nodes supply inputs to the future proof of the presentation node, not the combined presentation itself. The tensor-kernel-factorization node is a module factorization criterion, not this tensor-square calculation.

Every recorded new-node query was run through the prescribed msearch.py command; `searches.jsonl` contains the actual tool, query, status and hits. Both nodes have LeanFinder queries in two phrasings, Loogle, grep, and a LeanSearch attempt. LeanSearch for the presentation node was unavailable, recorded as unavailable. The annihilator LeanSearch succeeded and returned separability, coprimality, and squarefreeness results; none gives the full assertion.

I read Mathlib PrimitiveElement.lean:209 and IntermediateField/Adjoin/Basic.lean:396,590: these are the familiar finite-stage inputs already recorded as existing DAG leaves. Algebra.Generators.baseChange presupposes algebra generators; purely-inseparable tensor power results have the opposite separability assumptions. Neither constructs a single finite separable stage with all compatible evaluation certificates for an arbitrary tensor. I read Separable.lean:136-147 and Minpoly/MinpolyDiv.lean:35-85: derivative nonvanishing and minimal-polynomial-quotient identities cover parts of the second node, but do not give its explicit divided difference for arbitrary G and its annihilator action in arbitrary commutative L-algebras. No hit or one-line specialization states the entire new node. No Mathlib leaf is claimed.

## Review by Q21

I checked the item against Stacks Tag 0C2X, both paragraphs, with its seven old steps open. The statement and its hypotheses are unchanged: arbitrary separable algebraic k1/k, all characteristics, no finite-degree hypothesis. Only the finitely many right factors of an individual tensor enter a finite subextension. The assembly does not assume that maps between tensor products of subfields are injective.

Step 1 uses the actual tensor-pushout statement: clause (1) supplies the commutative ring, its unit, and coefficient inclusion; clause (2) with f=g=id supplies the algebra homomorphism mu. I reread these clauses rather than relying on the module tensor-product definition for multiplication. The localization definition explicitly defines multiplicative subsets. Thus S=mu^{-1}(k1 minus zero) is multiplicative, mu(s) is invertible, and mu is surjective by c tensor 1. No non-elementary fact is used silently here.

Step 2 uses precisely the new presentation statement: its hypotheses are the original separable algebraic field extension and an arbitrary x in its tensor square, both available. Its conclusion explicitly supplies separable bar P, bar P(alpha)=bar P(t)=0, F(t)=x and F(alpha)=mu(x). The kernel hypothesis therefore gives F(alpha)=0. These are statement clauses, not material borrowed from a proof. The choice n=0 remains valid for x=0.

Step 3 uses precisely the new annihilator statement with L=k1, R=k1 tensor_k k1, the coefficient homomorphism from step 1, P=bar P, and alpha,t,F from step 2. All four polynomial hypotheses hold explicitly. Its Q(alpha) nonzero and Q(t)F(t)=0 conclusions are quoted verbatim in citations.json. The coefficient calculation mu(Q(t))=Q(alpha) uses only that mu is a ring homomorphism fixing the left coefficients and sends t to alpha. Thus s=Q(t) is in the chosen S and sx=0. The new lemma has no nonzero/domain hypothesis on R that would need extra checking.

Step 4 uses the actual fraction construction of the localization definition: r/s=r'/s' iff some u in S kills s'r-sr', the addition formula, and the scalar multiplication formula with M=R. Applying mu cancels its nonzero denominator images, proves well-definedness, and gives a ring map. Surjectivity uses (c tensor 1)/1. For injectivity, the preceding step kills the numerator r by u in S, which is exactly the fraction relation to zero. Thus the parent proves the localization isomorphism as well as all three explicit conditions, without an unquoted exactness theorem.

I checked B1-B10: both children are self-contained statement-only nodes; TeX has single decoded backslashes; sources specify Tag 0C2X and its label; no unrun query or unsupported Mathlib match is claimed; ancestor and via lists use the existing blueprint chain; no project attachment is finished. I checked C1-C8 with every used node statement open, verbatim quotes for every use, and proof_deps equal to their union. The new nodes inherit the parent's unit and no off-route statement is used. I checked D1-D5: the two children give different mathematical arguments and neither says the localization theorem or simply repeats one of its three conditions; the old proof is preserved below, not shortened away. All parent steps are under 2000 characters and their sum is below 3000. I checked E1-E7: no missing separability, finite-stage, coefficient-map or root hypothesis, no wrong tensor factor, and no unexplained transport or denominator clearing remains.

Small cases: for k1=k one may take alpha=0, P=T, F constant, Q=1; if x lies in the kernel it is zero, so s=1 works. For x=0, n=0, E=k and alpha=0 work with the same P. For C/R with alpha=i, P=T^2+1 and Q=T+i, Q(i)=2i and (1 tensor i+i tensor 1)(1 tensor i-i tensor 1)=0. In F4/F2, P=T^2+T+1 and a root alpha give Q=T+alpha+1 and Q(alpha)=1, checking characteristic two. An infinite algebraic separable extension such as Qbar/Q is handled one finite tensor support at a time. In the polynomial lemma F=0 makes H=0, linear P yields a nonzero constant Q, and the zero R makes the evaluated identities 0=0. A nonzero constant P cannot have alpha as a root. The inseparable P=(T-alpha)^p would have Q(alpha)=0, confirming the separability hypothesis cannot be dropped.

## Preservation map for every old argument

- Old step 1 remains parent step 1 verbatim (688 characters).
- Old step 2, finite-support subextension, its finiteness, inherited separability and primitive element including the empty sum, is the presentation node's finite-stage assertion.
- Old step 3, minimal P, representatives g_i, F and the coefficientwise tensor evaluation, is the presentation node's remaining data and identities.
- Old step 4, the explicit finite geometric sum, both factorizations and Q(alpha)=P'(alpha), is the annihilator node's D_G formula and identities.
- Old step 5, evaluation of the separability Bezout identity and its validity in positive characteristic, is the annihilator node's nonvanishing assertion and intended argument recorded above.
- Old step 6 is distributed without loss: P(t)=1 tensor P(alpha)=0 belongs to the presentation node; Q(t)F(t)=P(t)H(t)=0 belongs to the annihilator node; mu(Q(t))=Q(alpha), membership in S, and sx=0 remain parent step 3. No assumption on the degree of k1/k was added.
- Old step 7 remains parent step 4 verbatim except for replacing its reference to step 6 by step 3. The fraction map, well-definedness calculation, ring operations, surjectivity, numerator annihilation and injectivity are all retained.

## Old proof, retained verbatim

### Old step 1

Put $R=k_1\otimes_k k_1$, the commutative ring with $(a\otimes b)(a'\otimes b')=aa'\otimes bb'$ and unit $1\otimes1$ of [lem-weil-pbc-algebra-tensor-pushout-universal-property] (1); by (2) of the same node, applied to $f=g=\mathrm{id}_{k_1}$, the multiplication $\mu$ is a homomorphism of $k$-algebras. Put $S=\{s\in R:\mu(s)\ne0\}$. Since $\mu(1)=1$ and $k_1$ is a field, $1\in S$ and $s,t\in S$ imply $\mu(st)=\mu(s)\mu(t)\ne0$. Thus $S$ is multiplicative in the sense of [def-weil-pbc-module-localization], and each $\mu(s)$ is a unit. Also $\mu$ is surjective, since $\mu(c\otimes1)=c$ for $c\in k_1$. It remains to show that every element of $\ker\mu$ is killed by an element of $S$.

### Old step 2

Fix $x\in R$ with $\mu(x)=0$. By the generation clause of [def-weil-pbc-module-tensor-product] write $x=\sum_{i=1}^n a_i\otimes b_i$, absorbing any $k$-scalar coefficients into the $a_i$. Let $E=k(b_1,\ldots,b_n)\subseteq k_1$. Each $b_i$ is algebraic over $k$ by [def-weil-pbc-separable-algebraic-extension], so [lem-weil-pbc-algebraic-generators-finite-extension] makes $E/k$ finite. Every element of $E$, being an element of $k_1$, is algebraic with separable minimal polynomial over $k$ by the same definition; thus $E/k$ is separable algebraic. Apply [lem-weil-pbc-finite-separable-primitive-element] to obtain $\alpha\in E$ with $E=k(\alpha)$. This also covers an empty tensor sum: then $E=k$ and a primitive element may be $0$.

### Old step 3

Let $P\in k[T]$ be the minimal polynomial of $\alpha$. By [def-weil-pbc-separable-algebraic-extension], $P(\alpha)=0$ and $P$ is separable. The last clause of [lem-weil-pbc-minimal-polynomial-quotient-field-iso] says that $k(\alpha)=\{g(\alpha):g\in k[T]\}$; hence choose $g_i\in k[T]$ with $b_i=g_i(\alpha)$. View $P,g_i$ also in $k_1[T]$ by the coefficient inclusion and set $F(T)=\sum_i a_i g_i(T)$. Put $t=1\otimes\alpha\in R$, and evaluate polynomials in $k_1[T]$ in the commutative ring $R$ (the map $c\mapsto c\otimes1$ is the ring homomorphism $\iota_{k_1}$ of [lem-weil-pbc-algebra-tensor-pushout-universal-property] (1)) by sending a coefficient $c$ to $c\otimes1$ and $T$ to $t$. The coefficientwise formulas of [def-weil-polynomial-ring] and tensor bilinearity [def-weil-pbc-module-tensor-product] give $F(t)=x$ and $F(\alpha)=\sum_i a_i b_i=0$: for $g_i=\sum_j c_{ij}T^j$ with $c_{ij}\in k$, one has $(c_{ij}\otimes1)t^j=1\otimes(c_{ij}\alpha^j)$ and therefore $(a_i\otimes1)g_i(t)=a_i\otimes b_i$.

### Old step 4

We spell out the polynomial factorization used in the source. For $G(T)=\sum_j c_jT^j\in k_1[T]$ define $D_G(T)=\sum_{j\ge1}c_j\sum_{h=0}^{j-1}T^{j-1-h}\alpha^h$. The finite geometric-sum identity $(T-\alpha)\sum_{h=0}^{j-1}T^{j-1-h}\alpha^h=T^j-\alpha^j$ gives $G(T)-G(\alpha)=(T-\alpha)D_G(T)$ by summing coefficients, using [def-weil-polynomial-ring]. Since $P(\alpha)=F(\alpha)=0$, take $Q=D_P$ and $H=D_F$ to get $P=(T-\alpha)Q$ and $F=(T-\alpha)H$. Evaluating the explicit sum for $Q$ at $\alpha$ gives $Q(\alpha)=\sum_{j\ge1}j p_j\alpha^{j-1}=P'(\alpha)$, where $P=\sum_j p_jT^j$ and the derivative is the coefficient formula of [def-pc-separable-polynomial]. No division algorithm or assertion about tensor-product injectivity is needed for these identities.

### Old step 5

By the separability of $P$, [def-pc-separable-polynomial] gives $U,V\in k[T]$ with $UP+VP'=1$. Evaluate this identity at $\alpha\in k_1$. Since $P(\alpha)=0$, it reads $V(\alpha)P'(\alpha)=1$. Thus $P'(\alpha)\ne0$, and Step 4 gives $Q(\alpha)\ne0$. This argument works in positive characteristic as well: the integer factors in the derivative are interpreted in the field, and the Bezout identity is what guarantees nonvanishing.

### Old step 6

Set $s=Q(t)\in R$, with evaluation as in Step 3. Since $\mu(c\otimes1)=c$ and $\mu(t)=\alpha$, one has $\mu(s)=Q(\alpha)\ne0$, so $s\in S$. In $R$, $P(t)=\sum_j(p_j\otimes1)(1\otimes\alpha^j)=1\otimes\sum_jp_j\alpha^j=1\otimes P(\alpha)=0$, using the balancing relations of [def-weil-pbc-module-tensor-product] since $p_j\in k$. Evaluating the identities from Step 4 in the commutative ring $R$ of [lem-weil-pbc-algebra-tensor-pushout-universal-property] (1), where $\mu$ is a ring homomorphism by (2) now gives $sx=Q(t)F(t)=Q(t)(t-\alpha\otimes1)H(t)=P(t)H(t)=0$. Thus every $x\in\ker\mu$ has the required annihilator in $S$. Only the finitely many right tensor factors of $x$ entered the finite subextension; no finiteness assumption on $k_1/k$ has been used.

### Old step 7

Using the fraction construction of [def-weil-pbc-module-localization] with $M=R$, define $\phi:S^{-1}R\to k_1$ by $r/s\mapsto\mu(r)\mu(s)^{-1}$. If $r/s=r'/s'$, there is $u\in S$ with $u(s'r-sr')=0$; applying $\mu$ and cancelling the nonzero factors proves equality of the proposed values. The fraction addition and multiplication formulas show that $\phi$ is a ring homomorphism, and $\phi(r/1)=\mu(r)$. It is surjective because $c=\phi((c\otimes1)/1)$. If $\phi(r/s)=0$, then $\mu(r)=0$, so Step 6 supplies $u\in S$ with $ur=0$. The fraction equality criterion gives $r/s=0$. Thus $\phi$ is injective as well, hence an isomorphism identifying $\mu$ with $R\to S^{-1}R$. In particular the three explicit localization conditions in the statement all hold (the fraction representation of $c$ uses numerator $c\otimes1$ and denominator $1$).

## Not duplicates

- lem-trf-separable-tensor-polynomial-presentation vs lem-per-finite-algebra-external-tensor-filtration: states filtrations of modules over A tensor B, not primitive tensor coordinates or divided-difference annihilation.
- lem-trf-separable-tensor-polynomial-presentation vs lem-pur-ordinary-kunneth-finite-ring: states a derived etale Kunneth isomorphism for schemes, not either algebra lemma.
- lem-trf-separable-tensor-polynomial-presentation vs lem-trf-geometric-reducedness-separable-scalar-restriction: states equivalence of two geometric reducedness conditions for algebras and uses the parent; neither child asserts that equivalence.
- lem-trf-separable-tensor-polynomial-presentation vs sk-lem-sf-kunneth-star: states an external-product/direct-image comparison, not either algebra lemma.
- lem-trf-separable-tensor-polynomial-presentation vs lem-pur-finite-field-derived-tensor-summand: constructs an idempotent and a derived tensor summand for finite fields; neither child states that construction, and the presentation child allows infinite separable algebraic extensions.
- lem-trf-separable-tensor-polynomial-presentation vs lem-pur-separable-field-tensor-chain: assumes a separability idempotent and compares total tensor complexes, not polynomial coordinates or the scalar polynomial calculation.
- lem-trf-separable-tensor-polynomial-presentation vs lem-pur-separable-field-tensor-sheaf: assumes a separability idempotent and supplies module-sheaf actions and a section, not either child statement.
- lem-trf-separable-tensor-polynomial-presentation vs lem-weil-pbc-finite-separable-multiplication-etale: states etaleness/smoothness of finite-extension multiplication, not the compatible polynomial certificates or explicit divided difference in arbitrary algebras.
- lem-trf-separable-tensor-polynomial-presentation vs lem-weil-pbc-geometric-regularity-separable-extension: states equivalence of geometric regularity under scalar restriction for Noetherian algebras, not either child statement.
- lem-trf-separable-tensor-polynomial-presentation vs lem-trf-separable-algebraic-diagonal-localization: the parent asserts a localization isomorphism for the tensor multiplication map; the presentation child asserts only coordinate certificates, and the polynomial child has no tensor or localization hypothesis or conclusion.
- lem-trf-separable-root-polynomial-annihilator vs lem-per-finite-algebra-external-tensor-filtration: states filtrations of modules over A tensor B, not primitive tensor coordinates or divided-difference annihilation.
- lem-trf-separable-root-polynomial-annihilator vs lem-pur-ordinary-kunneth-finite-ring: states a derived etale Kunneth isomorphism for schemes, not either algebra lemma.
- lem-trf-separable-root-polynomial-annihilator vs lem-trf-geometric-reducedness-separable-scalar-restriction: states equivalence of two geometric reducedness conditions for algebras and uses the parent; neither child asserts that equivalence.
- lem-trf-separable-root-polynomial-annihilator vs sk-lem-sf-kunneth-star: states an external-product/direct-image comparison, not either algebra lemma.
- lem-trf-separable-root-polynomial-annihilator vs lem-pur-finite-field-derived-tensor-summand: constructs an idempotent and a derived tensor summand for finite fields; neither child states that construction, and the presentation child allows infinite separable algebraic extensions.
- lem-trf-separable-root-polynomial-annihilator vs lem-pur-separable-field-tensor-chain: assumes a separability idempotent and compares total tensor complexes, not polynomial coordinates or the scalar polynomial calculation.
- lem-trf-separable-root-polynomial-annihilator vs lem-pur-separable-field-tensor-sheaf: assumes a separability idempotent and supplies module-sheaf actions and a section, not either child statement.
- lem-trf-separable-root-polynomial-annihilator vs lem-weil-pbc-finite-separable-multiplication-etale: states etaleness/smoothness of finite-extension multiplication, not the compatible polynomial certificates or explicit divided difference in arbitrary algebras.
- lem-trf-separable-root-polynomial-annihilator vs lem-weil-pbc-geometric-regularity-separable-extension: states equivalence of geometric regularity under scalar restriction for Noetherian algebras, not either child statement.
- lem-trf-separable-root-polynomial-annihilator vs lem-trf-separable-algebraic-diagonal-localization: the parent asserts a localization isomorphism for the tensor multiplication map; the presentation child asserts only coordinate certificates, and the polynomial child has no tensor or localization hypothesis or conclusion.

## Unfinished work

No repair point is left unresolved. Proofs of the two new statement-only nodes are intentionally left for separate workers, as the return requires. Dry-run and delivery results are recorded after the tool returns.
