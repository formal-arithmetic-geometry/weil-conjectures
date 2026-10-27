# Stage-1 repair: lem-sfb-multiradical-galois-degree

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-multiradical-galois-degree.json`: unchanged statement, five-step assembly (1854 characters), replacing the returned nine-step, 4790-character proof.
- `dag/nodes/sec-six-functors-basics/lem-sfb-split-binomial-root-torsor.json`: new statement, unsplit, no complete Mathlib match. This is the non-irreducible binomial calculation, including the root count, separability and scaled factorization, for arbitrary nonzero a.
- `dag/nodes/sec-six-functors-basics/lem-sfb-generated-field-scalar-character-order.json`: new statement, unsplit, no complete Mathlib match. This is a conditional scalar-character theorem for an arbitrary generated field and a finite scalar subgroup, including injectivity and finite group-order divisibility. It assumes neither radicals nor finite Galois structure and makes no field-degree assertion.
- `citations.json`: a verbatim statement quotation for each node cited by each assembly step. `searches.jsonl` preserves every actual search command, including unavailable LeanSearch responses.

The sandbox was empty except for dispatcher brief markers. I copied the current repository item as the repair baseline, preserving all statement text, Lean records, earlier searches and provenance. The full prior node is retained in `returned-node.json`, the earlier Q49 report in `previous-report.md`, and the full returned proof is reproduced below. No repository or launcher file was written; no git, Lean compiler, Lake or build command was run. Delivery uses the prescribed external tool.

## Attachments

None. The project-source tag and notion searches did not locate a finished declaration under WeilConjectures stating every clause. The current `IntermediateField.multiradical_galois_degree` in `lean/Sheaf/FieldTheory/MultiradicalGaloisDegree.lean:71` ends in `sorry`. KummerFreeSubgroup's compatible single radical systems and KummerInertia's single-root exponent calculations neither supply the whole item nor the two new general interfaces.

## WANTED

None. Sources used are locally available. No SGA source was used.

## Findings and repair of the return

The one numbered substantive instruction in the return is a re-split to spread the proof work among workers, with at least two comparable new statement-only tasks and assembly at most 3000 characters. It is repaired by the two independent tasks above. Neither task refers to the other, the parent, or the parent's hypotheses by shorthand. Neither alone implies the parent: the first has no generated-field, normality, automorphism or degree conclusion; the second assumes the scalar condition as a hypothesis and has no radical/root-polynomial or Galois-degree conclusion. Their intended arguments are comparable: approximately 1400 characters of root and factorization work versus approximately 1800 characters of character, generation and counting work. They are not elementary two-line facts: the first requires polynomial separability, root count/descent and scaled factorization; the second requires construction of a character, agreement on the generated field, and a finite coset counting argument. The short parent retains the separable-subfield and product splitting-field assembly and applies the existing Galois-order result.

The parent's mathematical statement was not corrected, weakened, shortened or otherwise changed. There is no STATEMENT-DISPUTED issue. The source's opening Kummer paragraph writes a quotient for a possibly zero a; the parent and the new binomial lemma assume a is nonzero, so this boundary issue does not affect them.

The existing `lem-sfb-splitting-field-finite-normal` is already on the repository and is reused, not delivered again. Its theorem does not assume that the product polynomial is separable. The root-torsor task uses the existing polynomial and field definitions. The scalar-character task defines U by its inherited operations and closure conditions and defines its automorphism and tuple groups explicitly; it introduces no new group convention node.

## Work allocation and full arguments for the statement-only tasks

The new node files deliberately have empty proof and proof_deps, null proof_origin and status unsplit. The following is handover material in this report, not a split of those nodes.

For `lem-sfb-split-binomial-root-torsor`, transfer returned steps 2 and 4 and the scaling part of step 5, reproduced verbatim in the archive below. For P_a=X^n-a, use the explicit Bezout identity -a^{-1}P_a+(na)^{-1}XP_a'=1, including a=1, to establish separability. The existing distinct-root lemma gives n distinct roots and monic factorization of X^n-1 in Omega. Because that polynomial already splits over F, evaluation of its F-linear factors shows that each Omega-root lies in F. They are nonzero and form precisely mu_n(F). For each nonzero radical alpha, substitute X/alpha in this factorization and multiply by alpha^n; the n linear factors give exactly the claimed scaled factorization. Every beta with beta^n=a has (beta/alpha)^n=1, so is alpha times a unique base root of unity. This proves both directions of the claimed bijection, not just a list of candidate roots. No primitive root or binomial irreducibility is needed. Existing interfaces available to its future worker are `def-pc-separable-polynomial` and `lem-pc-separable-polynomial-distinct-roots-alg-closed`.

For `lem-sfb-generated-field-scalar-character-order`, transfer returned steps 6, 7, the tuple count in step 8, and all of step 9, reproduced below. In the generalized statement the hypothesis replaces the radical calculation placing the ratios in the base scalar group; the parent still performs that calculation. Nonvanishing of b_j and injectivity F→E make the scalar u_j(sigma) unique. Define chi coordinatewise by those unique scalars. Since F-automorphisms fix them, u_j(sigma tau)=u_j(tau)u_j(sigma)=u_j(sigma)u_j(tau) and u_j(1)=1. Thus chi is a homomorphism. Equal characters imply equality on all generators; the agreement set is a subfield (closed under addition, subtraction, multiplication and inverses) containing F and every b_j, hence all E. This gives injectivity and uniqueness of the displayed homomorphism. The finite target H=U^r has |U|^r elements by induction, starting with the one empty tuple; an injective map into H makes G finite. The image I is closed under group operations. For h~k iff h^{-1}k lies in I, choose a representative set T for the finite equivalence classes. Then T×G→H, (t,g)↦t chi(g), is bijective: a representative for the class of h yields existence; equality of two outputs gives t^{-1}t'=chi(g)chi(g')^{-1} in I, so t=t' and cancellation and injectivity give g=g'. Counting gives |U|^r=|T||G|. Empty generators give E=F and the trivial G, consistently. This is a general scalar action theorem, not a restatement of the parent's radical character clause.

## Not duplicates

lem-sfb-split-binomial-root-torsor vs lem-sfb-multiradical-galois-degree: the common 09I6 source supplies different inputs; the new node is a polynomial root-torsor statement for a single arbitrary nonzero a and has no finite Galois extension or character conclusion.

lem-sfb-split-binomial-root-torsor vs lem-exc-kummer-binomial-splitting-field: the existing node assumes an irreducible binomial and a primitive root and proves a cyclic extension of degree n; the new node assumes splitting of X^n-1 and invertibility of n, allows reducible binomials, and states a root bijection and factorization rather than a cyclic Galois group.

lem-sfb-generated-field-scalar-character-order vs lem-sfb-multiradical-galois-degree: the new node has arbitrary generators and a finite scalar subgroup plus a scalar-action hypothesis, no algebraicity or normality hypothesis and no conclusion about field degree. The parent must establish that hypothesis from the radical equations and must separately prove finite Galois structure and identify degree with automorphism order.

lem-sfb-generated-field-scalar-character-order vs lem-exc-kummer-binomial-splitting-field: the existing node concerns one irreducible Kummer binomial and degree n; the new statement concerns a conditional diagonal action on arbitrary field generators and only the automorphism group order, with no binomial or degree-n assertion.

lem-sfb-split-binomial-root-torsor vs lem-sfb-generated-field-scalar-character-order: both have source 09I6, but one is a polynomial calculation and the other a conditional group-character/counting theorem for arbitrary fields. They have no proof or statement dependency on one another.

Further searches of the entire DAG and blueprint found `lem-sc-primitive-root`, which assumes the base algebraically closed and supplies no scaled-binomial factorization; `lem-exc-tame-root-extension`, which imposes henselian DVR/uniformizer conditions and gives exact ramification; `lem-per-finite-canonical-kummer-character`, which is a continuous surjection out of an absolute Galois group for a strictly henselian DVR; and the radical-kernel/restriction nodes, which concern pro-p kernels. I opened these statements; none is a generalization of either new node. Sheaf Kummer exactness and geometric root-cover nodes concern different objects. Source searches for 09I6 found only the parent and the irreducible-binomial node listed above as primary-source matches. The curve-normalization parent merely uses this algebraic input and cannot be cited without circularity.

Blueprint searches used Kummer, roots of unity, binomial, character, automorphism group, scalar character and generated field. No blueprint statement equals either new node; same_as is empty. The ancestor script returns None for this migrated chain, as in the delivered baseline. I preserved the parent's exact from.node and via list; each new node prepends this item and names the exact inherited route place plus the returned steps it extracts. The fixed chapter and unit were read; no route change was made.

## Mathlib search assessment

All new-node searches were actually run with msearch under Q44 and this item and their results were read. Each node records semantic, Loogle and grep searches and the unavailable LeanSearch response; further semantic phrasings checked possible generalizations. LeanSearch was rate limited and is recorded unavailable, never absence. Earlier parent searches are retained unchanged. The binomial hits include `Polynomial.separable_X_pow_sub_C_unit` (FieldTheory/Separable.lean:232), `X_pow_sub_C_eq_prod` (FieldTheory/KummerExtension.lean:85), `IsPrimitiveRoot.nthRoots_eq`, and primitive-root cardinality statements. I read the actual separability and Kummer declarations: they supply components, but the primitive-root formulations require producing a primitive root, and no single declaration or one-line specialization gives the new combined root/descent/separability statement under its splitting hypothesis. The task remains unsplit, not falsely marked absent in its individual parts.

For the scalar-character node, Loogle returned restriction homomorphisms and a cyclotomic autToPow injection; semantic searches returned fixed-field bijections, finite-field order formulas, normal-basis and cyclic Kummer results. These have different hypotheses or targets. I read IntermediateField.adjoin_algHom_ext at Adjoin/Defs.lean:498 and the Kummer character equivalence at KummerExtension.lean:248ff (irreducibility is assumed), plus Subgroup.card_dvd_of_injective at GroupTheory/Coset/Card.lean:79ff. Generator extensionality and finite-group divisibility separately support portions of the task but neither constructs its character from the scalar-action hypothesis. None is a full match or one-line specialization. Both new nodes therefore remain unsplit; zero new Mathlib leaves.

## Review by Q44

I read Stacks `fields.tex`, Tag 09I6 (`section-Kummer`, opening paragraph), which states the injective one-root character and subgroup-order divisibility. For the root-torsor node I read the root-factorization source there and the Bezout separability definition and existing distinct-root interface; for the scalar-character node I read the character and subgroup-order passage there. The two generalized formulations and explicit computations are agent supplied. I also read the local proofs and statements of 030K (`lemma-separable-first`), 09HC (`lemma-separable-elements`), 09HU (`lemma-splitting-field`) and 09I1 (`lemma-finite-Galois`) for the retained assembly. No unprovided source is claimed.

Assembly step 1 is the empty generated field calculation. Step 2 cites the new root-torsor statement for every binomial's separability, nonzero radicals, roots and root count. I opened the three existing separability nodes: `lem-weil-pbc-separable-first-purely-inseparable` explicitly states that the separable elements form a subfield which is separable algebraic; `def-weil-pbc-relative-separable-closure` explicitly characterizes them as roots of separable polynomials; `def-weil-pbc-separable-algebraic-extension` gives minimal polynomials as monic kernel generators. The algebraic-closure hypothesis supplies algebraicity of Omega/F. Inclusion of generated fields and equality of evaluation kernels explicitly justify restriction of separability to L; nothing is taken from the proof rather than statement of a cited node.

Step 3 uses precisely the new factorization in Omega and injectivity of coefficient inclusion to obtain it in L. I checked both generated-field containments: every listed root is in L, and each generator occurs with zeta=1. Since r>0 and n>=1, the monic product has degree rn>0. The cited `lem-sfb-splitting-field-finite-normal` explicitly states finite dimensionality and normality under these hypotheses, and requires no separability of the product. Combining with step 2 gives finite Galois structure even for repeated factors.

Step 4 explicitly computes the nth power of the ratio, and the root-torsor node for a=1 says all such roots in Omega come from F. Thus the scalar subgroup condition of the new general character lemma is satisfied with U=mu_n(F); b_j are nonzero and generate L. That lemma explicitly supplies the coordinate formula, injection, finiteness and divisibility of the automorphism order. Its target cardinality is n^r because the first new node says |U|=n. Step 5 cites `lem-weil-pbc-finite-galois-fixed-field`, whose full statement explicitly says the finite automorphism group has order the field degree, as well as the fixed-field assertion suggested by its title. Step 3 supplies its finite Galois hypotheses. Substitution gives the desired divisibility. Every cited statement was opened, and citations.json quotes each one verbatim.

I checked B1--B10 against the two new files: complete self-contained objects, definition dependencies, no proofs or proof sketches in statements, correct single TeX escapes and source tag/label, authentic searches, no unsupported Mathlib-leaf claim, and exact inherited blueprint references. C1--C8: all non-elementary inputs of the short assembly are cited nodes; citations say exactly what each step takes; dependencies are the union of uses; no new node cites the parent and no cycle is introduced. All remaining off-unit citations are existing Mathlib leaves, requiring no route exception. D1--D5: the new nodes isolate two independent substantive arguments of comparable size, neither restates the complete parent nor proves one of its clauses under identical hypotheses; no argument is erased, as shown by the archive and allocation. E1--E7: nonzero divisors, invertible n, algebraicity, field generation, product nonconstancy and finite Galois hypotheses have all been checked at their uses. The new statements are claims only; the handover argument is outside their node files as required. No assembly step exceeds 2000 characters.

Small cases: n=1 gives the one-element root group and L=F; r=0 gives the empty generated field and degree 1. For F=Q, n=2, repeated a_1=a_2=2 gives degree 2 dividing 4, although the product polynomial is not separable; both new tasks remain applicable. Taking a already an nth power allows reducible binomials and smaller degree. In positive characteristic n must be prime to that characteristic; neither proof uses a vanishing derivative. The binomial lemma excludes a=0, where the proposed bijection would fail. For the general scalar lemma, U={1} forces every automorphism to fix the generators, hence G is trivial; empty generators likewise force E=F; no hidden finite-dimensional or Galois hypothesis is used. The coset proof is valid in a general group, and the scalar target happens to be abelian, justifying the composition order calculation.

## Unfinished work

The authorized one-level split is complete. Two independent statement-only nodes await future workers. No Lean proof was attempted, and no source file was modified.

## Archive of the complete returned proof

This text preserves all nine old arguments, rather than shortening away work. Old step 1 is retained as assembly step 1. Old steps 2 and 4 and the scaling calculation of step 5 move to the root-torsor task. Old step 3 and the product-generation/finite-normal part of step 5 remain explicitly in assembly steps 2--3. Old step 6's ratio-to-base calculation remains explicitly in assembly step 4; its homomorphism calculation and old steps 7 and 9 move to the scalar-character task. Old step 8's tuple count moves to that task, while its Galois-order identity is retained in assembly step 5.

### Returned step 1

If $r=0$, adjoining no elements gives $L=F$. An $F$-automorphism of $F$ fixes every element, so its group and the empty product target are both trivial. The displayed map is their unique homomorphism, and $[F:F]=1\mid n^0=1$. Henceforth assume $r>0$.

Cited statements: none (explicit elementary argument).

### Returned step 2

For $a\in F^\times$ put $P_a=X^n-a$. It is monic of degree $n$, and its derivative is $nX^{n-1}$. Since $n$ and $a$ are invertible, the identity $-a^{-1}P_a+(na)^{-1}X P_a^{\prime}=1$ proves that $P_a$ is separable by the coprimality definition. This applies to $a=1$ and to every $a_j$; also $\alpha_j\ne0$ since $\alpha_j^n=a_j\ne0$. No irreducibility is used.

Cited statements: def-pc-separable-polynomial.

### Returned step 3

Apply the separable-subfield theorem to the algebraic extension $\Omega/F$. Its subfield $S$ of elements separable over $F$ is separable algebraic over $F$. Each $\alpha_j$ is a root of the separable polynomial $P_{a_j}$, so belongs to $S$ by the root description of the relative separable closure. Because $S$ is a subfield containing $F$ and these generators, $L\subseteq S$. Every $x\in L$ is consequently separable over $F$: the evaluation kernels of $F[X]\to L$ and $F[X]\to S$ at $x$ coincide under the injective inclusion, so their monic generators, the minimal polynomials, coincide. Thus $L/F$ is separable algebraic.

Cited statements: lem-weil-pbc-separable-first-purely-inseparable, def-weil-pbc-relative-separable-closure, def-weil-pbc-separable-algebraic-extension.

### Returned step 4

Apply the distinct-root and factorization theorem to the monic separable polynomial $X^n-1$ in the given algebraic closure $\Omega$: it has exactly $n$ distinct roots there. All these roots lie in $F$. Indeed, the assumed splitting over $F$ writes $X^n-1$ as a product of linear factors with coefficients in $F$; evaluating at any root in $\Omega$ forces one factor to vanish, so that root equals an element of $F$. The roots are nonzero. They are therefore exactly the elements of $\mu_n(F)$, proving $|\mu_n(F)|=n$ and the identity $X^n-1=\prod_{\zeta\in\mu_n(F)}(X-\zeta)$.

Cited statements: lem-pc-separable-polynomial-distinct-roots-alg-closed.

### Returned step 5

For every $j$, substitute $X/\alpha_j$ in the last factorization and multiply by $\alpha_j^n=a_j$. Since there are $n$ factors, this gives $X^n-a_j=\prod_{\zeta\in\mu_n(F)}(X-\alpha_j\zeta)$ in $L[X]$ (the polynomial equality can be checked in $\Omega[X]$, whose coefficient inclusion is injective). Hence $P=\prod_{j=1}^r(X^n-a_j)$ is a nonconstant split polynomial over $L$. Every root belongs to $L$, and each $\alpha_j$ is one of its roots, using $\zeta=1$. Thus the field generated over $F$ by all its roots is exactly $L$. The finite-normal splitting-field theorem gives finite dimensionality and normality of $L/F$. Together with step 3 this proves that $L/F$ is finite Galois. The product $P$ need not itself be separable when generators repeat; normality of a splitting field does not require separability of $P$.

Cited statements: lem-sfb-splitting-field-finite-normal.

### Returned step 6

For $\sigma\in\operatorname{Gal}(L/F)$ define $c_j(\sigma)=\sigma(\alpha_j)/\alpha_j$. Its $n$th power is $\sigma(a_j)/a_j=1$, so step 4 implies that it is the image of a unique element of $\mu_n(F)$. These elements are fixed by all $F$-automorphisms. With composition as group multiplication, $c_j(\sigma\tau)=\sigma(c_j(\tau)\alpha_j)/\alpha_j=c_j(\tau)c_j(\sigma)=c_j(\sigma)c_j(\tau)$, and $c_j(1)=1$. Coordinatewise these formulas prove that the displayed character is a homomorphism to $\mu_n(F)^r$.

Cited statements: none (explicit elementary argument).

### Returned step 7

If two automorphisms $\sigma,\tau$ have equal characters, multiplication by each nonzero $\alpha_j$ gives $\sigma(\alpha_j)=\tau(\alpha_j)$. The set of $x\in L$ on which they agree is a subfield: agreement is preserved by addition, subtraction, multiplication and inversion of nonzero elements. It contains $F$ and every $\alpha_j$, hence is all of $L$ by the definition of the generated field. Therefore $\sigma=\tau$, proving injectivity.

Cited statements: none (explicit elementary argument).

### Returned step 8

For the finite Galois extension established in step 5, the Galois-order theorem gives a finite group $G=\operatorname{Gal}(L/F)$ with $|G|=[L:F]$. Put $H=\mu_n(F)^r$ and let $\chi:G\to H$ be the injective homomorphism in steps 6 and 7. The group $H$ has $n^r$ elements: by step 4 each coordinate has $n$ choices, and induction on the number of coordinates multiplies the count by $n$, starting from one empty tuple.

Cited statements: lem-weil-pbc-finite-galois-fixed-field.

### Returned step 9

Write $I=\chi(G)\subseteq H$. It contains $1$ and is closed under products and inverses, by the homomorphism formulas. Define $h\sim k$ by $h^{-1}k\in I$; these closure properties give reflexivity, symmetry and transitivity. Since $H$ is finite, choose a set $T\subseteq H$ with one representative of each equivalence class. The map $T\times G\to H$, $(t,g)\mapsto t\chi(g)$, is bijective. Indeed, each $h$ lies in the class of some $t$, so $t^{-1}h=\chi(g)$ for some $g$, proving surjectivity. If $t\chi(g)=t^{\prime}\chi(g^{\prime})$, then $t^{-1}t^{\prime}=\chi(g)\chi(g^{\prime})^{-1}\in I$, so the representatives coincide; cancellation and injectivity of $\chi$ then give $g=g^{\prime}$. Counting this finite bijection gives $n^r=|H|=|T|\,|G|=|T|[L:F]$. This is the required divisibility.

Cited statements: none (explicit elementary argument).

## Dry-run repair

The first dry run rejected the scalar-character statement because its two definition references shared one bracket. I separated them into individually bracketed definition ids, retaining the same mathematics and stmt_deps, and regenerated its verbatim citation quote. No gate was bypassed.
