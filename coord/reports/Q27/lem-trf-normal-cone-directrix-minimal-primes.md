# Stage-1 repair: lem-trf-normal-cone-directrix-minimal-primes

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-normal-cone-directrix-minimal-primes.json`: item, split; statement and stmt_deps unchanged.
- `dag/nodes/sec-trace-formula/lem-trf-graded-polynomial-vertex-regularity.json`: statement, unsplit; no exact or one-line Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-flat-graded-fibre-regular-lift.json`: statement, unsplit; no exact or one-line Mathlib match.
- `citations.json`: one literal statement quotation per use in each assembly step.

## Attachments

None. Searches of lean/WeilConjectures for the item tag, directrix, normalCone/minimalPrimes, and the two proposed notions found no finished declaration stating them. The item has a sorry theorem in lean/Sheaf/RingTheory/NormalConeDirectrixMinimalPrimes.lean; that is retained as source material, not treated as an attachment.

## WANTED

None; all supporting sources are present. The full filtered-algebra and graded-coefficient syntheses are agent-written, not falsely attributed to a single Stacks tag.

## Fault repaired

The released stage-1 repair note overrides the old passing review: a 5481-character proof must distribute work among at least two new nodes and retain an assembly of at most 3000 characters. The sandbox initially contained only dispatcher brief markers, with no node, report or searches. I used the current repository's reviewed ten-step proof as the returned baseline; its statement, stmt_deps, blueprint metadata and Lean records remain intact. I corrected the inherited source-place typo 00MH/lemma-free-fibre-flat-free to 00NZ/lemma-finite-flat-local; the actual old proof already used the correct tag. No mathematical statement changed.

## What remains

The two new statements deliberately have no proof steps or proof dependencies and status unsplit, so two workers can prove them independently. Their complete predecessor arguments are retained below for takeover. Dry run and push are recorded at the end after completion.

## Search review

All new Mathlib searches ran through batch2/msearch.py and are recorded verbatim with actual results in searches.jsonl and the nodes. For each node I used LeanFinder, LeanSearch, Loogle and source grep, including a second natural-language phrasing. Loogle's unknown identifier MvPolynomial.coeff is marked unavailable, not a negative result; a separate valid Loogle query ran. Polynomial.Monic.isRegular (Mathlib/Algebra/Polynomial/Monic.lean:509) and the monomial-order leading-coefficient theorem (Mathlib/RingTheory/MvPolynomial/MonomialOrder.lean:471) were read: neither gives the graded-coefficient-to-monic coordinate comparison in one specialization. Regular.Flat results transport an already regular sequence along a flat map, rather than lift a residue initial form through an I-adic filtration. The prior item searches are retained unchanged because its statement and search question did not change.

DAG and whole-blueprint searches ran for associated graded, initial form, monic, nonzerodivisor, normal cone, polynomial vertex, graded fibre and 00ME, plus source searches by the new ids and concepts. I read the nearby approximation, Taylor/cone, formal-division and local residue-injection statements. No existing statement is either new lemma in greater generality.

## Not duplicates

lem-trf-graded-polynomial-vertex-regularity vs lem-trf-infinite-field-top-form-direction: the existing statement supplies only a direction or regularity after monicity is already established; the new statement constructs the coordinate automorphism and identifies its scalar leading coefficient for a graded coefficient algebra.

lem-trf-graded-polynomial-vertex-regularity vs lem-weil-pbc-monic-polynomial-nonzerodivisor: the existing statement supplies only a direction or regularity after monicity is already established; the new statement constructs the coordinate automorphism and identifies its scalar leading coefficient for a graded coefficient algebra.

lem-trf-flat-graded-fibre-regular-lift vs lem-weil-pbc-finite-flat-local-free: the existing statement is a general local module/filtration input, not the combined conclusion lifting a regular residue initial form to all graded multiplication maps and then to a regular element of the filtered ring.

lem-trf-flat-graded-fibre-regular-lift vs lem-weil-pbc-flat-mod-injective: the existing statement is a general local module/filtration input, not the combined conclusion lifting a regular residue initial form to all graded multiplication maps and then to a regular element of the filtered ring.

lem-trf-flat-graded-fibre-regular-lift vs lem-weil-pbc-krull-intersection-jacobson: the existing statement is a general local module/filtration input, not the combined conclusion lifting a regular residue initial form to all graded multiplication maps and then to a regular element of the filtered ring.

lem-trf-flat-graded-fibre-regular-lift vs lem-trf-local-universal-injective-residue: the existing statement is a general local module/filtration input, not the combined conclusion lifting a regular residue initial form to all graded multiplication maps and then to a regular element of the filtered ring.

lem-trf-flat-graded-fibre-regular-lift vs lem-weil-pbc-associated-graded-ideal-approximation: the existing statement is a general local module/filtration input, not the combined conclusion lifting a regular residue initial form to all graded multiplication maps and then to a regular element of the filtered ring.

lem-trf-flat-graded-fibre-regular-lift vs lem-trf-normal-cone-directrix-minimal-primes: the item compares minimal-prime component kernels with a polynomial vertex; the new lemma has no component or polynomial vertex and instead detects regular elements of a possibly nonreduced local ring from residue initial forms.

lem-trf-flat-graded-fibre-regular-lift vs lem-sc-principal-ideal-dvr: the existing statement characterizes a local domain with principal maximal ideal as a DVR; the new lemma allows arbitrary ideals and zero divisors and assumes flat associated graded algebra.

lem-trf-flat-graded-fibre-regular-lift vs lem-weil-pbc-finite-module-complete-over-complete-noetherian: the existing statement proves completeness of finite modules over a complete ring; the new lemma assumes no completeness and detects multiplication injectivity.

lem-trf-flat-graded-fibre-regular-lift vs lem-weil-pbc-krull-intersection-localization: the existing statement kills the intersection of ideal powers after localization; the new lemma constructs injective graded multiplication from residue injectivity and uses separation to detect a regular element.

lem-trf-flat-graded-fibre-regular-lift vs lem-sbc-complete-local-subideal: the existing statement changes the ideal of completion of an already complete local ring; the new lemma neither assumes nor concludes completeness.

lem-trf-flat-graded-fibre-regular-lift vs lem-sbc-regular-principal-prime-localization-dvr: the existing statement proves a localization at a principal regular prime is a DVR; the new lemma concerns residue initial forms for an arbitrary ideal and has no localization or prime assumption.

lem-trf-flat-graded-fibre-regular-lift vs lem-weil-pbc-completion-tensor-quotient-separated: the existing statement detects zero in a tensor product with a completion by its projections; the new lemma detects regular elements of the original local ring without any completion.

lem-trf-flat-graded-fibre-regular-lift vs lem-weil-pbc-flat-module-powers: the existing statement deduces flatness from flat ideal-power quotients; the new lemma assumes flat associated graded algebra and deduces finite-free graded pieces and multiplication injectivity.

lem-trf-flat-graded-fibre-regular-lift vs lem-sbc-power-series-punctured-global-sections: the existing statement is extension of sections across a puncture in a power-series scheme of depth at least two; the new lemma has no power series, depth or sections.

lem-trf-flat-graded-fibre-regular-lift vs lem-trf-noetherian-arrow-eventual-injective-flat-cokernel: the existing statement concerns eventual descent of flatness and injectivity through a directed system of local rings; the new lemma has one filtered local ring and concludes regularity of an element from its residue initial form.

lem-trf-graded-polynomial-vertex-regularity vs def-weil-pbc-triangular-field-model-equations: the existing node defines triangular presentation equations; it gives no coordinate change or injective multiplication assertion.

lem-trf-graded-polynomial-vertex-regularity vs lem-weil-pbc-algebraic-tower-triangular-relations: the existing statement constructs monic relations of an algebraic tower with linearly independent bounded monomials; the new lemma transforms a given homogeneous polynomial over a graded algebra.

lem-trf-graded-polynomial-vertex-regularity vs lem-weil-pbc-cartier-equality: the existing statement computes transcendence degree using differentials and cotangent homology; the new lemma concerns a homogeneous polynomial and its vertex image.

lem-trf-graded-polynomial-vertex-regularity vs lem-weil-pbc-field-extension-complete-intersection-subalgebras: the existing statement constructs complete-intersection subalgebras in a field extension; the new lemma gives a scalar-monic coordinate form for a given polynomial over a possibly nonreduced graded algebra.

lem-trf-graded-polynomial-vertex-regularity vs lem-weil-pbc-finitely-generated-field-complete-intersection-model: the existing statement constructs a complete-intersection domain with prescribed fraction field; the new lemma has no field extension or fraction-field construction.

lem-trf-graded-polynomial-vertex-regularity vs lem-weil-pbc-regular-sequence-quotient-localization-presentation: the existing statement presents a principal localization by adding a regular-sequence equation; the new lemma establishes regularity of a given homogeneous polynomial by changing variables.

lem-trf-graded-polynomial-vertex-regularity vs lem-weil-pbc-transitivity-gamma: the existing statement is the injective left end of the Jacobi-Zariski sequence for fields; the new lemma is a coordinate-monic comparison in a graded polynomial ring.

lem-trf-graded-polynomial-vertex-regularity vs lem-weil-pbc-triangular-field-model-bounded-independent: the existing statement establishes linear independence of bounded monomials in a quotient by monic triangular equations; the new lemma first produces monicity from a nonzero vertex polynomial.

lem-trf-graded-polynomial-vertex-regularity vs lem-weil-pbc-triangular-field-model-bounded-spanning: the existing statement establishes spanning by bounded monomials in a triangular quotient; the new lemma neither constructs such a quotient nor asserts a spanning result.

lem-trf-graded-polynomial-vertex-regularity vs lem-weil-pbc-triangular-field-model-coefficient-descent: the existing statement descends coefficients of a zero relation through a given monic final equation; the new lemma produces a coordinate change and nonzero scalar leading coefficient for a graded polynomial.

lem-trf-graded-polynomial-vertex-regularity vs lem-weil-pbc-triangular-field-model-data: the existing statement constructs transcendence-basis triangular field-model data and independent bounded monomials; the new lemma concerns a given homogeneous polynomial over an arbitrary standard graded algebra.

## Review by Q27

I read the entire returned ten-step split and the released keep_plan repair note, and checked the source statements in algebra.tex: 00NZ (lemma-finite-flat-local), 00ME (lemma-mod-injective), 00IP/00IQ (the two Krull-intersection labels), 00EW (lemma-reduced-ring-sub-product-fields, part 3), and the monic-polynomial use in the proof of 07BV (lemma-colimit-syntomic). For the new polynomial node I also read the direction and monic-nonzerodivisor leaf statements; for the new filtered node I read the finite-flat-free and Krull-intersection leaf statements. The source fields explicitly distinguish the agent syntheses from these supporting lemmas. The chapter and unit route and the inherited blueprint ancestor were read; this is the same historical algebraic refinement, not a new chapter route or any use of an SGA source.

Assembly step 1 uses exactly the associated-graded quotient definition and the tensor universal property. I recomputed F_j=I^j/mI^j and the component quotient (I^j+p)/(mI^j+p); I^{j+1} is absorbed because I is contained in m. Subtracting a representative in mI^j produces a representative in I^j intersect p. This elementary argument is kept explicit, including mutually inverse quotient-tensor maps. No flatness of R/p is assumed.

Assembly step 2 uses only the direct-sum homogeneous decomposition and the standard grading. Since p is contained in m, q_p is the identity in degree zero. At e=0 the vertex has no positive degrees. Thus a counterexample has positive n and e, precisely the hypotheses of the new polynomial node.

Assembly step 3 cites the new polynomial node's actual assertion that multiplication by f is injective. Here k is infinite because Q embeds in its residue field, B is standard graded as assumed, theta preserves the total grading, and epsilon(f) is nonzero by the contradiction hypothesis. The node also retains the specific coordinate-monic comparison from old steps 5--6, rather than merely renaming a clause of the item: it has no R, I, p, or component cone.

Assembly step 4 cites the new lifting node's actual conclusion that a is a nonzerodivisor. R is Noetherian local, I is contained in m, G is flat over A, a is in I^n, and h is its residue initial class; step 3 supplies the only additional hypothesis. This node has no B, vertex, minimal prime, reducedness, or characteristic assumption, so it is a separate argument rather than a restatement of the item. Its finite-free pieces, residue-matrix lifting, determinant/adjugate inverse and separated initial-form argument retain old steps 1--2 and 7--8 in full.

Assembly step 5 cites 00EW through the actual existing reduced-zerodivisor statement, not its proof: a in a minimal prime of the reduced R admits a nonzero annihilator. This contradicts step 4. Step 6 uses only the quotient universal property, with the descended map explicitly written on q_p(x). The resulting homomorphism is graded and surjective because the original epsilon theta is so. Every node cited by these steps was opened and its statement read, and citations.json contains its verbatim statement; no citation uses only a proof or a definition to obtain a theorem.

Edge cases checked: I=0 gives F=k and the claimed lifting implication only for nonzero residue a, hence a a unit. n=0 in the new lifting node is allowed and agrees with this local unit test. Rank-zero source pieces cause no matrix exception. A field, e=0, and B=k are covered. For a nonreduced B, e.g. k[u]/(u^2) with u in degree one, T+u has image T and is monic regular although B has zero divisors. The coordinate-monic conclusion uses total homogeneity: a coefficient in B_+ has T-degree strictly below n, while the T_1^n coefficient must lie in B_0=k. I make no claim about a corresponding coordinate-monic conclusion for nonhomogeneous polynomials. In the local-ring lifting argument I need neither reducedness nor Q, whereas both remain in the item where used. The familiar R=Q[x,y]/(xy) localized at (x,y), I=(x) fails normal flatness, so it is not a counterexample to the lift. For I=m the special fibre is the tangent cone and the two components' kernels are killed by the vertex projection. All new statements are self-contained; no statement dispute was found.

I checked delivery-errors B--E: new nodes are statement-only with real definitions cited, no proof sketch in their statements, exact blueprint ancestry, genuine logged searches; the assembly contains every non-elementary input as a node, has no circular dependence or off-unit replacement, and introduces no hidden flatness or reducedness hypothesis. No non-elementary assembly step exceeds 2000 characters. The elementary quotient/homogeneity and descent arguments are retained as steps under the no-elementary-new-node rule.

## Retained predecessor arguments and allocation

These are the returned proof steps verbatim, including their original citations and source places, so no argument is lost or blurred. Steps 1,2,7,8 belong to the new filtered-lifting node; steps 5,6 to the new polynomial node; steps 3,4,9,10 remain as the elementary assembly and contradiction. The two extracted workloads are 2063 and 1151 characters of original argument respectively, rather than moving the whole theorem into a single node.

### Original step 1 — lem-trf-flat-graded-fibre-regular-lift

Write $\mathfrak n=\mathfrak m/I$, the maximal ideal of the local ring $A$, and $G_j=I^j/I^{j+1}$. Each $G_j$ is finite over $A$: the Noetherian hypothesis gives finitely many generators of the ideal $I^j$, whose images generate $G_j$, and $I$ annihilates $G_j$. It is flat over $A$. Indeed the inclusion $s_j:G_j\to G$ and degree projection $r_j:G\to G_j$ satisfy $r_js_j=1$. After tensoring an injection $U\hookrightarrow V$ with these maps, an element of the kernel for $G_j$ maps into the zero kernel for $G$ and then retracts to zero. This proves flatness directly from the assumed tensor-injectivity of $G$.

Uses: def-weil-pbc-associated-graded-ring, def-weil-pbc-module-tensor-product, def-weil-pbc-noetherian-ring.

Source: literature/stacks-project/algebra.tex; Agent calculation with the associated-graded direct sum; supporting Tag 00NZ, lemma-finite-flat-local: verification of finite and flat hypotheses.

### Original step 2 — lem-trf-flat-graded-fibre-regular-lift

Apply [lem-weil-pbc-finite-flat-local-free] to $A$ and each finite flat module $G_j$. Thus every $G_j$ is free and has a finite basis (a finite generating set involves only finitely many members of any basis). In particular each multiplication map $G_j\to G_{j+n}$ below can be represented by a finite matrix over the local ring $A$.

Uses: lem-weil-pbc-finite-flat-local-free.

Source: literature/stacks-project/algebra.tex; Tag 00NZ, lemma-finite-flat-local, applied degree by degree.

### Original step 3 — assembly

Fix a minimal prime $\mathfrak p\subset R$; it is contained in $\mathfrak m$. Put $F=G\otimes_Ak$. On degree $j$, the elementary quotient-tensor identification $M\otimes_A(A/\mathfrak n)=M/\mathfrak nM$ gives $F_j=I^j/(I^{j+1}+\mathfrak mI^j)=I^j/\mathfrak mI^j$, since $I\subseteq\mathfrak m$. The target of $q_{\mathfrak p}$ in degree $j$ is $(I^j+\mathfrak p)/(\mathfrak mI^j+\mathfrak p)$. Here $\bar I^{j+1}$ disappears because it lies in $\mathfrak m\bar I^j$. Consequently every $h\in(\ker q_{\mathfrak p})_j$ has a representative $a\in I^j\cap\mathfrak p$: if a representative $x\in I^j$ has $x=b+a$ with $b\in\mathfrak mI^j$, $a\in\mathfrak p$, then $a=x-b\in I^j$. The quotient-tensor identification used here sends $m\otimes\bar c$ to $cm$ modulo $\mathfrak nM$, with inverse $m\mapsto m\otimes1$; bilinearity verifies both compositions.

Uses: def-weil-pbc-associated-graded-ring, def-weil-pbc-module-tensor-product.

Source: literature/stacks-project/algebra.tex; Agent quotient calculation from the associated-graded definition and the tensor universal property; no flatness of R/p is asserted.

### Original step 4 — assembly

Both $q_{\mathfrak p}$ and $\epsilon\theta$ preserve degree. Therefore it suffices to prove the kernel inclusion on homogeneous elements: decompose any kernel element into its finitely many homogeneous components. Degree zero of $q_{\mathfrak p}$ is the identity $k\to k$ by the preceding formula. If $e=0$, $k[T_1,\ldots,T_e]=k$ has no positive degrees, so the inclusion already follows. Otherwise suppose for contradiction that a homogeneous $h\in(\ker q_{\mathfrak p})_n$ has $H=\epsilon\theta(h)\ne0$. Then $n>0$ and $e>0$. Choose its representative $a\in I^n\cap\mathfrak p$ as above, and write $\alpha=a\bmod I^{n+1}\in G_n$. Its reduction in $F_n$ is $h$.

Uses: def-weil-pbc-associated-graded-ring, def-pc-standard-graded-algebra.

Source: literature/stacks-project/algebra.tex; Agent homogeneous reduction, including the degree-zero and e=0 cases.

### Original step 5 — lem-trf-graded-polynomial-vertex-regularity

The residue field $k$ contains $\mathbf Q$: every nonzero rational is a unit in $R$, so its residue is nonzero. Hence $k$ is infinite. Apply [lem-trf-infinite-field-top-form-direction] to the nonzero homogeneous degree-$n$ polynomial $H$ in $e\ge1$ variables, obtaining $v\ne0$ with $H(v)\ne0$. Extend $v$ to a basis of $k^e$ and make the invertible linear substitution whose first column is $v$. The inverse basis matrix supplies the inverse substitution, so this is a graded automorphism of $B[T_1,\ldots,T_e]$.

Uses: lem-trf-infinite-field-top-form-direction, def-weil-pbc-mv-polynomial-ring.

Source: literature/stacks-project/algebra.tex; Agent direction choice, using the existing infinite-field polynomial leaf (Mathlib MvPolynomial.funext_set); elementary inverse-matrix substitution.

### Original step 6 — lem-trf-graded-polynomial-vertex-regularity

After that substitution, view $f=\theta(h)$ as a polynomial in $T_1$ with coefficients in $D=B[T_2,\ldots,T_e]$. Since $B$ is nonnegatively graded with $B_0=k$ and $f$ has total graded degree $n$, its $T_1$-degree is at most $n$, and its coefficient of $T_1^n$ is the scalar $c=H(v)\in k^\times$. Indeed a term with a coefficient in $B_+$ has total $T$-degree less than $n$, so it cannot contribute to $T_1^n$. Thus $c^{-1}f$ is monic in $D[T_1]$. By [lem-weil-pbc-monic-polynomial-nonzerodivisor] it is a nonzerodivisor there. Multiplying by the unit $c$ and undoing the substitution shows that multiplication by $h$ is injective on $F$.

Uses: def-pc-standard-graded-algebra, def-weil-pbc-mv-polynomial-ring, lem-weil-pbc-monic-polynomial-nonzerodivisor.

Source: literature/stacks-project/algebra.tex; Agent coefficient calculation; monic nonzerodivisor input as in Tag 07BV, lemma-colimit-syntomic, proof (supporting elementary polynomial fact, not the full vertex assertion).

### Original step 7 — lem-trf-flat-graded-fibre-regular-lift

For each $j\ge0$, let $U_j:G_j\to G_{j+n}$ be multiplication by $\alpha$. Its residue matrix $\overline U_j$ represents multiplication by $h$ on $F_j$, so is injective by the preceding step. Choose a left inverse of this finite matrix over the field $k$, and lift its entries to a matrix $V_j$ over $A$. Then $V_jU_j$ is square and reduces to the identity; its determinant reduces to $1$, so is a unit in the local ring $A$. The adjugate formula makes $V_jU_j$ invertible, giving $(V_jU_j)^{-1}V_j$ as a left inverse of $U_j$. Thus all $U_j$ are injective. A source of rank zero causes no exception: that map is injective outright.

Uses: .

Source: literature/stacks-project/algebra.tex; Agent finite-matrix calculation, the finite-free special case of Tag 00ME, lemma-mod-injective; the determinant and left inverse are written out rather than invoked as an additional lemma.

### Original step 8 — lem-trf-flat-graded-fibre-regular-lift

By [lem-weil-pbc-krull-intersection-jacobson] with $M=R$, we have $\bigcap_{j\ge0}I^j=0$: $R$ is Noetherian, finite over itself, and $I\subseteq\mathfrak m=\operatorname{Jac}(R)$ because $R$ is local. If $b\ne0$ and $ab=0$, separation provides an $r\ge0$ with $b\in I^r\setminus I^{r+1}$ (take the first power not containing $b$). The nonzero class $\beta=b\bmod I^{r+1}\in G_r$ then has $U_r(\beta)=ab\bmod I^{r+n+1}=0$, contradicting injectivity. Hence $a$ is a nonzerodivisor of $R$.

Uses: lem-weil-pbc-krull-intersection-jacobson, def-weil-pbc-associated-graded-ring.

Source: literature/stacks-project/algebra.tex; Tag 00IQ, lemma-intersection-powers-ideal-module, part (2), or local Tag 00IP, lemma-intersect-powers-ideal-module-zero; explicit initial-form argument.

### Original step 9 — assembly

But $a\in\mathfrak p$ and $R$ is reduced. The statement [lem-weil-pbc-reduced-zerodivisors-union-minimal-primes] therefore gives a $b\ne0$ with $ab=0$. This contradicts the preceding step, so $\epsilon\theta(h)=0$ for every homogeneous $h\in\ker q_{\mathfrak p}$. The homogeneous reduction proves $\ker q_{\mathfrak p}\subseteq\ker(\epsilon\theta)$ for every minimal prime $\mathfrak p$.

Uses: lem-weil-pbc-reduced-zerodivisors-union-minimal-primes.

Source: literature/stacks-project/algebra.tex; Tag 00EW, lemma-reduced-ring-sub-product-fields, part (3).

### Original step 10 — assembly

For the equivalent formulation, define the descended map on a class $q_{\mathfrak p}(x)$ by $\epsilon\theta(x)$. The kernel inclusion makes this well defined; addition, multiplication and grading follow from those of the original maps. It is surjective because $\epsilon\theta$ is surjective, and its composite with $q_{\mathfrak p}$ is $\epsilon\theta$ by construction.

Uses: .

Source: literature/stacks-project/algebra.tex; Agent quotient universal-property calculation.


## Dry-run repair log

The first no-push invocation exited with a duplicate-tag checklist, before pushing. I opened all twenty-one additional statements it named and added the explicit distinctions above; none states either new lemma or a generalization specializing to it.


## Promotion-return repair, 2026-10-22

The return is L's refusal to land a side-project completion that had not been promoted to the live queue DAG. I continued the retained delivery, including both new statement-only nodes, citations.json, the complete predecessor proof and searches.jsonl. The retained receipt identifies prepared head 584ab076642. The first required no-push run rebuilt the overlay on current origin/sheaf-dag and passed at c54aa9e228b. This supersedes the old side-project base; the delivery tool retains the live maintainer-owned review, Lean and audit fields.

I compared the sandbox item with the current read clone. The item statement and all five statement dependencies are identical; the current clone still has the original ten-step proof, whose full arguments remain in this report. The sandbox's substantive changes are the two independent new lemmas, the six-step assembly and the corrected supporting source tag 00NZ. The live parent component-rigidity step 2 still uses precisely this item's minimal-prime kernel inclusion under its stated normal-flatness and polynomial-decomposition hypotheses, so no interface or route changes are needed.

I re-opened every existing statement cited by the assembly: def-weil-pbc-associated-graded-ring (steps 1 and 2), def-weil-pbc-module-tensor-product (step 1), def-pc-standard-graded-algebra (step 2), and lem-weil-pbc-reduced-zerodivisors-union-minimal-primes (step 5). Each entire current statement is byte-identical to the corresponding retained quotation in citations.json; no changed cited statement requires a different argument. The two new statements used in steps 3 and 4 were read in full again, and their unchanged literal quotations still give exactly injective polynomial multiplication and filtered regularity lifting. All seven step/node citation pairs remain valid. The definition statements for Noetherian rings and multivariate polynomials were also re-read, as were the finite-flat, residue-injectivity, Krull-intersection, infinite-field-direction and monic-polynomial supporting statements in the retained takeover arguments.

This review found and repaired a local omission in the extracted assembly: old step 1 defined the maximal ideal of A, but that step now belongs to the lifting lemma, so assembly step 1 had used the undefined symbol \mathfrak n. It now explicitly puts \mathfrak n=\mathfrak m/I before the quotient-tensor calculation. This is a proof-text correction only. All target and new-node statements, searches, quotations and retained predecessor arguments are unchanged. In particular, no new search question arose, and the actual logged searches and their negative or unavailable verdicts were reused rather than re-created.

I re-read Stacks algebra.tex at 00EW/lemma-reduced-ring-sub-product-fields, 00NZ/lemma-finite-flat-local, 00ME/lemma-mod-injective, 00IP/lemma-intersect-powers-ideal-module-zero, 00IQ/lemma-intersection-powers-ideal-module, and the monic triangular equations in 07BV/lemma-colimit-syntomic. The two syntheses remain explicitly agent-written. The corrected assembly uses flatness only in the lifting lemma and reducedness only for the minimal-prime annihilator contradiction. The coordinate convention T_i maps to sum_j M_ij T_j has first column v, so evaluating the transformed top form at (T_1,0,...,0) gives H(v)T_1^n as required. The cases e=0, n=0 in the lifting lemma, I=0, zero-rank graded pieces and nonreduced graded B remain covered by the preceding review. The two new nodes still have empty proof and proof_deps, with no hidden assembly argument moved into a statement's proof sketch. No non-elementary assembly step exceeds 2000 characters and the complete assembly remains below 3000.


## Continued promotion repair: current-base verification

The retained promotion repair was resumed after provider interruptions. Its first dry run in this continuation exited successfully at 6e1f9e91554; the durable receipt confirms completion, so no interrupted delivery was repeated. This continuation re-read the live item, the two sandbox helper statements, the chapter/unit records, the released stage-1 repair order, and every assembly citation. The current read clone still has the ten-step predecessor proof; both extracted helper files remain absent from that DAG. The retained six-step assembly is therefore a substantive split to promote, not an unchanged copy of the live item. Its statement and five statement dependencies agree with the live item. The delivery command rebuilds this overlay on current origin/sheaf-dag while preserving maintainer-owned metadata.

All seven step/node quotations are still exact entire statements, including the four existing statement texts; no cited statement changed relative to the retained quotations. I checked the component-rigidity parent's step 2 again: it supplies reduced Noetherian local R containing Q, I contained in the maximal ideal, flat G, and the graded polynomial decomposition, and consumes exactly the unchanged kernel inclusion. I also re-read the supporting finite-flat-free, residue-injectivity, Krull-intersection, infinite-field-direction and monic-polynomial statements and the algebra.tex source labels 00EW, 00NZ, 00ME, 00IP, 00IQ and 07BV. The source distinctions remain accurate: the two helper results are agent-written syntheses of these inputs.

For the renewed mathematical review, steps 1--2 use the quotient and direct-sum definitions to obtain a representative in I^n intersect p and reduce to positive degree and e>0. Step 3 uses only the polynomial helper's injective multiplication conclusion, with k infinite and the vertex image nonzero. Step 4 uses only the lifting helper's nonzerodivisor conclusion, with the same a and residue initial class h. Step 5 uses the reduced minimal-prime zerodivisor statement, and step 6 explicitly descends the original map on quotient classes. The restored definition of the residue maximal ideal in step 1 remains present. The assembly has 2906 characters, with no non-elementary step over 2000. The I=0 and e=0 cases, n=0 in the lifting helper, zero-rank pieces and B=k[u]/(u^2) in the polynomial helper cause no change to the argument. Logged searches were read and retained because neither statement nor search question changed. No Lean file, compiler or repository mutation was used in this repair.


## Current promotion repair verification, 2026-10-23

The resumed command exited successfully: the initial required dry run prepared a1122644393 on the current server base and printed OK (not pushed). No delivery process remains active. I compared all sandbox item fields with the current read clone: the statement, statement dependencies, blueprint ancestry and maintainer-owned records remain unchanged; the delivered changes remain the two statement-only helpers, the six-step assembly, and the supporting 00NZ source correction. This continues the substantive retained repair rather than reverting to the old ten-step split.

I re-read every assembly citation against the current DAG and both helper statements: all seven quotations are still literal statement substrings. Steps 1--2 use the associated-graded, tensor and standard-grading definitions for the explicit quotient calculation and homogeneous reduction; step 3 has infinite k, positive n and e, and nonzero vertex polynomial as required by the polynomial helper; step 4 has precisely the flat associated graded ring and residue initial form required by the lifting helper; step 5 applies the reduced minimal-prime zerodivisor assertion; step 6 writes the quotient factorization explicitly. The parent component-rigidity step 2 continues to provide all hypotheses and consume exactly the unchanged conclusion. No cited statement changed, so neither the assembly nor its citations need adaptation.

I also re-opened the supporting statements and algebra.tex labels for 00EW, 00NZ, 00ME, 00IP, 00IQ and 07BV. The first-column convention in the polynomial helper gives H(v) as the T_1^n coefficient; coefficients of positive B-degree cannot contribute at that degree. The lifting helper retains the finite-free pieces, residue-matrix left inverse and separated-filtration argument. For n=0 its injective residue scalar is nonzero and a is a unit; for I=0 the only nonzero piece is degree zero. Nonreduced B causes no problem for a scalar-monic polynomial. The assembly also explicitly covers e=0. All predecessor arguments and logged searches were retained and read; no statement or search question changed. A fresh search of WeilConjectures found no attachment, and the Sheaf theorem still contains sorry. The released repair order still requires two new unsplit nodes and an assembly below 3000 characters; these conditions hold. No compiler or Lean-writing action was used.


## Final current-base promotion repair, 2026-10-23

The initial required dry run completed at 59409cdcc8c with preflight passed and OK (not pushed). I checked its completed tool result before any further invocation. This repair retains the delivered proof, both new nodes, all predecessor arguments, citations and actual search logs. Against the current read clone, the live item still has the old ten-step proof and neither helper exists; the substantive promoted changes therefore remain the two unsplit helpers and the six-step assembly, including the earlier correction defining the residue maximal ideal, rather than an unchanged re-push. Only source, proof, proof_deps and split_report differ on the item; the statement, five statement dependencies, blueprint and maintainer-owned records agree with the live item. The delivery tool rebuilds the commit on the current server base.

I re-read every assembly citation and both new statements. Steps 1 and 2 obtain the explicit quotient representatives and homogeneous reduction from the associated-graded, tensor and standard-grading definitions. Step 3 uses the polynomial helper with infinite residue field, positive degree and positive variable count, and a nonzero vertex polynomial; its stated injective multiplication conclusion is exactly what is needed. Step 4 uses the lifting helper with the given Noetherian local ring, ideal inside its maximal ideal, flat associated graded algebra, and the same residue initial form. Step 5 uses the reduced-ring minimal-prime zerodivisor statement to contradict that conclusion. Step 6 explicitly constructs the descended quotient map. All seven step/node quotations remain verbatim; no cited statement changed and no citation adaptation is necessary. The component-rigidity parent step 2 still supplies every hypothesis and consumes exactly the unchanged kernel inclusion.

For both helpers I re-opened the supporting algebra.tex statements and labels 00NZ, 00ME, 00IP, 00IQ, 00EW, and the monic triangular calculation in 07BV. They remain supporting inputs to agent-written syntheses, not claimed sources of the full new statements. The retained polynomial argument has first column v, hence leading scalar H(v), even with nonreduced B; the lifting argument uses finite-free pieces, a lifted left inverse and separated ideal powers. I checked I=0, e=0, degree zero in the lifting statement and zero-rank pieces again. The complete assembly has 2906 characters and no non-elementary step over 2000. A fresh project-source search found no attachment; the existing Sheaf theorem still has sorry. Logged searches and their results were read and reused because neither statements nor search questions changed. The source correction from 00MH to 00NZ and the restored definition of the residue maximal ideal remain present. This addresses the single promotion/rebase return without changing a mathematical interface.
