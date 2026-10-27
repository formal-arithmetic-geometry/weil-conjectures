## Worker report

Repair of the landing return for lem-a1-affine-groupoid-orbit-fibres, group NM, returned head 9eb5adb4a65. This retry retained the complete delivered sandbox, including all three new nodes, the four-step parent, report, citation quotes and actual search log. The original attempt recovered the ten-step proof into original-item.json; that complete JSON is still identical to the current live item. The current released stage-1 repair note explicitly reopens this otherwise split-and-reviewed node and requires at least two separate tasks and an assembly proof of at most 3000 characters. The delivery tool rebases the retained split onto current origin/sheaf-dag, preserving its current maintainer-owned fields.

Files written under dag/nodes/sec-purity-real-sheaves/:

- lem-a1-affine-groupoid-orbit-fibres.json: unchanged statement and statement dependencies; four-step assembly, 2198 text characters.
- lem-a1-affine-groupoid-basechange-polynomial-norm.json: statement, unsplit, no Mathlib match. Carries the scalar-extended groupoid, local determinant specialization, and polynomial invariant-coefficient norm identity (old steps 3–5).
- lem-a1-affine-groupoid-norm-prime-separation.json: statement, unsplit, no Mathlib match. Carries the finite source fibre and its rational points, prime-avoidance separation, and the two local norm evaluations (old steps 6–8).
- lem-a1-affine-groupoid-common-algebraic-closure-lifts.json: statement, unsplit, no Mathlib match. Carries arbitrary algebraically closed lifts and simultaneous prescribed-prime lifts through residue fields (old steps 2 and 10, using the lying-over input of old step 1).

citations.json contains the verbatim statement of every node used in each of the four parent steps. Searches are in searches.jsonl. The original proof and its citations are preserved verbatim below as the detailed handoff for the three tasks; original-item.json preserves the complete recovered JSON for comparison. repair.py is the sandbox-only generation script.

Attachments: none. Searching lean/WeilConjectures by the blueprint tag, affine groupoid, invariant norm and orbit terminology produced no declaration proving this item. lean/Sheaf/AlgebraicGeometry/AffineGroupoidOrbitFibres.lean:171–193 ends in sorry. The private norm_tmul_one in WeilConjectures/AlgebraicGeometry/FiniteLocallyFreeNormCharts.lean:31–37 proves only free-algebra scalar extension, without the invariant-coefficient or geometric-separation conclusions; it is not an attachment.

WANTED: none. The sources used are present locally.

The defect was granularity: the ten-step proof was one 7842-character work item despite containing several independently provable arguments. No mathematical statement or target is corrected. The parent statement and all its hypotheses remain byte-for-byte unchanged. The current historical blueprint ancestry is retained, including its inherited chapter/unit: the ancestor lem-a1-affine-hc0 now has a different current compact-support statement, but the stored historical Tag 03XX quotient support branch is the route being repaired. No chapter/unit file or Lean file was written, no compiler was run, and no agent was started.

## Review by NM

This retry addresses the actual landing refusal in coord/returns/NM.md (2026-10-22 12:46 UTC): the side project's completion had not been promoted to the live DAG. I compared the retained delivered version identified by delivery.log (head 9eb5adb4a65), its original-item.json baseline, and every field of the current live item. The live item equals that original baseline exactly, rather than the retained four-step split. None of the three new node ids exists in the current live DAG. The current released repair note still orders this re-split, so the older reviewed record does not supersede it. I revised this report and the parent's split_report to make the live rebase and current four-step mapping explicit; this is the promotion repair requested, preserving the reader-approved mathematics.

I re-opened the live statements for integral-invariants, integral-injective-lying-over, module-base-change and affine-spectrum, and the three retained new statements. Every one of the ten step/node citation pairs still has its full verbatim quote in the actual current statement; no changed interface requires a different argument. I also re-read all definition dependencies, including the norm-charts node: it supplies local finite-free charts for finite flat locally finitely presented maps without a constant-rank hypothesis. For step 1 the integral-invariants hypothesis matches the functorial groupoid and both finite locally free maps, and the inclusion is injective by its definition. Step 2 receives a groupoid of k-schemes from scalar extension, precisely the input of norm separation; the maps alpha_j fix k, so they agree on each scalar norm. Step 3 uses only pure tensors, the affine ring-map correspondence and the assumed groupoid laws. Step 4 uses the prescribed kernels in clause (2), not just an unspecified pair of lifts. I re-read the local Stacks proofs 03BH, 03BK, 03BL and 0BD2 and the logged Mathlib search results. No statement or search question changed, so I reused the successful logged searches rather than repeating them.

The initial required dry run on the retained split exited successfully at 1da47b4d436. The final dry run and push must follow these report/split_report repairs; only one invocation is kept active at a time. The live item, all its source hypotheses, the three independent tasks, and the full ten-step argument handoff below are retained. No source discrepancy, new mathematical correction, unquoted citation, step above 2000 characters or unauthorized SGA route was found.

I read Stacks groupoids.tex, groupoids-lemma-points (Tag 03BL), including the two surjectivity arguments, finite list of arrows, prime avoidance, norm contradiction, and final common-algebraic-closure argument. The item states all of its assertions. The endpoint order differs from the displayed first clause of Stacks; the inverse arrow reconciles it. I also read groupoids-lemma-invariants-base-change (03BK), especially its base-change groupoid and polynomial lifting argument, groupoids-lemma-determinant-trick (03BH), and divisors-lemma-finite-locally-free-has-norm (0BD2). The latter constructs local multiplication determinants and explicitly states arbitrary base-change compatibility; its printed statement assumes fixed positive degree, so the new norm statements instead use the existing norm-charts node, which allows varying degree. The chartwise matrix argument in the old proof works without a global rank. I read algebra-lemma-silly (00DS) as well: the source-fibre list is nonempty thanks to the identity, so the existing prime-avoidance node's r >= 1 condition is met.

For the first new node, I checked the full functorial groupoid input against 03BH/03BK, not just a finite group action special case. C has equal source and target maps, so every groupoid map is over Spec C; the base-change structure maps obey the same identities. Finite, flat, and locally finite presentation have their separate existing permanence statements, all of which were read. This preserves exactly the hypotheses of invariant-norm after adjoining polynomial variables or extending scalars. On a pulled-back free chart, the multiplication matrix is the entrywise scalar extension, so the determinant permutation formula gives the same norm after any substitution. For f = sum a_j tensor d_j, the invariant polynomial norm G has coefficients in C; substitution sends it to 1 tensor d[T](G)(d_j). This is the precise equality the parent uses, and does not claim that all invariants commute with nonflat base change. The full old determinant and polynomial argument is assigned to this node, not silently removed. Its future worker can reuse invariant-norm or iterate the existing one-variable polynomial-norm node. The new node is strictly more about scalar specialization, not another statement that G is invariant.

For the second new node, I read the statements of the affine tensor formula, finite-fibre theorem, finite-implies-integral theorem, integral-prime-over-maximal theorem, closed-point-residue-field theorem, prime avoidance, local norm charts, and norm prime criterion. These say precisely what old steps 6–8 take: E_1 is the finite-dimensional source-fibre algebra, its primes are all closed, and their residue fields are k, giving all and only the beta maps. A finite k-module generating set generates it as a k-algebra, so no finite-type hypothesis on A/k is needed for the closed-point argument. Distinct surjective k-algebra maps A -> k have distinct maximal kernels, because an identification of the quotient with k fixing k is unique; distinct maximal ideals do not contain one another. Prime avoidance supplies f. At alpha_1 all source-fibre primes avoid tau(f); at alpha_0 the identity arrow is a prime killing tau(f). Separate local free charts and the norm prime criterion then give alpha_1(g) != 0 and alpha_0(g) = 0. This lemma assumes there is no arrow but does not assume equality of invariant values; it supplies a separating norm, rather than restating the parent's fibre conclusion.

For the third new node, I read the integral residue-extension leaf, the integral-injective lying-over statement, the algebraic-extension embedding statement, and the definitions of residue fields, affine spectra, field extension and algebraic closure. Algebraicity applies to each prime over its contraction without Noetherian or finite hypotheses. For an arbitrary d:C -> k, the field k is not required to be algebraic over kappa(ker d): only kappa(q)/kappa(p) must be algebraic for the embedding theorem. The fraction formula gives the fixed embedding of kappa(p), and extending it makes the final map restrict exactly to d. For two prescribed primes the field k is one chosen algebraic closure of their common base residue field; the two extensions are taken relative to this same fixed inclusion. The resulting ring maps retain their prescribed kernels. These two lifting tasks belong to arbitrary integral inclusions, not just to groupoids, and neither asserts any orbit conclusion.

Parent step 1 uses the integral-invariants node with exactly the original groupoid hypotheses, lying over with the genuinely injective displayed subring inclusion, and clause (1) of the new lifting statement. Each quoted statement provides the claimed result. This proves both surjectivities without a hidden existence step.

Parent step 2 uses the first new node to obtain the actual finite locally free base-changed groupoid and the scalar norm, and the second new node for its contradictory evaluations if an arrow is absent. The tensor maps alpha_j are well defined because the a_j agree on C, and fix the scalar k. The new separation lemma needs k-algebra structure maps; the new base-change lemma supplies them. No claim about all base-changed invariants is made.

Parent step 3 is elementary: tensor restriction/extension on pure tensors gives the arrow correspondence; equal source/target restrictions on C show preservation; the assumed identity, inverse and composition establish the equivalence relation. Its cited module-base-change and affine-spectrum definitions actually give these maps. It uses the groupoid laws already assumed in the item and obtained by step 2, not an uncited groupoid theorem.

Parent step 4 uses clause (2) of the new lifting statement for exactly the primes representing u_0,u_1 and the inclusion shown integral in step 1. The affine-spectrum definition identifies underlying points with kernels and the morphisms with inverse images, so the arrow has the required endpoints. Conversely equality of C -> B makes the contractions equal. Both directions of the ordinary-fibre assertion remain present.

Small cases checked: C=A=B=0 makes the point and field-map assertions vacuous; a trivial groupoid gives a scalar fibre k and no possible pair of unequal objects there. A finite pair groupoid on two k-points gives the same norm at either object, illustrating the scalar assertion. The disjoint identity groupoid on A=k x k has two distinct orbits: f=(0,1) separates them and the norm is f, confirming that the separation lemma itself must not impose equal invariant values. Nonreduced finite source fibres such as k[epsilon]/(epsilon^2) still have finitely many primes with residue field k; the norm criterion detects units, so no reducedness/domain hypothesis was smuggled in. Purely inseparable residue-field extensions cause no problem for algebraically closed embeddings. Ranks may vary across components, and an object with an identity arrow cannot have a rank-zero source fibre. The m=0 polynomial expression is covered by the empty-variable polynomial ring; over the zero scalar ring all identities hold in the zero ring.

I checked B1–B10 and C1–E7 against the actual files. All three new nodes have complete hypotheses and their own objects, only statements with empty proof/proof_deps, explicit sources, TeX and definition dependencies, actual logged semantic/Loogle/source searches with a second semantic phrasing, and blueprint ancestry with the precise historical proof place. The whole DAG was searched by tags 03BL, 03BK, 03BH, 0BD2 and by groupoid/norm/separation/lifting terminology; the whole imported blueprint was searched using blueprint_refs.py for groupoid, groupoid norm, finite groupoid, norm polynomial, norm separation, integral algebraically, integral spectrum, and common algebraic closure. None states these new interfaces. The tag-sharing pairs are individually distinguished below. I checked the candidate Mathlib norm_eq_zero_iff at RingTheory/Norm/Basic.lean:95–113: it assumes domains and does not cover the source-fibre product/nonreduced algebra. I checked IsAlgClosed.lift at FieldTheory/IsAlgClosed/Basic.lean:350–357: it is an embedding for algebraic domain extensions; the new integral-ring statement still needs lying over, quotient/residue fields and kernel control. The searches found no exact or one-line specialization for any new node. All relevant new statements are strictly smaller than the item, and their proof work is comparable in size (old steps 3–5, 6–8, and 2/10 respectively). There is no new node that combines all the work or simply rephrases a fibre clause. No SGA route is cited.

Repair of the specific return: (1) three new nodes are delivered statement-only with source and actual three-kind searches; (2) the parent's statement is unchanged and its proof has 2198 characters, below 3000; (3) the three tasks are separate arguments and every old proof step is mapped and retained verbatim below, including all of its existing citations; (4) old step 9 remains explicitly as elementary assembly in parent step 3. The two long arguments become independent work items; the parent is a short contradiction and transfer. No old argument was shortened away to satisfy the size gate. No unfinished work remains within this stage-1 repair, subject to the required server dry run and delivery.

## Not duplicates

lem-a1-affine-groupoid-basechange-polynomial-norm vs lem-a1-affine-groupoid-polynomial-norm-invariant: the existing result gives the invariant polynomial norm over A[T]; it does not identify arbitrary tensor-element norms with evaluated scalar polynomials after a nonflat invariant-base extension.

lem-a1-affine-groupoid-basechange-polynomial-norm vs lem-a1-affine-groupoid-invariant-norm: the existing result asserts source/target invariance of a norm on the original groupoid; it states neither scalar specialization nor finite-fibre prime-avoidance separation.

lem-a1-affine-groupoid-basechange-polynomial-norm vs lem-a1-affine-groupoid-orbit-fibres: the parent asserts surjectivity and orbit fibres; this node supplies a separate algebraic lifting, scalar specialization, or norm-separation argument used to prove that conclusion, and asserts no orbit-fibre identification.

lem-a1-affine-groupoid-basechange-polynomial-norm vs lem-a1-integral-residue-extension-algebraic: the existing Mathlib leaf asserts only algebraicity of residue-field extensions; it does not select primes, lift maps to algebraically closed fields, control both prescribed kernels, or prove a norm identity.

lem-a1-affine-groupoid-basechange-polynomial-norm vs lem-sfb-sylow-generic-prime-to-ell-lift: the existing result selects a generic point of prime-to-ell degree for finite-group quotient data on normal finite-type schemes; it assumes orbit fibres, and gives none of the present groupoid norm identities or arbitrary integral-inclusion lifts.

lem-a1-affine-groupoid-basechange-polynomial-norm vs lem-sfb-generic-invariant-field-orbit-open: the existing result shrinks a generically finite projective map with a finite constant group action and purely inseparable invariant function fields; it does not handle arbitrary affine finite locally free groupoids, separating norms, or general integral-ring point lifts.

lem-a1-affine-groupoid-basechange-polynomial-norm vs lem-sfb-finite-quotient-generic-fields: the existing result identifies invariant generic fields for normal Noetherian schemes with a finite constant group action and assumes orbit fibres; it does not construct norm specialization or integral-inclusion point lifts.

lem-a1-affine-groupoid-basechange-polynomial-norm vs lem-per-torsor-subgroup-quotient-finite-etale: the existing result gives a connected finite etale subgroup quotient and geometric fibre degree for a Galois torsor; it does not give scalar norm specialization or residue-field lifts of arbitrary integral inclusions.

lem-a1-affine-groupoid-basechange-polynomial-norm vs lem-per-admissible-quotient-affine-integral-charts: the existing result constructs quotients for admissible actions of a finite constant group; it does not cover arbitrary scheme groupoids, provide the polynomial norm scalar identity, supply a separating norm, or state general integral-inclusion lifts with prescribed kernels.

lem-a1-affine-groupoid-basechange-polynomial-norm vs lem-pur-finite-flat-kummer-norm-degree: the existing result concerns norms of line bundles, Kummer compatibility and curve degrees under Noetherian hypotheses; it states no groupoid norm or geometric-orbit separator.

lem-a1-affine-groupoid-norm-prime-separation vs lem-a1-affine-groupoid-invariant-norm: the existing result asserts source/target invariance of a norm on the original groupoid; it states neither scalar specialization nor finite-fibre prime-avoidance separation.

lem-a1-affine-groupoid-norm-prime-separation vs lem-a1-affine-groupoid-orbit-fibres: the parent asserts surjectivity and orbit fibres; this node supplies a separate algebraic lifting, scalar specialization, or norm-separation argument used to prove that conclusion, and asserts no orbit-fibre identification.

lem-a1-affine-groupoid-norm-prime-separation vs lem-a1-integral-residue-extension-algebraic: the existing Mathlib leaf asserts only algebraicity of residue-field extensions; it does not select primes, lift maps to algebraically closed fields, control both prescribed kernels, or prove a norm identity.

lem-a1-affine-groupoid-norm-prime-separation vs lem-sfb-generic-invariant-field-orbit-open: the existing result shrinks a generically finite projective map with a finite constant group action and purely inseparable invariant function fields; it does not handle arbitrary affine finite locally free groupoids, separating norms, or general integral-ring point lifts.

lem-a1-affine-groupoid-norm-prime-separation vs lem-per-admissible-quotient-affine-integral-charts: the existing result constructs quotients for admissible actions of a finite constant group; it does not cover arbitrary scheme groupoids, provide the polynomial norm scalar identity, supply a separating norm, or state general integral-inclusion lifts with prescribed kernels.

lem-a1-affine-groupoid-norm-prime-separation vs lem-pur-finite-flat-kummer-norm-degree: the existing result concerns norms of line bundles, Kummer compatibility and curve degrees under Noetherian hypotheses; it states no groupoid norm or geometric-orbit separator.

lem-a1-affine-groupoid-common-algebraic-closure-lifts vs lem-a1-affine-groupoid-orbit-fibres: the parent asserts surjectivity and orbit fibres; this node supplies a separate algebraic lifting, scalar specialization, or norm-separation argument used to prove that conclusion, and asserts no orbit-fibre identification.

lem-a1-affine-groupoid-common-algebraic-closure-lifts vs lem-a1-integral-residue-extension-algebraic: the existing Mathlib leaf asserts only algebraicity of residue-field extensions; it does not select primes, lift maps to algebraically closed fields, control both prescribed kernels, or prove a norm identity.

lem-a1-affine-groupoid-common-algebraic-closure-lifts vs lem-sfb-generic-invariant-field-orbit-open: the existing result shrinks a generically finite projective map with a finite constant group action and purely inseparable invariant function fields; it does not handle arbitrary affine finite locally free groupoids, separating norms, or general integral-ring point lifts.

lem-a1-affine-groupoid-common-algebraic-closure-lifts vs lem-per-admissible-quotient-affine-integral-charts: the existing result constructs quotients for admissible actions of a finite constant group; it does not cover arbitrary scheme groupoids, provide the polynomial norm scalar identity, supply a separating norm, or state general integral-inclusion lifts with prescribed kernels.

lem-a1-affine-groupoid-common-algebraic-closure-lifts vs lem-weil-pbc-integral-injective-lying-over: lying over supplies only a prime; the new statement supplies compatible residue-field embeddings, field-valued maps and their prescribed kernels.

lem-a1-affine-groupoid-common-algebraic-closure-lifts vs lem-weil-pbc-algebraic-extension-embeds-algebraically-closed: the existing field theorem takes an algebraic field extension as input; the new statement starts from an arbitrary integral inclusion and includes prime choice, passage to residue fields, and agreement of maps on C.

lem-a1-affine-groupoid-norm-prime-separation vs lem-pd-finite-free-norm-prime-criterion: the existing criterion tests one element against primes of a finite free algebra. The new statement enumerates all geometric source arrows, chooses f by prime avoidance, and obtains two different norm evaluations using the identity arrow and separate local charts.

## Argument handoff: all ten returned steps, verbatim

These are archived work instructions, not proof steps placed in the statement-only nodes. Each future worker has a self-contained theorem statement in its node and the complete original argument here. Existing nodes below remain reusable; they are not new proof dependencies of an unsplit node.

### Returned step 1

Assigned to: Parent step 1 retains integral invariants and lying over; its prime choice is also input to common-algebraic-closure-lifts (1).

Apply [lem-a1-affine-groupoid-integral-invariants] with the given groupoid: $C\hookrightarrow A$ is integral. It is injective because $C$ is the displayed subring of $A$. Lying over [lem-weil-pbc-integral-injective-lying-over] therefore gives a prime of $A$ over every prime of $C$, proving surjectivity of $|U|\to|M|$. This includes $A=0$, when both spectra are empty.

Existing citations: lem-a1-affine-groupoid-integral-invariants, lem-weil-pbc-integral-injective-lying-over.

### Returned step 2

Assigned to: common-algebraic-closure-lifts (1).

Fix an algebraically closed field $k$ and a map $c:C\to k$. Put $\mathfrak p=\ker c$. Lying over supplies $\mathfrak q\subset A$ over $\mathfrak p$. The map $c$ extends to $\kappa(\mathfrak p)\to k$ by sending a fraction to the quotient of its images. By [lem-a1-integral-residue-extension-algebraic], $\kappa(\mathfrak q)/\kappa(\mathfrak p)$ is algebraic. Apply [lem-weil-pbc-algebraic-extension-embeds-algebraically-closed] to extend that embedding to $\kappa(\mathfrak q)\to k$. Composing $A\to\kappa(\mathfrak q)\to k$ lifts $c$. The affine spectrum correspondence identifies this with a $k$-point of $U$ over the prescribed $k$-point of $M$.

Existing citations: lem-a1-affine-groupoid-integral-invariants, lem-weil-pbc-integral-injective-lying-over, lem-a1-integral-residue-extension-algebraic, lem-weil-pbc-algebraic-extension-embeds-algebraically-closed, def-weil-affine-spectrum.

### Returned step 3

Assigned to: basechange-polynomial-norm: its base-changed groupoid and local freeness; parent step 2 writes the alpha_j maps.

To compare two lifts $a_0,a_1:A\to k$ of $c$, form $A'=A\otimes_C k$, $B'=B\otimes_C k$ and $\sigma',\tau':A'\to B'$. The affine tensor-product base-change formula [lem-sbc-finite-affine-tensor-base-change], with one summand, identifies these with the schemes obtained by base change from $M$ to $\operatorname{Spec}k$. The structure maps are over $M$: the two maps from $R$ agree on $C$; also $s\circ e=t\circ e=1$, inversion interchanges $s,t$, and composition preserves the common $M$-image. Thus their base changes satisfy the same groupoid identities. The maps $a_j$ extend to $k$-algebra maps $\alpha_j:A'\to k$, $\alpha_j(a\otimes\lambda)=a_j(a)\lambda$. Finite, flat, and locally finite presentation are separately preserved by arbitrary base change by the three cited permanence statements, so $s',t'$ satisfy exactly the finite locally free definition. On each local free norm chart, tensoring a basis gives a basis over the new ring. This also gives the chartwise multiplication matrices used below.

Existing citations: lem-sbc-finite-affine-tensor-base-change, lem-pd-finite-locally-free-norm-charts, def-weil-finite-integral-morphism, def-pc-fibre-product, def-weil-module-base-change, lem-weil-pbc-finite-morphism-permanence, lem-weil-pbc-flat-morphism-base-change, lem-weil-pbc-qcqs-morphism-permanence, def-pc-finite-locally-free.

### Returned step 4

Assigned to: basechange-polynomial-norm: determinant compatibility with arbitrary substitution.

Use the norm sections of [lem-pd-finite-locally-free-norm-charts]. Their compatibility with scalar extension is a direct determinant calculation: on a free chart the matrix of multiplication by $b\otimes1$ is obtained by applying the scalar ring map to every entry of the matrix for $b$. The permutation-sum formula for the determinant [def-weil-endomorphism-determinant] therefore gives $N(b)\otimes1=N(b\otimes1)$. The same calculation holds after any substitution in a polynomial ring. It holds globally since the pulled-back free charts cover and the norm sections restrict to these determinants. No freeness on the whole affine scheme or constant rank is needed.

Existing citations: lem-pd-finite-locally-free-norm-charts, def-weil-endomorphism-determinant, def-weil-module-base-change.

### Returned step 5

Assigned to: basechange-polynomial-norm: invariant polynomial G and its scalar evaluation.

For any $f\in A'$ write $f=\sum_{j=1}^m a_j'\otimes\lambda_j$ and put $F=\sum_j a_j'T_j\in A[T_1,\ldots,T_m]$. Extend the original groupoid by adjoining these same polynomial variables to both rings. This is its product with affine $m$-space over $\operatorname{Spec}\mathbf Z$, hence still a groupoid with finite locally free source and target (finite, flat and locally finite presentation are preserved separately as in step 3). Apply [lem-a1-affine-groupoid-invariant-norm] to obtain $G=N_{\sigma[T]}(\tau[T](F))\in C[T_1,\ldots,T_m]$: polynomial source and target images agree exactly when their coefficients agree. Substitute $a\mapsto a\otimes1$ and $T_j\mapsto1\otimes\lambda_j$. By step 4 the resulting element is $g=N_{\sigma'}(\tau'(f))\in A'$. Since every coefficient of $G$ belongs to $C$, this substitution sends $G$ to the scalar $c[T](G)(\lambda_1,\ldots,\lambda_m)\in k\subset A'$. Consequently $\alpha_0(g)=\alpha_1(g)$. This proves the needed scalar equality for these particular norms directly, without assuming invariants commute with nonflat scalar extension.

Existing citations: lem-a1-affine-groupoid-invariant-norm, lem-pd-finite-locally-free-norm-charts, def-weil-endomorphism-determinant, def-weil-module-base-change, lem-weil-pbc-finite-morphism-permanence, lem-weil-pbc-flat-morphism-base-change, lem-weil-pbc-qcqs-morphism-permanence.

### Returned step 6

Assigned to: norm-prime-separation: finite nonempty source-arrow list and all residue fields.

Let $D_1=B'\otimes_{A',\alpha_1}k$, using $\sigma'$ for the $A'$-algebra structure. The affine tensor formula identifies $\operatorname{Spec}D_1$ with the source fibre of $s'$ over $\alpha_1$. It is finite-dimensional over $k$ by tensoring finite module generators of $B'$; hence its structure morphism is finite and it has finitely many points by [lem-weil-pbc-finite-closed-map-finite-fibres]. Finite implies integral by [pqf-lem-finite-integral-lft], and every prime over the maximal ideal $(0)$ of $k$ is maximal by [lem-weil-pbc-integral-prime-over-maximal-maximal]. Also $D_1$ is finitely generated as a $k$-algebra (a finite module generating set already generates it as an algebra), so [lem-weil-pbc-closed-point-residue-field-base] gives residue field $k$ at each of these closed points. Thus the points correspond to a finite list of all $k$-algebra maps $\beta_i:B'\to k$ with $\beta_i\sigma'=\alpha_1$. This list is nonempty because it contains the identity arrow at $\alpha_1$.

Existing citations: lem-sbc-finite-affine-tensor-base-change, def-weil-finite-integral-morphism, lem-weil-pbc-finite-closed-map-finite-fibres, pqf-lem-finite-integral-lft, lem-weil-pbc-integral-prime-over-maximal-maximal, lem-weil-pbc-closed-point-residue-field-base.

### Returned step 7

Assigned to: norm-prime-separation: distinct maximal kernels and prime avoidance.

Suppose no arrow has source $\alpha_1$ and target $\alpha_0$. For the finite list in step 6 put $\alpha_i'=\beta_i\tau'$, $\mathfrak m_i=\ker\alpha_i'$ and $\mathfrak m_0=\ker\alpha_0$. These kernels are maximal because all the maps are $k$-algebra maps to $k$, hence surjective. The kernels are unequal: two such maps with the same kernel identify the quotient with $k$ identically on its subfield $k$, so are equal, contrary to the assumption. Distinct maximal ideals do not contain each other, so $\mathfrak m_0\not\subset\mathfrak m_i$ for each $i$. Prime avoidance [lem-weil-pbc-prime-avoidance] therefore supplies $f\in\mathfrak m_0$ outside all $\mathfrak m_i$. Equivalently, $\alpha_0(f)=0$ whereas $\alpha_i'(f)\ne0$ for every $i$.

Existing citations: lem-weil-pbc-prime-avoidance.

### Returned step 8

Assigned to: norm-prime-separation: two local norm-prime evaluations.

Apply the local norm prime criterion [lem-pd-finite-free-norm-prime-criterion] to $\tau'(f)$. More explicitly, choose a free affine norm chart around the point $\ker\alpha_1$; restriction does not change its source fibre, so all primes over this point are the points listed in step 6. At each of them the value of $\tau'(f)$ is $\beta_i\tau'(f)=\alpha_i'(f)\ne0$. The criterion and the chart description of the norm imply $\alpha_1(g)\ne0$ for $g=N_{\sigma'}(\tau'(f))$. Around $\ker\alpha_0$ use another free norm chart. The identity arrow at $\alpha_0$ is a prime in its source fibre and evaluates $\tau'(f)$ to $\alpha_0(f)=0$. The same criterion gives $\alpha_0(g)=0$. This contradicts the scalar equality in step 5. Thus an arrow with source $\alpha_1$ and target $\alpha_0$ exists.

Existing citations: lem-pd-finite-free-norm-prime-criterion, lem-pd-finite-locally-free-norm-charts.

### Returned step 9

Assigned to: Parent step 3 retains the tensor arrow correspondence and equivalence relation assembly.

A $k$-arrow in the scalar-extended groupoid gives an original $k$-arrow by precomposing $B\to B'$. Conversely an original $k$-arrow $\gamma:B\to k$ whose endpoints restrict to $c$ extends by $b\otimes\lambda\mapsto\gamma(b)\lambda$, so step 8 gives an arrow relating any two original lifts. An arrow always preserves the restrictions to $C$ since $\sigma|_C=\tau|_C$. Identity, inverse and composition in $R(k)\rightrightarrows U(k)$ make the relation of being joined by one arrow reflexive, symmetric and transitive. Therefore it equals the equivalence relation generated by $s,t$, and steps 2 and 8 prove exactly the surjectivity and fibre assertion on $k$-points.

Existing citations: def-weil-affine-spectrum, def-weil-module-base-change.

### Returned step 10

Assigned to: common-algebraic-closure-lifts (2); parent step 4 retains passage from the geometric arrow to its ordinary point and the converse.

Finally let $u_0,u_1\in|U|$ have the same image $m\in|M|$. By integrality and [lem-a1-integral-residue-extension-algebraic], both $\kappa(u_j)/\kappa(m)$ are algebraic. Choose an algebraic closure $k$ of $\kappa(m)$ [def-weil-algebraic-closure]. By [lem-weil-pbc-algebraic-extension-embeds-algebraically-closed] embed both residue fields into this same $k$, extending its fixed inclusion of $\kappa(m)$. The composites $A\to\kappa(u_j)\to k$ have underlying points $u_j$ and the same restriction $C\to\kappa(m)\to k$. By step 9 they are joined by a $k$-arrow. Its underlying point in $R$ has the two required endpoints; invert the arrow if necessary to match the order $s(r)=u_0$, $t(r)=u_1$. Conversely, an underlying point $r\in|R|$ has equal $M$-images under $s,t$, since the two ring maps $C\to B$ are equal. Together with step 1 this proves the entire assertion on ordinary points.

Existing citations: lem-a1-affine-groupoid-integral-invariants, lem-a1-integral-residue-extension-algebraic, def-weil-algebraic-closure, lem-weil-pbc-algebraic-extension-embeds-algebraically-closed, def-weil-affine-spectrum.

## Search evidence and candidate reading

All mathlib_searches entries in the delivered nodes refer to actual commands logged in this item's searches.jsonl. Two semantic formulations were read for every new node, plus LeanSearch, Loogle and a source grep. The top-hit summaries are copied from that log; none is reported as unavailable because these actual searches succeeded. Some exploratory Loogle patterns returned no hits or an identifier diagnostic; the delivered combined patterns all returned zero hits without a service failure. The initial broad results for norm separation returned unrelated separatedness declarations, and the ring-lifting results returned existing ingredients rather than the combined statement. No unrun search is recorded as evidence.
