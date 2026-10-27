# Stage-1 repair report: lem-sfb-admissible-finite-type-field-quotient

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-admissible-finite-type-field-quotient.json`: unchanged statement, five-step assembly.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-fixed-endomorphism-sheaf.json`: statement; Mathlib no exact match; status unsplit.
- `dag/nodes/sec-six-functors-basics/lem-sfb-orbit-invariant-ringed-space-factorization.json`: statement; Mathlib no exact match; status unsplit.
- `dag/nodes/sec-six-functors-basics/lem-sfb-invariant-subalgebra-finite-type-transfer.json`: statement; Mathlib no exact match; status unsplit.
- `dag/nodes/sec-six-functors-basics/lem-sfb-locally-closed-proj-finite-affine.json`: statement; Mathlib no exact match; status unsplit.

## Attachments

No exact project attachment for the whole item. The project theorem and the two admission theorems in `lean/Sheaf/AlgebraicGeometry/AdmissibleFiniteTypeFieldQuotient.lean` remain sorry. The upstream field-only affine-neighbourhood theorems in `WeilConjectures/AlgebraicGeometry/ProjectiveSpace/AffineNeighbourhood.lean` are proved, but do not state the arbitrary-graded-ring ambient refinement D.

## Wanted

None. All sources used are available locally.

## What was wrong and what changed

The returned proof had 8331 characters and did not distribute the work. This repair adds four independent statement-only nodes. No statement dispute, hypothesis change, route change, Lean edit, compilation, repository write or git command was needed. The sandbox initially contained only dispatcher marker files; the current repository supplied the entire returned split, source citations and search records. No older report or searches.jsonl was present to preserve. The existing node search records are retained unchanged. The blueprint ancestor tool returns None, as recorded already; the inherited null ancestor and complete via chain are retained.

## Outstanding work

The four new arguments deliberately remain unsplit, with no proof steps or proof dependencies, for parallel takeover. The item proof is complete relative to them.

## Repair allocation

- Original Steps 1--2 stay as the routine application of existing separated-intersection, coproduct, finite-free, groupoid-orbit and integral-closed-map statements in assembly Step 1. They introduce no additional unsourced lemma.
- A takes the entire fixed-fraction, zero-divisor, restriction-compatibility and affine-sheaf comparison argument of original Step 4; it generalizes to finitely many endomorphisms without group laws. Scheme-chart assembly is retained in Step 2.
- B takes original Steps 3 and 7: orbit topology, invariant sheaf, factorization on sections, locality on stalks, uniqueness and invariant-open restrictions. It applies to arbitrary locally ringed spaces and arbitrary groups; it does not assert scheme quotient existence.
- C takes the substantive algebra of original Steps 5--6 and 8--9: integral generators, Artin--Tate, reduced subrings, image C' of an arbitrary base, Noetherian finiteness of invariants as a submodule, and corestriction of generators. Affine-local scheme assembly remains in Steps 3--4.
- D takes original Step 10: the ambient homogeneous ideal, irrelevant ideal, graded prime avoidance, standard affine chart and closed pullback. Subgroup admissibility remains the elementary subset argument in Step 5.

## Review by Q22

I read the current item and all ten original steps, ILO IX 1.4 on printed pp.132--133 and X 2.3 Step 2 on p.151, Stacks groupoids lemma-points (03BL) and lemma-find-invariant-affine (03JE), algebra lemma-Artin-Tate (00IS), and properties lemma-ample-finite-set-in-affine (01ZY). The chapter and unit were read; this keeps their alteration/quotient route and the original field quotient statement. The existing general admissible-quotient node was inspected for duplicate detection, but its branch is not substituted for the constructive argument.

For A I checked the zero-divisor fraction argument in the original Step 4 against the localization definition, the basic-open sections statement and Schemes lemma-standard-open-affine (01I3). A fixed fraction r/f^n need not have fixed numerator; a common annihilating power over the finite index set is essential. The strengthened endomorphism version remains valid because each endomorphism fixes f and A. The empty family gives A=R, and nilpotent or zero f gives the zero localization. The fixed subsheaf and its canonical identification require compatible basic-open maps, explicitly included in A.

For B I checked the explicit orbit-space construction and the local-factor argument of original Steps 3 and 7 using the definition of a locally ringed-space morphism. Sheaf gluing uses uniqueness in O_X to preserve fixedness. Openness follows from the union of translates, even for an infinite group. A factor on stalks is local because a unit at y pulls back to a unit at any x over y, whereas a germ in the maximal ideal of Z pulls back into the maximal ideal at x. Local rings and local quotient maps are hypotheses of the local-factor clause, supplied by the affine charts in the item; B does not assume or prove scheme representability globally. Empty X and invariant opens cause no exception.

For C I checked Artin--Tate in the local Stacks source and the old integral-generator and Noetherian-submodule inputs. The field is Noetherian; finite e-algebra generators of R also generate it over A and each is integral. This gives R finite over A, then Artin--Tate gives A finite type. In the arbitrary-base clause u must be an e-algebra map: this is why C' contains e. R is finite over C', Artin--Tate makes C' finite type over e, hence Noetherian, and A is a C'-submodule of the finite C'-module R. No Noetherian condition is silently imposed on C or B. Kernels in u, zero R, wild characteristic, nonfaithful actions and nilpotents are allowed.

For D I read all of Stacks 01ZY case (4) and compared the old graded-prime-avoidance argument. If the complement of O is V_+(J), use J intersected with S_+; for every point of E each factor has an element outside its homogeneous prime, so their product lies outside too. A positive homogeneous element avoiding all those primes gives D_+(f) inside O; its closed pullback is affine. The statement retains this ambient refinement over arbitrary graded rings, so the proved upstream field-only neighbourhood theorem is insufficient. Empty E is handled by f=0 in positive degree; nonclosed points and finite fields require no extra assumption.

I opened every node cited in the five assembly steps and read its statement. Step 1 uses separated intersection over Spec e, the exact finite-coproduct spectrum formula, finite-basis implies finite locally free, the groupoid orbit statement for both ordinary and algebraically closed points, integrality of invariant rings and integral-spectrum closedness. Source and target are the finite-free source and its composition with inversion, so all groupoid hypotheses hold. Step 2 uses precisely A's sheaf isomorphism and B's construction and factorization; the scheme definition turns their local affine models into a scheme. Step 3 uses the affine-target criterion, affine-pairs finite type, C's three algebra conclusions and the actual finiteness/finite-type/reducedness definitions. Step 4 uses C's arbitrary-base clause and affine-pairs finite type, with the invariant e-algebra map C to R provided by v; it then uses the finite morphism definition and open fibre-product identification. Step 5 uses D and the given factorization of a locally closed projective-space immersion, with the subgroup assertion a subset observation. The citations file quotes the complete verbatim statements, including every clause used. No step exceeds 2000 characters and the whole assembly is checked against the 3000-character bound.

The Mathlib searches were run only through msearch.py and their actual log entries were read. The second wording was used for every new node. Invariant integrality and fixed-field finiteness do not give C; preserving module finite limits does not identify A's ringed sheaf in one line; the locally ringed-space coequalizer is a useful candidate for B but not its explicit action/orbit/open comparison. Proj affine covers do not give D's simultaneous avoidance. The one rate-limited LeanSearch request is recorded as unavailable.

## Not duplicates

lem-sfb-finite-fixed-endomorphism-sheaf vs lem-weil-pbc-principal-localization-open-immersion: the new statement identifies the common fixed subring and its full canonical sheaf for a finite family of arbitrary ring endomorphisms, including zero divisors; the existing statement supplies only principal affine charts or localization data, with no fixed-endomorphism comparison.
lem-sfb-finite-fixed-endomorphism-sheaf vs lem-weil-pbc-affine-ideals-closed-subscheme: the new statement identifies the common fixed subring and its full canonical sheaf for a finite family of arbitrary ring endomorphisms, including zero divisors; the existing statement supplies only principal affine charts or localization data, with no fixed-endomorphism comparison.
lem-sfb-finite-fixed-endomorphism-sheaf vs lem-weil-pbc-affine-open-section-vanishing-prime: the new statement identifies the common fixed subring and its full canonical sheaf for a finite family of arbitrary ring endomorphisms, including zero divisors; the existing statement supplies only principal affine charts or localization data, with no fixed-endomorphism comparison.
lem-sfb-invariant-subalgebra-finite-type-transfer vs lem-sfb-artin-tate-subalgebra-finite-type: the new statement proves module finiteness over invariants and transfers it to an arbitrary possibly non-Noetherian base via its image; the existing statement gives only Artin--Tate finite type or a scheme properness conclusion for an already given quotient.
lem-sfb-invariant-subalgebra-finite-type-transfer vs lem-sfb-finite-quotient-normal-proper: the new statement proves module finiteness over invariants and transfers it to an arbitrary possibly non-Noetherian base via its image; the existing statement gives only Artin--Tate finite type or a scheme properness conclusion for an already given quotient.
lem-sfb-invariant-subalgebra-finite-type-transfer vs lem-per-artin-tate-subalgebra-finite-type: the new statement proves module finiteness over invariants and transfers it to an arbitrary possibly non-Noetherian base via its image; the existing statement gives only Artin--Tate finite type or a scheme properness conclusion for an already given quotient.
lem-sfb-locally-closed-proj-finite-affine vs lem-pd-projective-finite-affine-neighbourhood: the new statement gives a positive homogeneous ambient standard open inside a prescribed open of Proj for an arbitrary graded ring and its affine closed pullback; the existing statement gives affine neighbourhoods from an ample sheaf or an affine map to projective space, or is a descent theorem.
lem-sfb-locally-closed-proj-finite-affine vs thm-pd-effective-descent: the new statement gives a positive homogeneous ambient standard open inside a prescribed open of Proj for an arbitrary graded ring and its affine closed pullback; the existing statement gives affine neighbourhoods from an ample sheaf or an affine map to projective space, or is a descent theorem.
lem-sfb-locally-closed-proj-finite-affine vs lem-sc-ample-finite-set-affine: the new statement gives a positive homogeneous ambient standard open inside a prescribed open of Proj for an arbitrary graded ring and its affine closed pullback; the existing statement gives affine neighbourhoods from an ample sheaf or an affine map to projective space, or is a descent theorem.

lem-sfb-finite-fixed-endomorphism-sheaf vs lem-sbc-affine-invariant-basic-open-descent: the existing statement assumes a domain and a nonzero denominator and factors maps to affine targets. A allows arbitrary rings and zero divisors, a finite endomorphism family and gives the full canonical sheaf comparison.
lem-sfb-orbit-invariant-ringed-space-factorization vs lem-per-admissible-quotient-affine-integral-charts: B concerns arbitrary locally ringed spaces, arbitrary groups, and conditional locality of the explicit ringed orbit space. It does not construct a scheme quotient or give affine charts, integrality, or orbit fibres.
lem-sfb-locally-closed-proj-finite-affine vs lem-sc-graded-prime-avoidance: the existing statement chooses a homogeneous element of an ideal avoiding finitely many homogeneous primes; D supplies a specified ambient standard open inside O and its affine closed pullback. This is the entire former geometric Step 10, now assigned to a worker as required by the return.

## Returned proof retained verbatim for takeover

### Original step 1

For each orbit $E$, choose an affine open $W$ containing $E$. The finite intersection $W_E=\bigcap_{h\in H}hW$ still contains $E$ and is invariant. Each translate is affine, and repeated application of the separated-affine-intersection lemma over $\operatorname{Spec}e$ shows that $W_E$ is affine. These opens cover $V$. In what follows use the cover consisting of all invariant affine opens, so the argument applies to any such open, not just a selected subcover.

Uses: lem-weil-pbc-separated-affine-open-intersection.
Source: literature/stacks-project/schemes.tex; Tag 01KP, lemma-characterize-separated (1)(a); separatedness simplifies the invariant-neighbourhood input of Tag 03JE.

### Original step 2

Fix an invariant affine $W=\operatorname{Spec}R$ and put $A=R^H=\{r:h(r)=r\text{ for all }h\in H\}$. The action groupoid has arrows $\coprod_{h\in H}W$, source $(h,x)\mapsto x$, target $(h,x)\mapsto hx$, inverse $(h,x)\mapsto(h^{-1},hx)$ and composition $(g,hx)\circ(h,x)=(gh,x)$. The group-action identities give its laws. The finite coproduct is $\operatorname{Spec}(\prod_H R)$. The source corresponds to the diagonal $R\to\prod_HR$, whose module has the coordinate basis indexed by $H$, hence is finite locally free; the target is isomorphic to the source via the inverse map. Thus both hypotheses on source and target in the orbit-fibre lemma hold. That lemma says that $p_W:W\to\operatorname{Spec}A$ is surjective with ordinary and algebraically closed-point fibres precisely the orbits. The finite-invariant-ring lemma says $R$ is integral over $A$; the integral-spectrum closed-map lemma makes $p_W$ closed. It is therefore a topological quotient, and identifies $|W|/H$ homeomorphically with $|\operatorname{Spec}A|$.

Uses: lem-weil-pbc-finite-affine-coproduct-spectrum, lem-weil-pbc-finite-free-algebra-spectrum, lem-a1-affine-groupoid-orbit-fibres, lem-dl-a1-finite-invariant-prime-orbits-residues, lem-weil-pbc-integral-spec-closed-map.
Source: literature/stacks-project/groupoids.tex; Tag 03BL, lemma-points; finite free action groupoid via 02KB; integrality 0BRI and closedness 00GU/00HZ.

### Original step 3

Define the set $|Q|=|V|/H$ with the quotient topology, and let $q$ be the orbit projection. It is open: the inverse image of the image of an open $O$ is $\bigcup_{h\in H}hO$. For an open $T\subseteq |Q|$ define $\mathcal O_Q(T)=\mathcal O_V(q^{-1}T)^H$ with inherited restriction maps. This is a sheaf of rings: glue matching sections in $\mathcal O_V$ and use uniqueness to see that their glue is fixed by every $h$. The inclusions into $\mathcal O_V(q^{-1}T)$ form a map of sheaves. Every invariant open $W$ is saturated, $q^{-1}q(W)=W$; $q(W)$ is open and carries the orbit-space topology of $W$. For an invariant affine $W$, Step 2 consequently identifies $q(W)$ topologically with $\operatorname{Spec}(R^H)$.

Uses: def-weil-locally-ringed-space-morphism.
Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; IX 1.4, pp.132--133, admissible quotient; explicit orbit-space and invariant-sheaf construction supplied here.

### Original step 4

For $A=R^H$ and $f\in A$, the canonical inclusion $A_f\to R_f$ identifies $A_f$ with $(R_f)^H$. Injectivity follows from the fraction equality criterion, since $A\subset R$. For surjectivity, write a fixed fraction as $r/f^n$. For each $h$, fixedness gives an exponent $m_h$ with $f^{m_h}(h(r)-r)=0$. Choose $m$ at least all $m_h$; then $f^mr\in A$ and $r/f^n=(f^mr)/f^{n+m}$. The maps respect restrictions because they are induced by the same inclusions and localization maps. Sections over the inverse image of $D_A(f)$ are $R_f$, by the affine-basic-open section lemma. Hence the canonical map from the structure sheaf of $\operatorname{Spec}A$ to $\mathcal O_Q|_{q(W)}$ is an isomorphism on its basic-open basis. Sheaf gluing gives the isomorphism on every open. Thus $q(W)$ is the affine scheme $\operatorname{Spec}A$ and $q|_W=p_W$ as a morphism of ringed spaces. These opens cover $Q$, so $Q$ is a scheme and $q$ is a scheme morphism, since the maps $p_W$ are local on stalks. Invariant constants $e\to\mathcal O_Q(T)$ give its $e$-structure; on nonempty stalks the map from the field $e$ is local. This makes $q$ an $e$-morphism.

Uses: def-weil-ring-localization-away, lem-weil-pbc-affine-open-section-vanishing-prime, lem-weil-pbc-spec-localization-away-basic-open, def-weil-affine-spectrum, def-pc-scheme, def-weil-locally-ringed-space-morphism.
Source: literature/stacks-project/schemes.tex; Tag 01HV, lemma-spec-sheaves (3),(5), and 01I3, lemma-standard-open-affine; fraction calculation from Algebra 00CO; scheme definition 01IJ.

### Original step 5

The affine opens $q(W)$ have affine inverse images $W$, so the affine-local-target criterion makes $q$ affine. Take any affine open $T=\operatorname{Spec}A$ of $Q$. Its inverse image is now affine, say $\operatorname{Spec}R$, and the sheaf definition gives $A=R^H$ under the canonical map. Since $V$ is locally of finite type over $e$, the affine-pairs criterion says $R$ is a finitely generated $e$-algebra. Choose finitely many $e$-algebra generators $r_1,\ldots,r_n$. The same elements generate $R$ over $A$, because the image of $e$ is in $A$. Each is integral over $A$ by the finite-invariant-ring lemma. The finite-integral-adjoining lemma therefore says $R=A[r_1,\ldots,r_n]$ is a finite $A$-module. This holds for every affine $T$, so the definition of a finite morphism proves $q$ finite. Surjectivity and the geometric-point orbit assertion already hold on the cover by $q(W)$ by Step 2, hence hold globally.

Uses: pqf-lem-affine-local-target, lem-weil-pbc-lft-affine-pairs, lem-dl-a1-finite-invariant-prime-orbits-residues, lem-sc-finite-generated-integral-subring, def-weil-finite-integral-morphism.
Source: literature/stacks-project/algebra.tex; Tag 02JJ, lemma-characterize-finite-in-terms-of-integral (3) => (1), with lemma-characterize-integral; integrality 0BRI; affine-pairs criterion Morphisms 01T2, affine criterion 01S8.

### Original step 6

On each affine $T=\operatorname{Spec}A$ just considered, $R$ is finite type over $e$ and finite as an $A$-module. A field is Noetherian (its only ideals are zero and the unit ideal), so Artin--Tate applied to $e\to A\subseteq R$ gives $A$ of finite type over $e$. These affine charts prove $Q$ locally of finite type, with no finite-cover assumption. If $V$ is reduced, every such $R$ is reduced. An element of its subring $A$ with a zero power is zero already in $R$, hence zero in $A$. Thus all affine rings of $Q$ are reduced, which is the reduced-scheme criterion.

Uses: lem-sfb-artin-tate-subalgebra-finite-type, def-weil-finite-type-morphism, def-pc-reduced-scheme.
Source: literature/stacks-project/algebra.tex; Tag 00IS, lemma-Artin-Tate; reduced-scheme criterion Schemes 01J1.

### Original step 7

Let $a:V\to Z$ be any invariant scheme morphism. Its underlying continuous map factors uniquely through the quotient topology on $|Q|$. For every open $O\subseteq Z$, $a^\sharp$ takes values in $\mathcal O_V(a^{-1}O)^H$, since $a\circ h=a$ as scheme morphisms, so it factors through $\mathcal O_Q$ and defines a ringed-space morphism $b:Q\to Z$. This factor is local: for $y\in Q$ choose $x$ above it. If a germ in the maximal ideal of $\mathcal O_{Z,b(y)}$ mapped to a unit at $y$, its pullback would be a unit at $x$, contradicting locality of $a$. Thus $b$ is a scheme morphism. Uniqueness follows from surjectivity on points and the inclusions of section rings. In particular invariant $e$-morphisms factor by $e$-morphisms, since the two structure composites agree after $q$. The construction on any invariant open $V'\subseteq V$ is literally the restriction of the orbit space and invariant sheaf to $q(V')$. It proves the same universal property there, and Step 4, applied to every invariant affine, gives exactly the asserted affine quotient formula.

Uses: def-weil-locally-ringed-space-morphism.
Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; IX 1.4, pp.132--133, and X 2.3 Step 2, p.151; explicit categorical and invariant-open verification supplied here.

### Original step 8

For the finiteness assertion over $U\subseteq B$, let $b:Q\to B$ be the factor of $v$ from Step 7. Fix an affine open $T=\operatorname{Spec}C$ of $U$. Finiteness of $v^{-1}U\to U$ gives an affine $W=v^{-1}T=\operatorname{Spec}R$ with $R$ a finite $C$-module. It is invariant, so Steps 3--4 give $b^{-1}T=q(W)=\operatorname{Spec}A$ with $A=R^H$. The image $C'\subseteq R$ of $C$ is contained in $A$ because $v$ is invariant, and it contains the image of $e$ because $v$ is an $e$-morphism. The same finite module generators show $R$ is finite over $C'$. The affine-pairs criterion makes $R$ finite type over $e$. Artin--Tate applied to $e\to C'\subseteq R$ gives $C'$ of finite type over $e$. This uses no Noetherian assumption on $C$ or on $B$.

Uses: def-weil-finite-integral-morphism, lem-weil-pbc-lft-affine-pairs, lem-sfb-artin-tate-subalgebra-finite-type.
Source: literature/stacks-project/algebra.tex; Tag 00IS, lemma-Artin-Tate, applied to the image subalgebra of the arbitrary base section ring.

### Original step 9

The finite-type Noetherian-ring lemma makes $C'$ Noetherian. Regard $A\subseteq R$ as a $C'$-submodule; it is stable because $C'\subseteq A$. Since $R$ is finite over $C'$, the Noetherian-submodule lemma makes $A$ finite over $C'$. Those same generators generate $A$ over $C$, since $C\to C'$ is onto. Consequently $b^{-1}T\to T$ is finite for every affine open $T$ of $U$. By the definition of a finite morphism, $Q\times_B U=b^{-1}U\to U$ is finite. The equality denotes the usual canonical identification of the inverse image of an open with its fibre product.

Uses: lem-weil-pbc-finite-type-algebra-noetherian, lem-weil-pbc-noetherian-submodule-finite, def-weil-finite-integral-morphism, def-pc-fibre-product.
Source: literature/stacks-project/algebra.tex; Tags 00FN, lemma-Noetherian-permanence, and 00IK, lemma-Noetherian-basic; Morphisms finite definition.

### Original step 10

Finally suppose $V$ has a locally closed immersion into $\mathbf P^n_e=\operatorname{Proj}S$, $S=e[x_0,\ldots,x_n]$. Factor it as a closed immersion into an open $O$ of $\operatorname{Proj}S$. For a finite nonempty subset $E\subseteq V$, write the complement of $O$ as $V_+(J)$ for a homogeneous ideal $J$, and let $I=J\cap S_+$. For each homogeneous prime corresponding to a point of $E$, $I$ is not contained in that prime: $J$ is not contained in it and neither is $S_+$, so the product of a member of each outside the prime belongs to $I$ and is outside it. Graded prime avoidance supplies a positive-degree homogeneous $f\in I$ missing all those primes. Then $D_+(f)$ is affine, contains the image of $E$ and is contained in $O$. Its inverse image in $V$ is affine, by the affine description of a closed immersion, and contains $E$. The empty set is contained in the empty affine open. In particular every finite-group orbit lies in an affine open. Every subgroup orbit is a subset of the corresponding whole-group orbit, so the same assertion holds for subgroup actions (indeed this last observation holds for any admissible action).

Uses: def-pc-proj, lem-sc-graded-prime-avoidance, lem-sc-proj-standard-open-basis, def-weil-closed-immersion.
Source: literature/stacks-project/properties.tex; Tag 01ZY, lemma-ample-finite-set-in-affine, case (4), with Algebra 00JS and Constructions 01MB; ILO IX 1.4 for subgroup admissibility.

