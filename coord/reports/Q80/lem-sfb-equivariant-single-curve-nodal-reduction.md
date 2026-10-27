# Q80 repair: lem-sfb-equivariant-single-curve-nodal-reduction

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-equivariant-single-curve-nodal-reduction.json: unchanged statement; six-step assembly, 2698 characters; status split.
- dag/nodes/sec-six-functors-basics/lem-sfb-genus-raising-equivariant-stable-model.json: statement, unsplit; no Mathlib match, no proof steps or proof dependencies.
- dag/nodes/sec-six-functors-basics/lem-sfb-equivariant-stable-model-evaluation.json: statement, unsplit; no Mathlib match, no proof steps or proof dependencies.
- dag/nodes/sec-six-functors-basics/lem-sfb-curve-field-kernel-invariant-tower.json: statement, unsplit; no Mathlib match, no proof steps or proof dependencies.
- dag/nodes/sec-six-functors-basics/lem-sfb-quasisplit-regular-constant-alteration.json: statement, unsplit; no Mathlib match, no proof steps or proof dependencies.
- dag/nodes/sec-six-functors-basics/lem-sfb-marked-nodal-boundary-control.json: statement, unsplit; no Mathlib match, no proof steps or proof dependencies.

The five new nodes cover returned Steps 2–4, 5–6, 7–8, 9–11 and 12–13 respectively. The six steps of the parent keep Step 1 and assemble these results. This is a repair of the human-requested oversized-proof return, not an unchanged re-push. There were no retained node files or report in this sandbox, only dispatcher markers; the returned version was recovered from the current repository and preserved as returned-item.json. No repository or launcher files were written and no git commands, compiler, Lake or build tools were run by this worker. The required delivery tool handles rebasing onto current server main.

## Attachments

None. Searches by the exact blueprint tag and the geometric notions in lean/WeilConjectures found no declaration stating the item. The existing Sheaf.AlgebraicGeometry.EquivariantSingleCurveNodalReduction theorem at line 210 ends with sorry at line 305, so is not an attachment. The new statements have no finished project matches. The parent's existing Lean and audit metadata are retained.

## WANTED

WANTED: local literature/de-jong-families-curves-alterations-1997.pdf, Theorem 2.4, Remark 2.5, §§3.2–3.13, Lemmas 5.5 and 5.7, for the item and the five new nodes. The publisher scan https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf was consulted online without downloading a local copy. The field and integrality expansions are agent arguments retained below, not claims of verbatim theorems in that paper. No SGA source is used.

## What was wrong and what changed

The returned proof carried 10713 characters of work in one node. Its statement is not changed. Every argument is retained below, verbatim, with its destination; the new nodes give self-contained interfaces for those arguments and have no proof sketches in their statements. The parent now only supplies the inputs, identifies the resulting maps and applies the interfaces. No statement dispute was needed.

The generic tensor-field assertion has been made explicit: integrality is asserted after any dominant integral base change, but the assertion that the tensor algebra of function fields is itself a field assumes the base-field extension is finite. This is the hypothesis that all alterations in the retained construction satisfy. No arbitrary-base-change generic-smoothness assertion was introduced.

## Mathlib and blueprint searches

Each new id has two different LeanFinder phrasings, one Loogle pattern, one Mathlib grep, and one LeanSearch, all executed by the required msearch.py command. searches.jsonl holds the unmodified receipts, and *.search*.txt holds the complete returned signatures, all read. search_plan.json maps the queries to the intended node ids. None was unavailable. The parent's earlier searches are retained from the returned item, not represented as newly executed here.

The stable-model searches returned covers and Galois categories, not stable pointed reduction. Evaluation searches returned rational maps and a geometric-integrality lemma assuming EVERY fibre is geometrically integral; a nodal stable fibre here may be reducible. The field searches returned purely inseparable transitivity and Galois fixed-field facts, not the tensor invariant equality plus kernel-tower statement. The quasi-splitting searches returned elliptic models and generic finite-action facts; boundary searches returned smooth-locus and nowhere-dense facts without the marked proper-family conclusion. These are useful ingredients, not one-line matches. Follow-up logged greps attempted the candidate declaration names; the pinned Mathlib source did not expose the geometric-integrality and smooth-locus names under those expressions.

Whole-DAG statement and title searches checked stable pointed curves, Hom closure, tensor invariants, fixed fields, quasi-splitting, generic fibres and curve boundaries. blueprint_refs.py searched stable pointed, quasi-split, tensor invariants, nodal, purely inseparable, marked, kernel invariant and stable model across all imported blueprint nodes. The ancestor tool reports null; the new nodes keep that inherited null ancestor and give the exact old-step place and full via chain. same_as is empty: none of the imported nodes states these interfaces. The current blueprint direct-image proof was read; this repair stays below the already chosen alteration route and changes no chapter or unit record.

## Not duplicates

lem-sfb-genus-raising-equivariant-stable-model vs lem-sfb-high-genus-equivariant-cover: the existing result stops at Q/S1; the new result also constructs an equivariant stable pointed model over S2, with generic identification, unique action and H-projectivity.

lem-sfb-genus-raising-equivariant-stable-model vs lem-sfb-stable-pointed-generic-extension: the existing result has neither a target cover nor a group action; the new statement retains the genus-raising diagram and kernel fields.

lem-sfb-genus-raising-equivariant-stable-model vs lem-sfb-stable-pointed-isom-finite: the existing Isom theorem extends a given generic isomorphism; the new construction must produce the model and establish its genuine group action.

lem-sfb-equivariant-stable-model-evaluation vs lem-sfb-high-genus-hom-closure: the existing closure may have nonnormal base R; the new statement includes equivariant normal domination S-prime and integrality plus field descriptions under subsequent dominant base changes.

lem-sfb-equivariant-stable-model-evaluation vs lem-sfb-semilinear-galois-alteration-domination: the existing lemma constructs a normal alteration of the base only; the new statement extends evaluation on the curve and identifies its total function field.

lem-sfb-curve-field-kernel-invariant-tower vs lem-weil-pbc-tensor-field-extension-galois-invariants: the existing statement is a vector-space fixed-point equality; the new result includes tensor fields, purely inseparable intermediate fixed fields and propagation through kernels of composite surjections.

lem-sfb-quasisplit-regular-constant-alteration vs lem-sfb-nodal-finite-quasi-splitting: the existing statement only gives a quasi-split base cover; the new one also regularizes constants, preserves total and base kernel invariants and produces H-projective evaluation alterations.

lem-sfb-quasisplit-regular-constant-alteration vs lem-sfb-normal-alteration-constant-regularization: the existing result concerns the base and constants only; the new result also quasi-splits the curve and handles its evaluation map to C and total invariant field.

lem-sfb-marked-nodal-boundary-control vs lem-trf-relative-marked-nodal-reduction: the existing theorem creates a new curve by alteration, without a prescribed group action or given markings; the new statement constructs only the exceptional closed subset of an already marked curve and proves its persistence.

lem-sfb-marked-nodal-boundary-control vs lem-sfb-equivariant-single-curve-nodal-reduction: the new statement assumes an existing quasi-split marked nodal family and controls an arbitrary generically marked closed subset; it constructs no alteration, group extension or constants.

## Review by Q80

I read the returned item, every one of its original proof-dependency statements, its chapter and unit, the current direct-image blueprint proof, and the new stable-pointed and quasi-split definition nodes. For the source route I consulted the publisher's printed pp.602–609 and 614–615. The stable-model task follows §3 through genus raising and stable extension; evaluation follows Hom closure in §§3.9–3.13; constants and quasi-splitting follow Lemmas 5.5 and 5.7. The boundary task follows Remark 2.5. The field-tower task is the retained agent expansion of the generic invariant calculations. Sources are assigned individually in each node and the entire returned arguments are preserved below.

For parent Step 1 I checked flat preparation gives exactly its smooth geometrically integral generic curve, finite etale marking and finite purely inseparable K0/K. The field-excellence statement applies to k, finite-type/localization permanence applies to its algebras, and finite-type-over-Noetherian gives the required Noetherian schemes. Those are the four cited statements, not facts borrowed from their proofs.

For parent Step 2 I checked the first new interface supplies both groups, both bases, Q, rational generic markings, the three fixed-field equalities, the no-rational-curve property and the actual action on the H-projective stable model. It does not assert an evaluation map prematurely. Flat preparation meets all its input hypotheses; the empty marking is allowed and the high-genus auxiliary cover is retained.

For parent Step 3 I checked the second interface accepts a target that need not be flat or integral. Its geometric fibres are the old Q fibres after field extension, so the first interface supplies precisely its no-rational-curve hypothesis. The generic pointed identification is equivariant. The output includes equivariance of S-prime to R, not merely a map from a non-equivariant domination statement. It gives the integral total scheme and the finite-extension field comparison used next.

For parent Step 4 I checked both new statements cited there: evaluation supplies integrality, tensor fields and the base kernel equality; the field-tower interface supplies the tensor fixed-field equality and propagation along two surjections. Smooth geometric integrality of the generic curve gives the tensor-domain input. All base-field extensions in this application are finite. The initial fixed fields are F0 and K0, which are purely inseparable over F and K. The final radicial change is covered by the identity group surjection case, not by a separability assumption.

For parent Step 5 I checked the fourth new interface assumes the invariant conclusions just obtained and an actual equivariant dominant generically finite map to C. The generic identification followed by the finite auxiliary cover verifies dominance and generic finiteness; the base is a composite of alterations. The interface outputs all constants, the total invariant field, the projectivity and dense-open finiteness of both horizontal maps. It retains the graph argument in its assigned old Step 11 below. It has no boundary-control conclusion, which remains a separate argument.

For parent Step 6 I checked the final interface accepts the closed set c-inverse(E) and only requires generic containment in the markings. The generic identification in the first new statement identifies these markings with the reduced inverse image of the old generic marking, which is the closure supplied by preparation. Set-theoretic containment is sufficient; no scheme factorization is inferred from support containment. The new boundary statement provides D, smoothness away from D and every listed base-change property; the dimension-zero clause applies after the fourth interface gives B=Spec(e).

I tested every new statement on empty markings and E, trivial and nonfaithful finite actions, characteristic zero, and dimension-zero bases. In characteristic zero the purely inseparable assertions become equalities. A reducible nodal special fibre is permitted in evaluation, so an all-fibres-geometrically-integral Mathlib lemma is insufficient. The generic smooth fibre makes the nonsmooth image proper, and the Noetherian hypothesis gives finitely many closed components. Over a point there are no vertical components and the smooth generic fibre is the only fibre, giving empty D. Base change into D preserves nodality and sections but need not have smooth generic fibre or nowhere dense inverse image of D; the interface explicitly has the correct scope. The finite-extension assumption in the tensor-field clause avoids the false assertion that a tensor algebra over an arbitrary transcendental field extension must already be a field.

I checked delivery-errors B–E: each new statement introduces all its objects and definitions, has sources, actual searches and a non-duplicate explanation, and is statement-only; every parent non-elementary assertion is covered by a cited statement with a verbatim quote in citations.json; there is no reliance on the proof of a cited node or an unmentioned lemma. All five new nodes use only definition dependencies, so no cycle is introduced. Each parent step is shorter than 2000 characters. The five extracted arguments have comparable original sizes (2014, 1895, 1554, 2818, 1830 characters); no single new node restates the whole item. The 2818-character block contains three tightly linked finalization arguments and is deliberately left as an unsplit task, not hidden inside the parent's proof. No new node has proof steps.

## Preserved arguments and exact coverage of the returned proof

These paragraphs are the previous proof, preserved without shortening. They are handoff material in the report; the new nodes themselves remain statement-only. Each numbered old step has exactly one destination, except old Step 1 which remains in the parent.

### Returned Step 1 → parent Step 1

Put $K=k(Y)$ and $F=k(C)$. Apply equivariant flat preparation to $(g,H,E)$, obtaining $S,P,f,M,a,b_0$ with $K_0=k(S)/K$ finite purely inseparable. Put $F_0=k(P)=F\otimes_K K_0$. The generic curve of $P/S$ is smooth geometrically integral and its reduced generic marking is finite etale. The $H$-action is retained. Fields are excellent, finite-type algebras and their localizations are excellent, and finite-type schemes over a field are Noetherian; hence all bases constructed below are excellent Noetherian. This step prepares the generic curve and the target, and makes no stable-modification claim.

Cited statements: lem-sfb-equivariant-flat-curve-preparation, lem-exc-fields-excellent, lem-exc-finite-type-localization-excellent, lem-weil-pbc-finite-type-over-noetherian.

Source: literature/de-jong-families-curves-alterations-1997.pdf, §§2.7--2.10, pp.603--605; excellence bookkeeping from the cited generic algebra statements.

### Returned Step 2 → lem-sfb-genus-raising-equivariant-stable-model

Apply the auxiliary high-genus cover to $P/S$, its marking $M$ and $H$. Denote its output by $Q/S_1$, $H_1\twoheadrightarrow H$, and $K_1=k(S_1)$, $F_1=k(Q)$. Its generic fibre is smooth geometrically integral of genus at least two. Its generic inverse image of $M$ is a finite set of distinct rational points $p_i$, invariant as a set under $H_1$. Every geometric fibre of $Q/S_1$ contains no nonconstant image of $\mathbf P^1$. If $A_1=\ker(H_1\to H)$, the cover supplies $F_1^{A_1}=F_0$ and $K_1^{A_1}=K_0$. The finite separable auxiliary covering is retained: the required conclusion allows the genus to increase and does not prescribe $k(V)=F\otimes_K k(B)$.

Cited statements: lem-sfb-high-genus-equivariant-cover.

Source: literature/de-jong-families-curves-alterations-1997.pdf, §§3.2--3.6, pp.605--608, including the fibre-product group and invariant Kummer cover in §3.5.

### Returned Step 3 → lem-sfb-genus-raising-equivariant-stable-model

Apply stable pointed extension to the smooth pointed generic curve $(Q_\eta,p_i)$ over $S_1$. It gives an integral alteration $T\to S_1$, with finite separable generic extension, and a stable pointed curve over $T$. Apply semilinear Galois domination to this alteration and $H_1$. Obtain a normal projective $S_2$, a surjection $H_2\twoheadrightarrow H_1$, and a map $S_2\to T$. Pull the stable pointed curve to $S_2$ and call it $(W,s_i)$. Its generic pointed fibre is $Q_\eta\times_{K_1}K_2$, where $K_2=k(S_2)$. For $N_2=\ker(H_2\to H_1)$, domination gives $K_2^{N_2}=K_1$ (the separable case). No morphism from $W$ to $P$ has yet been asserted.

Cited statements: lem-sfb-stable-pointed-generic-extension, lem-sfb-semilinear-galois-alteration-domination.

Source: literature/de-jong-families-curves-alterations-1997.pdf, Lemma 3.7 and §3.8, p.608: stable pointed extension and normal equivariant domination.

### Returned Step 4 → lem-sfb-genus-raising-equivariant-stable-model

For each $h\in H_2$, the given action on the generic curve identifies the unordered pointed generic fibres of $h^*W$ and $W$. Finite-Isom rigidity extends it uniquely to an isomorphism on the normal integral base $S_2$. The composite of the extensions for $h,h'$ and the extension for $hh'$ have identical generic restrictions, so uniqueness proves the group law; the identity extends to the identity. This gives a genuine action preserving the union of the sections, allowing permutations. The curve $W/S_2$ is projective in the projective-bundle sense. As $S_2$ is projective over $k$, it has an absolute ample invertible sheaf. Projective-bundle to H-projective conversion makes $W/S_2$ H-projective.

Cited statements: lem-sfb-stable-pointed-isom-finite, lem-weil-pbc-projective-ample-invertible, lem-trf-projective-bundle-to-h-projective.

Source: literature/de-jong-families-curves-alterations-1997.pdf, §3.8, pp.608--609; the argument concerns stable pointed curves, not stable modifications of a given pair.

### Returned Step 5 → lem-sfb-equivariant-stable-model-evaluation

Apply the Hom-closure theorem to $W/S_2$, the H-projective target $Q\times_{S_1}S_2$, and their generic identification. The no-rational-curve condition on this target holds by the high-genus cover, since its geometric fibres are geometric fibres of $Q/S_1$ after field extension. Obtain an integral projective birational $R\to S_2$, with evaluation $W_R\to Q_R$. The closure and evaluation are $H_2$-equivariant by naturality. Apply semilinear Galois domination to $R\to S_2$, obtaining normal projective $S_3$, $H_3\twoheadrightarrow H_2$, and $S_3\to R$. This last map is equivariant: its translates agree at the generic point because $R\to S_2$ is birational; the closed equalizer and reducedness of $S_3$ make them equal. Pull back evaluation and the sections. We have an $H_3$-equivariant map $W_3\to Q\to P\to C$ over $S_3\to S_1\to S\to Y$, and a stable pointed curve $W_3/S_3$.

Cited statements: lem-sfb-high-genus-hom-closure, lem-sfb-high-genus-equivariant-cover, lem-pc-projective-base-change, lem-sfb-semilinear-galois-alteration-domination, lem-sfb-stable-pointed-generic-extension.

Source: literature/de-jong-families-curves-alterations-1997.pdf, §§3.9--3.12, Claim 3.10 and Lemma 3.13, p.609; extend the generic map using the proper closure in Hom.

### Returned Step 6 → lem-sfb-equivariant-stable-model-evaluation

For this and every subsequent dominant integral base change $T'\to S_3$, the pulled-back curve is integral. Indeed, over an affine domain $A$ in $T'$, on every affine chart $\operatorname{Spec}B$ of the flat curve, multiplication by $a\in A\setminus\{0\}$ is injective by flat-invertible-sections-torsion-freeness applied to $\mathcal O$. Hence $B\hookrightarrow B\otimes_A\operatorname{Frac}(A)$. A nonempty chart has nonempty generic fibre and this generic ring is a domain, since the generic curve is geometrically integral. Thus every chart is a domain. The generic fibre is irreducible and meets every nonempty open by the same injectivity, so the entire curve is irreducible, and is reduced chartwise. Its function field after base extension $L'/L$ is the function field $D$ of the preceding generic curve tensored with $L'$; this is a domain and is finite dimensional over $D$, hence a field. In particular $k(W_3)=F_1\otimes_{K_1}k(S_3)$. The same argument works for purely inseparable base extensions.

Cited statements: lem-sc-flat-invertible-sections-torsion-free, lem-weil-pbc-finite-dimensional-domain-is-field, lem-trf-semistable-marked-base-change.

Source: literature/de-jong-families-curves-alterations-1997.pdf, Generic-field preservation in §3.11, p.609, expanded using flatness; this replaces every former normal-base-change appeal to stable modification.

### Returned Step 7 → lem-sfb-curve-field-kernel-invariant-tower

Record how the invariant fields behave at each of our base extensions. Let $J'\twoheadrightarrow J$ have kernel $N$, let $L'/L$ be the corresponding finite extension of base fields, and suppose $(L')^N=M$ is purely inseparable over $L$. The group $N$ acts trivially on the preceding generic curve field $D$ and only on $L'$ in $D'=D\otimes_L L'$. The field $D_M=D\otimes_L M$ is a field by the domain and finite-dimension argument of Step 6. Tensor invariants over $M$, with vector space $D_M$, give $(D')^N=D_M$. Every element of $D_M$ has some common characteristic power in $D$: write it as a finite sum of tensors and take a power putting all coefficients from $M$ into $L$. In characteristic zero $M=L$ and this is equality. Therefore $(D')^N/D$ is purely inseparable.

Cited statements: lem-weil-pbc-tensor-field-extension-galois-invariants, lem-weil-pbc-finite-dimensional-domain-is-field.

Source: literature/de-jong-families-curves-alterations-1997.pdf, §§3.2, 3.5 and 3.11, pp.605,607--609; explicit kernel invariant-field calculation under base extension.

### Returned Step 8 → lem-sfb-curve-field-kernel-invariant-tower

If $A=\ker(J\to H)$ and $A'=\ker(J'\to H)$, then $A'\to A$ is surjective. For $z\in(D')^{A'}$, Step 7 puts some characteristic power $z^{p^r}$ in $D$. Since all lifts of $A$ fix $z$, that power lies in $D^A$. If $D^A/F$ is purely inseparable, a further power lies in $F$. The identical power argument for the base fields proves the base invariant assertion. In characteristic zero both powers are identities. Start with $F_1^{A_1}=F_0$ and $K_1^{A_1}=K_0$ from Step 2; $F_0/F$ and $K_0/K$ are purely inseparable by Step 1. The domination steps give $(L')^N=L$ in the separable case. Thus for $A_3=\ker(H_3\to H)$ we have $k(W_3)^{A_3}/F$ and $k(S_3)^{A_3}/K$ purely inseparable. The same reasoning will apply to the next finite base cover and to the final radicial constant change.

Cited statements: .

Source: literature/de-jong-families-curves-alterations-1997.pdf, Composition bookkeeping as in Remarks 2.3(iii) and §2.6, pp.602--603; the preceding tensor calculation is Step 7.

### Returned Step 9 → lem-sfb-quasisplit-regular-constant-alteration

Apply finite quasi-splitting to $W_3/S_3$ and $H_3$. Its hypotheses hold: the family is H-projective, flat and finitely presented, with nonempty connected reduced nodal geometric fibres and smooth geometrically integral generic fibre. Obtain normal projective $S_4\to S_3$ finite surjective generically etale and $H_4\twoheadrightarrow H_3$. Pull the stable curve and its sections to $S_4$. The family is quasi-split; the markings remain disjoint and smooth. Integrality and the field description follow from Step 6. The base kernel invariant field is purely inseparable by finite quasi-splitting; Steps 7--8 therefore retain both invariant-field conclusions. The group action on the pulled-back markings permutes the sections. There is no finite-etale-marking cover $T_1$ in this construction: the sections were extended from the rational points $p_i$ in Step 3.

Cited statements: lem-sfb-nodal-finite-quasi-splitting, lem-trf-semistable-marked-base-change, lem-sfb-stable-pointed-generic-extension.

Source: literature/de-jong-families-curves-alterations-1997.pdf, Lemma 5.7, p.615, applied to an already semistable curve; disjoint sections come from Lemma 3.7, not a possibly disconnected splitting cover.

### Returned Step 10 → lem-sfb-quasisplit-regular-constant-alteration

Apply constant regularization to $S_4\to Y$, $H_4\to H$ and the base invariant conclusion just proved. Obtain a finite extension $e/k$, normal projective geometrically integral $B/e$, and a finite radicial surjection $B\to S_4$, with the same group $G=H_4$. Write $\alpha:G\to H$, $A=\ker\alpha$. The constant lemma gives $e^A/k$ and $k(B)^A/K$ purely inseparable. Pull the curve and sections to $B$, naming it $v:V\to B$. Semistable marked base change retains the fibre and section assertions; quasi-splitting persists by its base-change clause. The smooth geometrically integral generic fibre persists since $B\to S_4$ is dominant. Step 6 proves $V$ integral. In Steps 7--8 take $J'=J=G$, $N=1$, and the purely inseparable field extension $k(B)/k(S_4)$; the same calculation proves $k(V)^A/F$ purely inseparable.

Cited statements: lem-sfb-normal-alteration-constant-regularization, lem-trf-semistable-marked-base-change, lem-sfb-nodal-finite-quasi-splitting.

Source: literature/de-jong-families-curves-alterations-1997.pdf, Lemma 5.5, p.614, field-base constants, and Lemma 5.7; generic fields and kernels tracked by Steps 6--8.

### Returned Step 11 → lem-sfb-quasisplit-regular-constant-alteration

Let $c:V\to C$ and $b:B\to Y$ be the composites already constructed. The fibre-product diagrams give $gc=bv$, and all maps are equivariant via $\alpha$. The map $v$ is H-projective by base change. Constant regularization explicitly supplies H-projectivity of $b$. Since $Y$ is H-projective over $k$, composition makes $B$ H-projective over $k$. The graph of $B\to S$ is closed because $S/k$ is separated; combining it with a projective embedding of $B/k$ proves $B\to S$ H-projective. Its base change $P\times_S B\to P$ is H-projective. Likewise an embedding $V\hookrightarrow\mathbf P^n_B$ and the map $V\to P\times_S B$ give a closed graph embedding into $\mathbf P^n_B\times_B(P\times_S B)$, since the target is separated over $B$. Thus evaluation is H-projective, and composition with $P\times_S B\to P\to C$ proves $c$ H-projective. Projectivity implies properness. Both $c,b$ are dominant with finite function-field extensions: the auxiliary cover and all subsequent generic changes are finite. Proper closed image proves surjectivity. The generic-finite-neighbourhood lemma gives finiteness over dense opens, so $c,b$ are alterations.

Cited statements: lem-pc-projective-base-change, lem-trf-h-projective-composition, lem-pc-projective-proper, lem-weil-pbc-proper-closed-image, lem-weil-pbc-generic-finite-morphism-open-neighborhood, lem-sfb-normal-alteration-constant-regularization.

Source: literature/de-jong-families-curves-alterations-1997.pdf, §3.11, p.609, with explicit H-projective graph argument and dense-open finiteness.

### Returned Step 12 → lem-sfb-marked-nodal-boundary-control

Let $J_B=\bigcup_i s_i(B)$. The generic identification in stable pointed extension and the generic evaluation show that the reduced inverse image of $E$ on the generic fibre of $V/B$ is contained in these marked points. The closed set $c^{-1}E$ has finitely many irreducible components, since $V$ is Noetherian. A component dominating $B$ lies in $J_B$: its generic point does, and $J_B$ is closed (a finite union of sections of a separated morphism). Every other component has proper closed image by properness of $v$. The nonsmooth locus is closed by the nodal Fitting-locus lemma, and has proper closed image because the generic curve is smooth. Let $D$ be the union of these finitely many images and all their $G$-translates. Each image misses the generic point of the integral base, so $D$ is invariant, closed and nowhere dense. It has $c^{-1}E\subseteq v^{-1}D\cup J_B$, and $v$ is smooth over $B\setminus D$.

Cited statements: lem-weil-pbc-noetherian-finitely-many-components, lem-weil-pbc-proper-closed-image, lem-trf-nodal-family-fitting-singular, lem-sfb-stable-pointed-generic-extension, lem-sfb-high-genus-equivariant-cover.

Source: literature/de-jong-families-curves-alterations-1997.pdf, Remark 2.5, p.603; the closed boundary and nonsmooth images supply the exceptional set.

### Returned Step 13 → lem-sfb-marked-nodal-boundary-control

For arbitrary $B'\to B$, projectivity is preserved, and semistable marked base change preserves flatness, finite presentation, pure relative dimension one, nodal geometric fibres and smooth disjoint markings. Nonemptiness, geometric connectedness and reducedness are properties of the geometric fibres and persist on extending their algebraically closed fields. Quasi-splitting persists by the quasi-splitting lemma: rational nodes and their two rational branches remain rational after residue-field extension. The equations $v s_i=1_B$ pull back to section equations. This persistence does not require the inverse image of $D$ to be nowhere dense or the new generic fibre to lie outside it. If $\dim Y=0$, the constant regularization clause gives $B=\operatorname{Spec}e$. Its sole fibre is the smooth generic fibre, and all points of $c^{-1}E$ are marked; hence the construction of Step 12 gives $D=\varnothing$.

Cited statements: lem-pc-projective-base-change, lem-trf-semistable-marked-base-change, lem-sfb-nodal-finite-quasi-splitting, lem-sfb-normal-alteration-constant-regularization.

Source: literature/de-jong-families-curves-alterations-1997.pdf, Remark 2.5 and §§3.3, 5.5--5.7, pp.603,605,614--615.

## Unfinished work

The five new statements are intentionally unsplit parallel tasks, as the return requires. There is no new Lean work. Mechanical validation is recorded below; delivery follows the final passing dry run.

## Validation

The server review_split check passed. The required deliver.py --no-push exited successfully with preflight passed at 6806d228fee, including the server DAG and split checks. Local read-only comparison confirms the current repository still matches the recovered returned baseline, the item statement is byte-for-byte unchanged, the six parent proof steps total 2698 characters (maximum 602), all five new nodes have status unsplit and empty proof/proof_deps, and every cited definition exists. citations.json contains all 11 required step/node pairs. The final dry run after adding this validation paragraph is followed by the authorized delivery command. No compile was run.
