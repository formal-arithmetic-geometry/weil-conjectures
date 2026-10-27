# Q39 repair report: equivariant marked plurinodal field alteration

The returned item has been re-split into four independent statement-only work items. The original statement, source, prior Mathlib searches, Lean metadata, prior review records and blueprint ancestry are retained. The parent now has four assembly steps, with 2200 characters of proof text (below 3000). No Lean was written or compiled. The sandbox initially contained no files; the live returned node was copied before editing. There was no earlier sandbox report or search log to recover. The live item contains exactly the thirteen returned steps; its current proof was used as the returned head. No repository or launcher files were written and no git command was run in the shared repository.

## What is delivered

- `lem-sfb-flat-curve-pullback-function-field`: ordinary fibre-product reducedness, integrality, generic density and function-field tensor identification. This is the work of old steps 6--7 (about 2300 characters), with the relevant generic-fibre part of step 5.
- `lem-sfb-marked-nodal-tower-cartesian-extension`: extension of already supplied data, diagonal action, section and boundary checks, smoothness/quasi-splitness, projectivity/surjectivity and finite function-field extension. This is old steps 5, 8 and 9 (about 2100 characters). It assumes the integrality and finite-degree result, rather than concealing that argument.
- `lem-sfb-tensor-kernel-inseparable-invariants`: diagonal tensor invariants and the two-power argument through the two kernels, including the constant-field specialization. This is old step 10 (about 1000 characters). It does not assume the desired final fixed-field assertion.
- `lem-sfb-generic-invariant-field-orbit-open`: finite-near-the-generic-point, finite affine quotient, invariant fractions, common-power localization and geometric orbit fibres. This is old steps 11--13 (about 2500 characters). It assumes an already supplied morphism and a purely inseparable fixed function field; it constructs no alteration or tower.

All four are `status: unsplit`, with empty proof, empty proof dependencies, null proof origin, sources, searched statement definitions and genuine logged Mathlib searches. There are zero new Mathlib leaves. Old steps 1--4 remain the parent's dimension induction, pencil and one-curve reduction. Every old argument is mapped to an owner below, and the complete old text and citations are preserved verbatim later in this report, so the next workers lose no argument.

## Sources and searches

Read the local ILO PDF, Exposé X Lemma 2.2 and its proof, printed pp.149--150 (PDF pages 155--156). Its initial plurinodal input is distinct from the later regular/SNC modifications. Read de Jong, *Families of curves and alterations* (1997), Remarks 2.3(iii)--(iv), Situation 5.8 and Theorem 5.9, printed pp.602, 615--617, at https://www.numdam.org/item/10.5802/aif.1575.pdf. The last fibre-product paragraph is the source of the four obligations, not a replacement black box for them.

WANTED: literature/de-jong-families-curves-alterations-1997.pdf, Remarks 2.3, Situation 5.8 and Theorem 5.9 proof, for the three extracted fibre-product/tower/invariants nodes and the parent; read online, absent locally.
WANTED: Vidal 2004b Proposition 4.4.3, for the original plurinodal input quoted by ILO X Lemma 2.2; still absent locally. No nonexistent primary text is claimed as read. The parent assembly is marked agent-origin.

For the pullback node, read Mathlib `Geometrically/Reduced.lean:109--131`, and `Geometrically/Integral.lean:91--114`. Loogle returns exactly the reduced-pullback instances, not generic-fibre integrality plus the tensor function field. The integral-pullback instances require all fibres geometrically integral, stronger than our hypothesis; reducible nodal special fibres are allowed here. The other semantic phrasing returned flat localization and going-down lemmas, also not the full result.

For the tower-extension node, read de Jong Situation 5.8 and the final paragraph of 5.9. Semantic hits `Scheme.Pullback.gluing` and `AffineSpace.isPullback_map` are constructions for other statements, not marked nodal tower extension. Initial Loogle projectivity names were unknown; these are recorded as unavailable queries, never as successful evidence of absence. The alternative Flat/pullback query reported the Loogle server under load. Successful LeanFinder searches and Mathlib grep were inspected.

For the kernel-invariant node, read de Jong Remarks 2.3 and Theorem 5.9(a); read Mathlib `FieldTheory/PurelyInseparable/Basic.lean:240--270` and the project theorem `TensorProduct.injective_and_range_eq_invariants` in `WeilConjectures/FieldTheory/TensorFieldExtensionGaloisInvariants.lean:50`. The latter is the already existing tensor-invariants node and remains available as the next worker's ingredient. Neither it nor `IsPurelyInseparable.trans` gives the new statement in one specialization: one must identify Q-fixed tensors and then take N/Q invariants. No proof-bearing leaf was incorrectly created.

For the orbit-open node, read local `groupoids.tex`, Tags 03JE (`lemma-find-invariant-affine`), 03BJ (`lemma-integral-over-invariants`) and 03BL (`lemma-points`), and `morphisms.tex`, Tag 01S4 (`lemma-universally-injective`). In the constant finite groupoid the source and target maps are finite locally free; the entire inverse image of the affine base is affine and invariant. The existing quotient node already includes its finiteness over a finite affine base. Mathlib UniversallyInjective only gives the criterion and stability; Galois-category transitivity or arithmetic Frobenius lemmas do not provide the generic spreading statement.

For every new node, the own statement was searched by LeanFinder with two phrasings, Loogle, Mathlib grep and LeanSearch using only msearch.py. LeanSearch returned an HTTP rate-limit error on all four queries, recorded unavailable. The grep on `AlgebraicGeometry/Group` was discovered to be an unsuitable path and is not used in any node's evidence; an actual search of all AlgebraicGeometry was run and recorded for the orbit node. Queries and answers were read, and exact query text is retained in each node and searches.jsonl. No query was invented. Whole-DAG statement and keyword searches and whole-blueprint searches (`plurinodal`, `marked`, `geometrically reduced`, `generic fibre`, `purely inseparable`, `tensor invariants`, `flat generic`, `geometric orbit`, `quasi-split`, `orbit`) found no existing node stating any of these four combined results. Broad tensor matches concern other tensor constructions. The ancestor command still returns None; the original null ancestor and via chain are preserved, with this item prepended in the new nodes.

The attachment check searched the item tag and plurinodal terms in live WeilConjectures. The matching local Sheaf module, `EquivariantMarkedPlurinodalFieldAlteration.lean`, declares `AlgebraicGeometry.exists_equivariant_marked_plurinodal_field_alteration` at line 204, with `sorry` at line 278. It is not a finished attachment. Searches for the new notions found the existing tensor invariant theorem as an ingredient, not a declaration for any complete new node.

## Review by Q39

I checked every extraction against the actual old proof and its input statements, not only its dependency names. The return asks to spread substantial arguments, so the four new nodes isolate geometric integrality, cartesian tower geometry, field theory and generic finite quotient spreading. None asserts the existence of the whole alteration, and none is the one-clause relabelling that would reduce the parent to applying the original theorem under a new name. No new node cites the parent; there is no inductive cycle. The lower-dimensional induction stays in the parent and is explicitly strengthened to allow nonfaithful groups, H-projectivity and the generic fixed-field condition.

Parent step 1 uses the zero-dimensional properness statement for finiteness/affineness, the geometric integrality definition to rule out a nontrivial finite constant extension, and the one-curve reduction's zero-dimensional-base clause for dimension one. The reduction statement explicitly gives B=Spec e, D empty, both inseparable fixed fields, markings and quasi-splitness; those are not taken from its proof. The empty boundary at dimension zero follows since a point has no nonempty nowhere dense closed subset.

Parent step 2 uses the pencil statement for birational X' and dim Y=d-1, the single-curve statement for normal proper geometrically integral B over finite e, and the dimension lemma for equality of dimensions under the proper finite-function-field map B->Y. I added an explicit citation to finite-type-over-Noetherian for its locally Noetherian hypothesis. The fields k and e have Noetherian spectra. The inverse image of Z avoids the generic point of X', so is nowhere dense. Induction is on the strictly smaller dimension d-1, with its full data retained; G need not act faithfully on B. Finite e/k means the new fibre-product lemma may regard P and V as finite-type e-schemes. All field actions and maps are compatible.

Parent step 3 first uses the new flat-curve pullback statement: v is flat, its geometric fibres are reduced, its generic fibre geometrically integral, and h is dominant with finite function field extension by induction. This supplies the integrality and finite-degree assumptions of the separate tower-extension lemma. That second statement takes the already constructed v,h,c,pi, the lower tower and its boundary: h^{-1}D is in Z_{d-1}, and c^{-1}pi^{-1}Z is in v^{-1}D plus the original sections, exactly as the one-curve reduction states. The conclusion supplies every claimed marking, base-change, equivariance, boundary, smoothness and quasi-split property and the alteration composite. I made explicit that h is an e-morphism and c,pi are k-morphisms so the fibre product has the required field structure. Ordinary fibre product, rather than its reduction/normalization, is essential and is stated explicitly.

Parent step 4 applies the new invariant lemma to N=ker(alpha beta), Q=ker beta. Surjectivity of beta gives N/Q=A=ker alpha; Q fixes L=k(V). The Q-fixed field M^Q/K is exactly the induction input, and L^A/k(X') is exactly the one-curve input. Equality k(X')=k(X) comes from the pencil statement used in step 2. The constant-field clause has the same kernels and the two actual inseparable hypotheses F^Q/e and e^A/k. Finally the orbit-open statement applies to a map already shown H-projective/surjective and finite on function fields, with N fixing X and k; the generic invariant assertion was just proved, not assumed circularly. That statement explicitly gives a finite surjective dense-open restriction and its nonempty geometric orbit fibres. Every parent uses entry has a verbatim quotation in citations.json; the quotations are complete statements to preserve all hypotheses.

For the four new statements I checked small cases and necessary hypotheses. The integral pullback allows a reducible nodal special fibre (so does not falsely assume all fibres integral), and handles h=identity and a purely inseparable finite field extension. Flatness is required of v, never of h. In characteristic p the original K-linear retraction of Omega/K gives descent of reducedness before the pullback lemma is applied; generic density is a different argument retained below. The gluing statement allows r=0, no sections, empty marking/boundary and nonfaithful groups; it requires W integral and finite over V on function fields, supplied separately, and claims no smooth total space. The invariant statement allows Q=1, Q=N, trivial actions and characteristic zero; in characteristic zero both inseparability assumptions become equalities. The constant-field assertion is the specialization L=K=e,M=F,R=k, not a second unexplained theorem. The generic orbit statement handles the trivial group and purely inseparable morphisms, requires no normality of W, and shrinks after choosing the quotient's finite module generators. Uniqueness of p-power roots holds in every field, so the all-field-valued criterion actually gives radiciality.

I also checked B--E point by point: complete objects/hypotheses and definition citations, statement-only new nodes, single TeX escaping, truthful search results, populated blueprint fields, no unsupported citation or off-route substitution, no added target hypotheses and no fixed-leg condition. Parent proof steps are all below 2000 characters; the new nodes have no steps. The original H-projective/permanence/function-field/quotient statements are included in the verbatim handoff below, so the next workers can cite them instead of silently appealing to generic facts. Existing generic tool declarations retained in split_report cover the zero-dimensional, dimension and Noetherian tools outside this unit; these do not change the ILO/de Jong route.

## Statement disputes retained

The previous corrected quasi-split statement is kept byte-for-byte. The old stronger fixed-marked-leg assertion was already disputed and repaired in the returned main node: over an algebraically closed field of characteristic different from 2, the involution x->-x on P1 swaps the boundary points +1 and -1. A plurinodal curve permits permutation of markings, as de Jong 5.8 states. This repair makes no further statement change, no smooth-total-space assertion and no SGA citation.

## Not duplicates

lem-sfb-flat-curve-pullback-function-field vs lem-sfb-flat-geometrically-reduced-pullback: The existing node supplies only reducedness; the new one also proves generic density, integrality and the finite tensor function-field identification.

lem-sfb-marked-nodal-tower-cartesian-extension vs lem-sfb-equivariant-single-curve-nodal-reduction: The existing node constructs a single reduced curve after alteration. The new one glues supplied data to an existing lower tower and verifies the composite and boundary; it constructs no nodal reduction.

lem-sfb-tensor-kernel-inseparable-invariants vs lem-weil-pbc-tensor-field-extension-galois-invariants: The existing node identifies fixed vectors when the scalar fixed field equals the base. The new one handles two group kernels and inseparable fixed fields in a tensor compositum, with a constant-field specialization.

lem-sfb-generic-invariant-field-orbit-open vs lem-sfb-finite-quotient-generic-fields: The existing node identifies generic fixed fields of normal Noetherian finite quotients already given. The new one starts with a generically finite projective map, does not assume normality, and produces the open with radicial intermediate quotient and orbit fibres.

lem-sfb-generic-invariant-field-orbit-open vs lem-weil-pbc-spread-purely-inseparable-factors: The existing node starts with a supplied finite algebra over a finite etale domain. It supplies the inseparable factor only; the new one must find a finite locus, form the invariant quotient and identify its generic field and geometric orbit fibres.

lem-sfb-generic-invariant-field-orbit-open vs lem-sfb-admissible-finite-type-field-quotient: The existing node supplies quotient existence and orbit fibres but no radicial open of the map to X from a purely inseparable invariant generic field.

lem-sfb-generic-invariant-field-orbit-open vs def-weil-radicial-morphism: Shared tag supplies a quotient, groupoid, or radicial ingredient; this existing statement (Radicial and universally injective morphisms of schemes) does not assert the new combination of a projective generically finite map, inseparable invariant function field and a dense open with single geometric N-orbits.

lem-sfb-generic-invariant-field-orbit-open vs def-a1-scheme-groupoid-laws: Shared tag supplies a quotient, groupoid, or radicial ingredient; this existing statement (Groupoid laws for schemes) does not assert the new combination of a projective generically finite map, inseparable invariant function field and a dense open with single geometric N-orbits.

lem-sfb-generic-invariant-field-orbit-open vs lem-a1-affine-groupoid-integral-invariants: Shared tag supplies a quotient, groupoid, or radicial ingredient; this existing statement (Integrality over affine groupoid invariants) does not assert the new combination of a projective generically finite map, inseparable invariant function field and a dense open with single geometric N-orbits.

lem-sfb-generic-invariant-field-orbit-open vs lem-a1-affine-groupoid-orbit-fibres: Shared tag supplies a quotient, groupoid, or radicial ingredient; this existing statement (Fibres of the affine groupoid invariant spectrum are orbits) does not assert the new combination of a projective generically finite map, inseparable invariant function field and a dense open with single geometric N-orbits.

lem-sfb-generic-invariant-field-orbit-open vs lem-a1-integral-residue-extension-algebraic: Shared tag supplies a quotient, groupoid, or radicial ingredient; this existing statement (Integral ring maps induce algebraic residue-field extensions) does not assert the new combination of a projective generically finite map, inseparable invariant function field and a dense open with single geometric N-orbits.

lem-sfb-generic-invariant-field-orbit-open vs lem-pd-finite-free-norm-prime-criterion: Shared tag supplies a quotient, groupoid, or radicial ingredient; this existing statement (Finite free algebra norm and primes over a prime) does not assert the new combination of a projective generically finite map, inseparable invariant function field and a dense open with single geometric N-orbits.

lem-sfb-generic-invariant-field-orbit-open vs lem-pd-finite-locally-free-norm-charts: Shared tag supplies a quotient, groupoid, or radicial ingredient; this existing statement (Norm sections on local finite free affine charts) does not assert the new combination of a projective generically finite map, inseparable invariant function field and a dense open with single geometric N-orbits.

lem-sfb-generic-invariant-field-orbit-open vs lem-pd-invariant-affine-neighbourhoods: Shared tag supplies a quotient, groupoid, or radicial ingredient; this existing statement (Finite locally free descent admits invariant affine neighbourhoods) does not assert the new combination of a projective generically finite map, inseparable invariant function field and a dense open with single geometric N-orbits.

lem-sfb-generic-invariant-field-orbit-open vs lem-pd-descent-orbit-saturated: Shared tag supplies a quotient, groupoid, or radicial ingredient; this existing statement (An orbit of a cartesian descent groupoid is saturated) does not assert the new combination of a projective generically finite map, inseparable invariant function field and a dense open with single geometric N-orbits.

lem-sfb-generic-invariant-field-orbit-open vs lem-pd-descent-norm-locus-affine: Shared tag supplies a quotient, groupoid, or radicial ingredient; this existing statement (Affineness of the norm nonvanishing locus) does not assert the new combination of a projective generically finite map, inseparable invariant function field and a dense open with single geometric N-orbits.

lem-sfb-generic-invariant-field-orbit-open vs lem-pd-descent-norm-affine-shrinking: Shared tag supplies a quotient, groupoid, or radicial ingredient; this existing statement (Invariant affine shrinking around a finite saturated set) does not assert the new combination of a projective generically finite map, inseparable invariant function field and a dense open with single geometric N-orbits.

lem-sfb-generic-invariant-field-orbit-open vs lem-pc-spec-pure-insep-integral-radicial-surjective: Shared tag supplies a quotient, groupoid, or radicial ingredient; this existing statement (Spec of a purely inseparable extension is integral, universally injective and surjective) does not assert the new combination of a projective generically finite map, inseparable invariant function field and a dense open with single geometric N-orbits.

lem-sfb-generic-invariant-field-orbit-open vs thm-pd-effective-descent: Shared tag supplies a quotient, groupoid, or radicial ingredient; this existing statement (Effective descent for quasi-projective schemes) does not assert the new combination of a projective generically finite map, inseparable invariant function field and a dense open with single geometric N-orbits.

lem-sfb-generic-invariant-field-orbit-open vs lem-per-admissible-quotient-affine-integral-charts: Shared tag supplies a quotient, groupoid, or radicial ingredient; this existing statement (Invariant affine charts of an admissible finite-group scheme quotient) does not assert the new combination of a projective generically finite map, inseparable invariant function field and a dense open with single geometric N-orbits.

lem-sfb-generic-invariant-field-orbit-open vs lem-weil-pbc-descend-universally-injective-qcqs: Shared tag supplies a quotient, groupoid, or radicial ingredient; this existing statement (Universal injectivity descends for finitely presented qcqs models) does not assert the new combination of a projective generically finite map, inseparable invariant function field and a dense open with single geometric N-orbits.

lem-sfb-generic-invariant-field-orbit-open vs lem-weil-pbc-finite-radicial-model-descent: Shared tag supplies a quotient, groupoid, or radicial ingredient; this existing statement (A finite radicial surjection over a limit has a finite-stage model) does not assert the new combination of a projective generically finite map, inseparable invariant function field and a dense open with single geometric N-orbits.

## Complete retained arguments and handoff

The following thirteen steps are the returned proof verbatim, not newly claimed proof steps in the unsplit nodes. Suggested proof ingredients remain their original uses. New workers have each complete argument here; no reduction of proof detail has been hidden in a new statement.

### Old step 1: parent assembly step 1 (strong induction and zero-dimensional case)

Use strong induction on $d$, proving also the following strengthened form: the input finite group may act nonfaithfully; the map to $X$ is H-projective; and, for $N=\ker(J\to H)$, the finite extension of function fields satisfies $k(T_d)^N/k(X)$ purely inseparable. All schemes in the tower are finite type over their constant field. The dense-open orbit assertion will be deduced uniformly in the final steps. For $d=0$, the zero-dimensional properness lemma makes $X$ finite over $k$. Its coordinate ring is a finite field extension $L/k$. Geometric integrality forces $L=k$: a nontrivial separable part splits after algebraic closure, and a nontrivial purely inseparable part creates nilpotents. Take $F=k$, $J=H$, $a=\mathrm{id}$ and the length-zero tower. Its boundary is empty, since a nowhere dense closed subset of a point is empty. All strengthened claims are immediate.

Original uses: lem-pc-dim-zero-finite-over-field, def-pc-geometrically-irreducible.

Original source: literature/de-jong-families-curves-alterations-1997.pdf, Theorem 5.9 proof, induction; zero-dimensional field case added explicitly.

### Old step 2: parent assembly step 1 (one-curve base case)

For $d=1$, apply the one-curve reduction node with $C=X$, $Y=\operatorname{Spec}k$ and $E=Z$. Its zero-dimensional clause gives $B=\operatorname{Spec}e$ and $D=\varnothing$. Set $F=e$, $J=G$, $T_1=V$ and $a=c$. The single marked nodal curve is smooth over $B$ because $D$ is empty, and its sections contain $a^{-1}Z$. The reduction node gives H-projectivity, the constant-field assertion $e^{\ker\alpha}/k$, and the strengthened function-field assertion $k(V)^{\ker\alpha}/k(X)$. Thus only the uniform dense-open verification remains for this case. Henceforth assume $d\geq2$.

Original uses: lem-sfb-equivariant-single-curve-nodal-reduction.

Original source: literature/de-jong-families-curves-alterations-1997.pdf, Theorem 5.9 proof, dimension-one case via Theorem 2.4 and Lemma 5.7.

### Old step 3: parent assembly step 2 (pencil, dimension and one-curve data)

Apply the equivariant curve-pencil node to obtain $\pi:X'\to X$ and $g:X'\to Y$. The inverse image $E=\pi^{-1}Z$ is invariant and nowhere dense: $\pi$ is an isomorphism over a dense open and the generic point maps outside $Z$. Apply the one-curve reduction to $g,E$, obtaining $e,G,\alpha,B,V,v,c,b,D$ and sections $s_j$. Here $Y$ has dimension $d-1$, $B$ is normal proper geometrically integral over $e$, and $\dim_e B=d-1$: the alteration $B\to Y$ is proper with finite function-field extension, so dimensions agree by the closed-dominant dimension lemma; replacing $k$ by the finite extension $e$ does not change chains of irreducible closed subsets. Write $A=\ker\alpha$. Retain $e^A/k$ and $k(V)^A/k(X')$ purely inseparable.

Original uses: lem-sfb-equivariant-curve-pencil, lem-sfb-equivariant-single-curve-nodal-reduction, lem-trf-closed-dominant-dimension.

Original source: literature/de-jong-families-curves-alterations-1997.pdf, Theorem 5.9 proof, curve pencil and marked one-curve reduction.

### Old step 4: parent assembly step 2 (lower-dimensional induction)

Apply the strengthened induction hypothesis in dimension $d-1$ to the $e$-scheme $B$, the finite group $G$ and its invariant nowhere dense boundary $D$. This gives $F/e$, a surjection $\beta:J\to G$, an H-projective alteration $h:P\to B$, and a marked quasi-split tower $P=T_{d-1}\to\cdots\to T_0=\operatorname{Spec}F$. Put $Q=\ker\beta$. The inductive data give $h^{-1}D\subseteq Z_{d-1}$, $F^Q/e$ purely inseparable and $k(P)^Q/k(B)$ purely inseparable. This is the induction hypothesis, not an invocation of the present theorem in unchanged dimension. No faithfulness of $G$ on $B$ is required in the strengthened claim.

Original uses: (induction hypothesis).

Original source: literature/de-jong-families-curves-alterations-1997.pdf, Theorem 5.9 proof, induction on the lower-dimensional base.

### Old step 5: lem-sfb-marked-nodal-tower-cartesian-extension, with generic integrality supplied by lem-sfb-flat-curve-pullback-function-field

Define $T_d=V\times_B P$, let $f_d:T_d\to P$ be the projection and let $a$ be the composite $T_d\to V\xrightarrow c X'\xrightarrow\pi X$. The diagonal $J$-action is defined by its action on $P$ and its action through $\beta$ on $V$; the fibre-product universal property gives its group law and equivariance. The base-change clauses of the one-curve node supply H-projectivity, flatness, finite presentation, nonempty connected reduced nodal geometric fibres, quasi-splitness, and smooth geometrically integral generic fibre for $f_d$. Dominance of $h$ ensures that this generic fibre is a field extension of the generic fibre of $v$. Pull back the sections $s_j$ to $P$; the identities $v s_j=\mathrm{id}$ and pairwise disjointness persist in the cartesian square.

Original uses: lem-sfb-equivariant-single-curve-nodal-reduction, def-pc-fibre-product.

Original source: literature/de-jong-families-curves-alterations-1997.pdf, Theorem 5.9 proof, final fibre-product construction.

### Old step 6: lem-sfb-flat-curve-pullback-function-field

The ordinary fibre product $T_d=V\times_B P$ is reduced. To check precisely the hypothesis of the flat geometrically reduced pullback lemma, fix any field $K$ and map $\operatorname{Spec}K\to B$. Choose an algebraic closure $\Omega/K$. Apply the arbitrary-base-change clause of the one-curve node over K; its geometric-fibre clause makes $V\times_B\operatorname{Spec}\Omega$ reduced. For every affine chart $\operatorname{Spec}A$ in $V\times_B\operatorname{Spec}K$, its scalar extension has ring $A\otimes_K\Omega$. The map $A\to A\otimes_K\Omega$ is injective: a $K$-linear functional $\Omega\to K$ sending $1$ to $1$, obtained by extending $1$ to a basis, gives a retraction after tensoring. A nilpotent of $A$ therefore vanishes, so the $K$-fibre is reduced. This is the elementary descent from algebraically closed fibres to the field-valued hypothesis actually stated by the pullback lemma. The base $P$ is reduced because it is integral. It is locally Noetherian by finite type over $F$ and the finite-type-over-Noetherian lemma; $\operatorname{Spec}F$ is Noetherian since a field has only the ideals $0$ and $F$. Apply the pullback lemma with $h=v$, $Y=V$, $S=B$, $T=P$ and $T\to S=h:P\to B$; it requires flatness of $v$, supplied by the one-curve node, and imposes no flatness condition on $P\to B$. The result $P\times_B V$ is our $T_d$ by the symmetry of the fibre-product universal property.

Original uses: lem-sfb-equivariant-single-curve-nodal-reduction, lem-sfb-flat-geometrically-reduced-pullback, lem-weil-pbc-finite-type-over-noetherian, def-pc-fibre-product, lem-weil-pbc-fibre-product-affine-spectra.

Original source: Mathlib/AlgebraicGeometry/Geometrically/Reduced.lean, GeometricallyReduced definition, lines 41--46, and the pullback instance at lines 128--131; elementary field-extension descent written explicitly; de Jong Theorem 5.9 induction, printed p.617..

### Old step 7: lem-sfb-flat-curve-pullback-function-field

The same ordinary fibre product is integral. The affine flatness criterion and the flat-module torsion-free lemma make its generic fibre over $P$ schematically dense: on affine charts over a domain $R$, a flat algebra injects into its localization at $R\setminus\{0\}$. If a nonempty affine basic open missed that fibre, its defining nonnilpotent element would become nilpotent after localization, contradicting this injection and reducedness. The generic fibre is integral by the one-curve node and dominance of $P\to B$, so its closure is irreducible and is the whole space. Thus $T_d$ is integral. Put $K=k(B)$, $M=k(P)$ and $L=k(V)$. Geometric integrality of the generic fibre of $v$ says $L\otimes_K M$ is a domain; since $M/K$ is finite, it is a finite-dimensional domain over $L$, hence a field. The affine fibre-product formula and localization identify it with the function field $k(T_d)$.

Original uses: lem-sfb-equivariant-single-curve-nodal-reduction, def-pc-geometrically-irreducible, lem-sc-integral-function-field-affine-fraction, lem-weil-pbc-flat-morphism-affine-criterion, lem-trf-flat-module-torsionfree-domain, lem-weil-pbc-fibre-product-affine-spectra.

Original source: literature/de-jong-families-curves-alterations-1997.pdf, Theorem 5.9 proof, verification of the fibre product; reducedness and generic density written out.

### Old step 8: lem-sfb-marked-nodal-tower-cartesian-extension

Let $Z_d=f_d^{-1}Z_{d-1}\cup\bigcup_j s'_j(P)$, with $s'_j$ the pulled-back sections. Pulling back $c^{-1}E\subseteq v^{-1}D\cup\bigcup_j s_j(B)$ and using $h^{-1}D\subseteq Z_{d-1}$ gives $a^{-1}Z\subseteq Z_d$. Every point of $P\setminus Z_{d-1}$ maps into $B\setminus D$, so the smoothness clause of the one-curve node makes $f_d$ smooth there. The lower tower already has the same properties by induction. Section unions and the recursively defined boundaries are $J$-stable. Quasi-splitness is the residue-field rationality of nodes and their two branches, preserved by base change; it does not prohibit the group from permuting the sections.

Original uses: lem-sfb-equivariant-single-curve-nodal-reduction.

Original source: literature/de-jong-families-curves-alterations-1997.pdf, Situation 5.8 and Theorem 5.9(b), boundary and equivariance verification.

### Old step 9: lem-sfb-marked-nodal-tower-cartesian-extension

The projection $T_d\to V$ is the base change of the H-projective surjection $h$. The base-change and composition lemmas make $a=\pi c\operatorname{pr}_V$ H-projective and surjective. This also makes it projective in the projective-bundle sense: use the free module $\mathcal O_X^{n+1}$ in an H-projective embedding. The tensor calculation in the preceding step shows that $k(T_d)/k(V)$ is finite. The one-curve reduction gives $k(V)/k(X')$ finite, while $k(X')=k(X)$ by the pencil. Hence $k(T_d)/k(X)$ is finite. The same finite-field argument applies to the lower-dimensional inductive map, and all maps to which these permanence statements are applied have already been constructed.

Original uses: lem-pc-projective-base-change, lem-trf-h-projective-composition, lem-weil-pbc-surjective-base-change, lem-trf-surjective-morphism-composition, def-trf-projective-bundle-morphism, lem-sfb-equivariant-curve-pencil, lem-sfb-equivariant-single-curve-nodal-reduction.

Original source: literature/de-jong-families-curves-alterations-1997.pdf, Theorem 5.9 proof, projectivity, surjectivity and generic finiteness; Stacks 01WE.

### Old step 10: lem-sfb-tensor-kernel-inseparable-invariants

Set $E_0=M^Q$. In $k(T_d)=L\otimes_K M$, the group $Q$ acts trivially on $L$. Apply the tensor-invariants node over the field $E_0$, with vector space $L\otimes_K E_0$ and extension $M/E_0$. Associativity of tensor products gives $(L\otimes_K M)^Q=L\otimes_K E_0$. This subalgebra is a field (it is the fixed subfield of a field). It is purely inseparable over $L$: in characteristic $p>0$, take a common $p$-power sending the finitely many coefficients of an element in $L\otimes_K E_0$ into $K$ and expand by Frobenius; in characteristic zero $E_0=K$. Put $N=\ker(\alpha\beta)$. The surjection $N\to A$ has kernel $Q$. For $z\in k(T_d)^N$ a $p$-power lies in $L$ by the preceding calculation, and lies in $L^A$ since $z$ was $N$-fixed. A further $p$-power lies in $k(X')=k(X)$ by the one-curve node. This proves the strengthened generic assertion. The identical two-power argument with $F^Q/e$ and $e^A/k$ gives $F^N/k$ purely inseparable. In characteristic zero both arguments use the first power. This establishes the induction.

Original uses: lem-weil-pbc-tensor-field-extension-galois-invariants, lem-sfb-equivariant-single-curve-nodal-reduction.

Original source: literature/de-jong-families-curves-alterations-1997.pdf, Theorem 5.9(a), Remarks 2.3(iii)--(iv); tensor-invariant and kernel calculations written out.

### Old step 11: lem-sfb-generic-invariant-field-orbit-open

It remains to obtain the dense open in every dimension, including the one-curve and length-zero cases. The scheme $X$ is Noetherian by finite type over a field. Choose a nonempty affine open $\operatorname{Spec}R\subseteq X$. The morphism $a$ is H-projective, hence projective, and its generic fibre is zero-dimensional because its function-field extension is finite. The projective-generically-finite lemma supplies a smaller nonempty affine open $U$ on which $a$ is finite. It remains surjective, since we restricted a surjective map on its target. Write $a^{-1}U=\operatorname{Spec}S$, with $S$ finite over $R=\mathcal O_X(U)$ and a domain, and let $K_X=\operatorname{Frac}R$, $P_X=\operatorname{Frac}S$. The subgroup $N$ fixes $X$ and $k$, so acts on this affine $k$-scheme over $U$. The finite quotient node applies with its orbit-in-an-affine hypothesis witnessed by the whole affine scheme. It gives $\operatorname{Spec}(S^N)$ as quotient, geometric quotient fibres equal to $N$-orbits, and $S^N$ finite over $R$.

Original uses: lem-weil-pbc-finite-type-over-noetherian, lem-fin-projective-generically-finite, lem-sfb-admissible-finite-type-field-quotient, lem-sc-integral-function-field-affine-fraction.

Original source: literature/de-jong-families-curves-alterations-1997.pdf, ILO X 2.2(iii), generic quotient verification; Stacks 03JE, 03BJ, 03BL via the cited quotient node.

### Old step 12: lem-sfb-generic-invariant-field-orbit-open

We have $\operatorname{Frac}(S^N)=P_X^N$. Indeed, for $x=s/t\in P_X^N$, the nonzero denominator $b=\prod_{n\in N}n(t)$ lies in $S^N$, and $bx\in S$ is invariant; hence $x=(bx)/b$. The finite-dimensional generic algebra $(S^N)\otimes_RK_X$ is a domain, so is this fixed field, which the induction proved purely inseparable over $K_X$. Choose finitely many $R$-module generators $r_i$ of $S^N$. In characteristic $p$ choose a common $q=p^m$ with $r_i^q\in K_X$; in characteristic zero take $q=1$. After inverting one nonzero $s\in R$ all these powers lie in $R[1/s]$. Frobenius then gives $r^q\in R[1/s]$ for every $r\in(S^N)[1/s]$. Two homomorphisms from this algebra to any field agreeing on $R[1/s]$ agree on all elements, since $q$th roots in a field are unique. The field-valued criterion in the radicial node therefore makes $\operatorname{Spec}(S^N)[1/s]\to\operatorname{Spec}R[1/s]$ universally injective.

Original uses: def-weil-radicial-morphism.

Original source: literature/de-jong-families-curves-alterations-1997.pdf, ILO X 2.2(iii); Stacks 01S4; explicit invariant fractions and common-power localization.

### Old step 13: lem-sfb-generic-invariant-field-orbit-open

Replace $U$ by $\operatorname{Spec}R[1/s]$. For any geometric point of $U$, the intermediate quotient has at most one geometric point by universal injectivity. It has at least one because $a$ is surjective and factors through it. The geometric-fibre statement of the finite quotient node now says that the entire geometric fibre of $a^{-1}U\to U$ is one $N$-orbit. The map is finite surjective by construction, and $U$ is dense because $X$ is integral. Together with the inductively constructed tower, boundary, constant extension and group surjection this proves every clause of the corrected statement.

Original uses: lem-sfb-admissible-finite-type-field-quotient, def-weil-radicial-morphism.

Original source: literature/de-jong-families-curves-alterations-1997.pdf, ILO X 2.2(iii); final geometric orbit verification.

## Verification

The required deliver.py --no-push completed with exit 0: OK (not pushed), temporary commit 55c10da7cb8, server preflight passed. This report records that receipt; the final unchanged mathematical payload is checked again before delivery. No local DAG/preflight/review checker was run.
