# Q57 repair: lem-sfb-projective-closed-subscheme-homogeneous-ideal

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-projective-closed-subscheme-homogeneous-ideal.json: statement unchanged; four-step assembly, 2449 characters.
- dag/nodes/sec-six-functors-basics/lem-sfb-homogeneous-quotient-chart-kernel.json: statement, unsplit; no Mathlib match. The separate algebraic task is exactness of the induced map on degree-zero homogeneous localizations, including its quotient isomorphism and degenerate denominators.
- dag/nodes/sec-six-functors-basics/lem-sfb-projective-local-equation-extension.json: statement, unsplit; no Mathlib match. The separate geometric task is homogenizing a local equation and extending its scheme-theoretic vanishing using a coordinate power.
- citations.json: one verbatim statement quotation per cited node per assembly step.
- returned-proof.md: the seven returned steps preserved verbatim for subsequent workers; also reproduced below.

## Attachments

None. I searched lean/WeilConjectures/AlgebraicGeometry by the item tag and by the projective/homogeneous-ideal notions. CoordinateModel.lean treats integral schemes over fields, not arbitrary closed subschemes over rings. The live Sheaf.AlgebraicGeometry.ProjectiveClosedSubschemeHomogeneousIdeal theorem exists_projectiveClosedSubscheme_homogeneousIdeal at line 101 ends in sorry at line 116. Its helper definitions are not proofs of the assertion, so the item cannot be attached. No Lean was written and nothing was compiled.

## WANTED

None. The sources used are available locally.

## Faults repaired and comparison with the returned version

The named sandbox initially contained no files or report. I copied the current repository node, whose seven steps have exactly the lengths listed in the return. This is a mathematical re-split of that retained returned argument, not an unchanged push. The current main statement, source, Lean record, accepted tool annotations and historical reviews are preserved. There is no blueprint_update on the item.

The human return requires at least two independent statement-only tasks and an assembly of at most 3000 characters. The graded chart exactness node extracts old Step 3 as a reusable graded-ring statement, independent of Z and of projective space. The equation-extension node extracts old Steps 4--6, independent of any quotient Proj or proposed homogeneous ideal. The item still proves the ideal property, applies the existing quotient-Proj construction, establishes both inclusions of the chart ideals using the two new statements, and gives the original explicit gluing argument. Neither new node restates the entire item, nor any of its final clauses. Both have empty proof/proof_deps, null proof_origin, status unsplit, full hypotheses, sources, blueprint ancestry and actual searches. Their arguments are retained in this report rather than smuggled into their statements.

I also replaced the old use of the definition of Proj for a theorem about the induced chart map with the already existing lem-sfb-graded-proj-quotient-twist-comparison. It explicitly gives the preimage of each standard open and the exact fraction formula. This reuse avoids a duplicate quotient-Proj chart node. The original prop-nagata-relative-proj-functoriality remains the generic tool for the closed immersion, clause (3) alone; no unit route is replaced. The item's chapter and unit remain untouched.

The first dry run rejected the new nodes' non-null ancestry. I inspected tools/blueprint_refs.py: its documented format explicitly uses null when the created.item chain is broken. Here the chain ends at the module name Sheaf.SixFunctors.CtfStabilityDirectImages, which is not a DAG node. I therefore set the new nodes' from.node to null, exactly as tools/blueprint_refs.py ancestor computes, while retaining the complete textual det-thm-sf-ctf-stability-direct-images support and the existing via chain in their from.place/from.via. The item's already accepted blueprint field is preserved. This follows the tool's documented broken-chain representation; no tool, parent node, or creation history is changed.

## Unfinished work

The two new statements are intentionally left unsplit for separate workers, as the return requires. No other requested work is omitted. Dry-run and push results are recorded after the checks below.

## Searches and duplication review

I searched the whole DAG with rg for 03GL, 01MY, homogeneous quotients/kernels, local equations and homogenization; I read the relevant candidates' statements. I searched the whole imported blueprint with tools/blueprint_refs.py for homogeneous, quotient, homogeneous localization, homogeneous quotient, local equation, vanishes, denominator, 03GL and 01MY. No imported node states either new result. The existing general section-clearing-denominators theorem extends an already given section of a quasi-coherent module; it does not identify sections with polynomial representatives or state that a prescribed homogeneous polynomial becomes zero on Z after a coordinate power. The existing graded quotient/twist theorem gives the chart map, not its kernel ideal, so it is cited rather than duplicated.

Every search recorded in the new nodes was actually run through batch2/msearch.py, with the exact query preserved in searches.jsonl. I read all hits and tried two independent semantic phrasings for each node. The first unquoted Loogle name patterns had unknown identifiers; those failures are recorded, and quoted name queries were run afterwards. LeanSearch and LeanFinder were available. The strongest algebraic candidate IsLocalization.ker_map is a theorem on ordinary localizations, whereas the new assertion concerns degree-zero subrings with homogeneous representatives. It requires a proof to pass to those subrings and is not a one-line specialization. I read HomogeneousLocalization.lean at the fraction-surjectivity and map declarations and Proj/Functor.lean at the chart-map formulas. For the geometric node, ProjectiveSpectrum.vanishingIdeal is an intersection of primes, not the vanishing of sections on a possibly nonreduced scheme; Polynomial.homogenize is a univariate polynomial construction only. There are no Mathlib leaves in this delivery.

## Not duplicates

lem-sfb-homogeneous-quotient-chart-kernel vs lem-sfb-proper-ample-section-proj-reconstruction: the existing node reconstructs a proper scheme with a relatively ample invertible module from its full section algebra and proves naturality for scheme and line-bundle isomorphisms. Its localization formula pulls back fractions of sections under that reconstruction; it neither assumes a homogeneous ideal K nor computes the kernel for S to S/K. The new node is exactness and a quotient-ring isomorphism for degree-zero homogeneous localization of an arbitrary graded ring quotient, including zero and nilpotent denominators. Neither statement specializes to the other.

lem-sfb-homogeneous-quotient-chart-kernel vs lem-trf-local-proj-isomorphism-compatibility: the existing statement assumes a graded algebra isomorphism and constructs inverse relative Proj maps, their compatibility with affine restriction, and invariance under degreewise unit rescaling. It neither assumes a homogeneous quotient nor identifies a localization kernel or the ring quotient by homogeneous fractions. The new statement applies to an arbitrary homogeneous ideal K in a graded ring S, including nonzero K and zero or nilpotent denominators, and proves the exact kernel formula for the induced degree-zero localization map. A graded algebra isomorphism alone cannot supply that formula.

lem-sfb-homogeneous-quotient-chart-kernel vs lem-sfb-projective-field-coordinate-euler-polynomial: the existing node concerns properness, coherence and the Euler/Hilbert polynomial of a closed projective scheme over a field, including existence of some homogeneous presentation. It does not compute the kernel of the degree-zero localization map for an arbitrary homogeneous ideal in an arbitrary graded commutative ring; this new algebraic statement neither assumes a field nor asserts a projective presentation.

lem-sfb-projective-local-equation-extension vs lem-sfb-projective-field-coordinate-euler-polynomial: the existing node gives an Euler/Hilbert polynomial and existence of a homogeneous presentation over a field. It does not extend a prescribed local equation to a polynomial vanishing scheme-theoretically on every chart by multiplying by a coordinate power. The new statement works over an arbitrary ring and specifies that equation and power, without a Hilbert-polynomial or Proj-presentation conclusion.

lem-sfb-homogeneous-quotient-chart-kernel vs lem-sfb-flat-projective-hilbert-polynomial-locality: the existing statement is Local constancy and base change of projective fibre Hilbert polynomials; it does not state exactness of a homogeneous quotient after degree-zero localization.

lem-sfb-homogeneous-quotient-chart-kernel vs lem-per-projective-closed-subscheme-homogeneous-ideal: the existing statement identifies an arbitrary closed projective subscheme with Proj of its vanishing ideal; this node states only the graded-localization kernel theorem, without a closed subscheme or Proj conclusion.

lem-sfb-homogeneous-quotient-chart-kernel vs lem-per-finite-graded-proj-morphism: the existing statement is Finite graded extensions induce finite surjective Proj maps; it does not state exactness of a homogeneous quotient after degree-zero localization.

lem-sfb-homogeneous-quotient-chart-kernel vs lem-trf-relative-proj-invertible-twist: the existing statement is Relative Proj is invariant under tensoring by an invertible module; it does not state exactness of a homogeneous quotient after degree-zero localization.

lem-sfb-homogeneous-quotient-chart-kernel vs lem-per-projective-finite-group-quotient: the existing statement is Finite group quotients preserve relative projectivity; it does not state exactness of a homogeneous quotient after degree-zero localization.

lem-sfb-homogeneous-quotient-chart-kernel vs lem-sfb-graded-proj-quotient-twist-comparison: the existing theorem compares Proj charts and twisting sheaves; this node identifies the algebraic kernel and quotient ring of a homogeneous localization map, not supplied by that statement.

lem-sfb-homogeneous-quotient-chart-kernel vs lem-per-equivariant-projective-envelope: the existing statement is An equivariant homogeneous projective envelope; it does not state exactness of a homogeneous quotient after degree-zero localization.

lem-sfb-homogeneous-quotient-chart-kernel vs lem-sfb-projective-hilbert-polynomial-representability: the existing statement is Projective representability of the full Hilbert functor by Hilbert polynomial; it does not state exactness of a homogeneous quotient after degree-zero localization.

lem-sfb-homogeneous-quotient-chart-kernel vs def-sfb-relative-proj-iso-of-graded-iso: the existing statement is Canonical relative Proj isomorphism induced by a graded algebra isomorphism; it does not state exactness of a homogeneous quotient after degree-zero localization.

lem-sfb-homogeneous-quotient-chart-kernel vs lem-sfb-projective-closed-subscheme-homogeneous-ideal: the existing statement identifies an arbitrary closed projective subscheme with Proj of its vanishing ideal; this node states only the graded-localization kernel theorem, without a closed subscheme or Proj conclusion.

lem-sfb-homogeneous-quotient-chart-kernel vs lem-coef-system-localization-universal: the existing statement is Functorial infinity localization preserves finite products; it does not state exactness of a homogeneous quotient after degree-zero localization.

lem-sfb-homogeneous-quotient-chart-kernel vs def-sfb-projective-coordinate-hilbert-polynomial: the existing statement is Coordinate Hilbert polynomial and canonical geometric-fibre embeddings; it does not state exactness of a homogeneous quotient after degree-zero localization.

lem-sfb-homogeneous-quotient-chart-kernel vs lem-sfb-hilbert-uniform-section-bound: the existing statement is Uniform generation and section bounds for projective ideals with fixed Hilbert polynomial; it does not state exactness of a homogeneous quotient after degree-zero localization.

lem-sfb-homogeneous-quotient-chart-kernel vs lem-coef-contractible-factor-universal-localization: the existing statement is A contractible factor preserves universal localization; it does not state exactness of a homogeneous quotient after degree-zero localization.

lem-sfb-homogeneous-quotient-chart-kernel vs lem-cbc-simplicial-groupoid-localization: the existing statement is Groupoid localization of a simplicial shape; it does not state exactness of a homogeneous quotient after degree-zero localization.

lem-sfb-homogeneous-quotient-chart-kernel vs prop-nagata-relative-proj-functoriality: the existing statement is Restriction, base change, and functoriality of Proj; it does not state exactness of a homogeneous quotient after degree-zero localization.

lem-sfb-homogeneous-quotient-chart-kernel vs lem-nagata-affine-proj-scalar-extension: the existing statement is Scalar extension of affine Proj with its chart maps; it does not state exactness of a homogeneous quotient after degree-zero localization.

lem-sfb-homogeneous-quotient-chart-kernel vs lem-nagata-proj-affine-restriction: the existing statement is Affine-base restriction maps for projective spectra of a graded algebra sheaf; it does not state exactness of a homogeneous quotient after degree-zero localization.

lem-sfb-homogeneous-quotient-chart-kernel vs lem-coef-weak-equivalence-representable-local-model: the existing statement is Local model of a weak-equivalence representable presheaf; it does not state exactness of a homogeneous quotient after degree-zero localization.

lem-sfb-homogeneous-quotient-chart-kernel vs lem-coef-enriched-category-tensor-calculus: the existing statement is Tensor, internal Hom and diagram calculus of enriched infinity categories; it does not state exactness of a homogeneous quotient after degree-zero localization.

lem-sfb-homogeneous-quotient-chart-kernel vs lem-coef-hammock-infinity-localization: the existing statement is Hammock localization presents universal infinity localization; it does not state exactness of a homogeneous quotient after degree-zero localization.

lem-sfb-projective-local-equation-extension vs lem-sfb-flat-projective-hilbert-polynomial-locality: the existing statement is Local constancy and base change of projective fibre Hilbert polynomials; it does not state extension of an arbitrary local equation on a closed projective subscheme by a coordinate power.

lem-sfb-projective-local-equation-extension vs lem-per-projective-closed-subscheme-homogeneous-ideal: the existing statement identifies an arbitrary closed projective subscheme with Proj of its vanishing ideal; this node states only extension of one local equation, without constructing an ideal or a quotient Proj.

lem-sfb-projective-local-equation-extension vs lem-per-finite-graded-proj-morphism: the existing statement is Finite graded extensions induce finite surjective Proj maps; it does not state extension of an arbitrary local equation on a closed projective subscheme by a coordinate power.

lem-sfb-projective-local-equation-extension vs lem-trf-relative-proj-invertible-twist: the existing statement is Relative Proj is invariant under tensoring by an invertible module; it does not state extension of an arbitrary local equation on a closed projective subscheme by a coordinate power.

lem-sfb-projective-local-equation-extension vs lem-per-projective-finite-group-quotient: the existing statement is Finite group quotients preserve relative projectivity; it does not state extension of an arbitrary local equation on a closed projective subscheme by a coordinate power.

lem-sfb-projective-local-equation-extension vs lem-sfb-graded-proj-quotient-twist-comparison: the existing theorem compares Proj charts and twisting sheaves; this node extends a local equation on an independently given closed subscheme; there is no graded quotient morphism in its hypotheses.

lem-sfb-projective-local-equation-extension vs lem-per-equivariant-projective-envelope: the existing statement is An equivariant homogeneous projective envelope; it does not state extension of an arbitrary local equation on a closed projective subscheme by a coordinate power.

lem-sfb-projective-local-equation-extension vs lem-sfb-projective-hilbert-polynomial-representability: the existing statement is Projective representability of the full Hilbert functor by Hilbert polynomial; it does not state extension of an arbitrary local equation on a closed projective subscheme by a coordinate power.

lem-sfb-projective-local-equation-extension vs def-sfb-relative-proj-iso-of-graded-iso: the existing statement is Canonical relative Proj isomorphism induced by a graded algebra isomorphism; it does not state extension of an arbitrary local equation on a closed projective subscheme by a coordinate power.

lem-sfb-projective-local-equation-extension vs lem-sfb-projective-closed-subscheme-homogeneous-ideal: the existing statement identifies an arbitrary closed projective subscheme with Proj of its vanishing ideal; this node states only extension of one local equation, without constructing an ideal or a quotient Proj.

lem-sfb-projective-local-equation-extension vs lem-coef-system-localization-universal: the existing statement is Functorial infinity localization preserves finite products; it does not state extension of an arbitrary local equation on a closed projective subscheme by a coordinate power.

lem-sfb-projective-local-equation-extension vs def-sfb-projective-coordinate-hilbert-polynomial: the existing statement is Coordinate Hilbert polynomial and canonical geometric-fibre embeddings; it does not state extension of an arbitrary local equation on a closed projective subscheme by a coordinate power.

lem-sfb-projective-local-equation-extension vs lem-sfb-hilbert-uniform-section-bound: the existing statement is Uniform generation and section bounds for projective ideals with fixed Hilbert polynomial; it does not state extension of an arbitrary local equation on a closed projective subscheme by a coordinate power.

lem-sfb-projective-local-equation-extension vs lem-coef-contractible-factor-universal-localization: the existing statement is A contractible factor preserves universal localization; it does not state extension of an arbitrary local equation on a closed projective subscheme by a coordinate power.

lem-sfb-projective-local-equation-extension vs lem-cbc-simplicial-groupoid-localization: the existing statement is Groupoid localization of a simplicial shape; it does not state extension of an arbitrary local equation on a closed projective subscheme by a coordinate power.

lem-sfb-projective-local-equation-extension vs prop-nagata-relative-proj-functoriality: the existing statement is Restriction, base change, and functoriality of Proj; it does not state extension of an arbitrary local equation on a closed projective subscheme by a coordinate power.

lem-sfb-projective-local-equation-extension vs lem-nagata-affine-proj-scalar-extension: the existing statement is Scalar extension of affine Proj with its chart maps; it does not state extension of an arbitrary local equation on a closed projective subscheme by a coordinate power.

lem-sfb-projective-local-equation-extension vs lem-nagata-proj-affine-restriction: the existing statement is Affine-base restriction maps for projective spectra of a graded algebra sheaf; it does not state extension of an arbitrary local equation on a closed projective subscheme by a coordinate power.

lem-sfb-projective-local-equation-extension vs lem-coef-weak-equivalence-representable-local-model: the existing statement is Local model of a weak-equivalence representable presheaf; it does not state extension of an arbitrary local equation on a closed projective subscheme by a coordinate power.

lem-sfb-projective-local-equation-extension vs lem-coef-enriched-category-tensor-calculus: the existing statement is Tensor, internal Hom and diagram calculus of enriched infinity categories; it does not state extension of an arbitrary local equation on a closed projective subscheme by a coordinate power.

lem-sfb-projective-local-equation-extension vs lem-coef-hammock-infinity-localization: the existing statement is Hammock localization presents universal infinity localization; it does not state extension of an arbitrary local equation on a closed projective subscheme by a coordinate power.

## Review by Q57

I read Stacks constructions.tex, Tag 03GL, label lemma-closed-in-projective-space, including both inclusions of J and J'. The chartwise definition of I_d in the item is the kernel of the map to Gamma(Z,O(d)|Z) in that lemma: on U_j, z_j^d is the standard basis, and the charts cover Z. The target statement is unchanged, and the nilpotent information in vanishing of sections is retained. For the new kernel statement I also read Tag 01MY, label lemma-morphism-proj, clause (2) and its fraction-map proof; for the geometric extension statement I read the full converse inclusion in 03GL, especially its powers T_0^{d_i} and their maximum. No SGA source is involved.

Assembly Step 1 is the original explicit elementary argument: each I_d is a submodule, multiplication by H sends it into I_{d+e}, and finite homogeneous decompositions make the direct sum an ideal. It uses no theorem disguised as a citation. Step 2 uses the statement of prop-nagata-relative-proj-functoriality, clause (3), for the surjective quotient; lem-sfb-graded-proj-quotient-twist-comparison for the chart map and preimages; prop-nagata-proj-standard-open for the cover; and the affine-quotient equivalence explicitly present in def-weil-closed-immersion. I opened all four statements. The polynomial ring is generated in degree one, the quotient homomorphism is graded and onto, and the family of variables generates the irrelevant ideal. These are precisely the hypotheses needed.

Step 3 uses the complete conclusion of the new kernel node with S=B, f=z_a and K=I, whose homogeneity Step 1 proved. Its quotient isomorphism is over A_a, hence determines the same closed embedding on each chart, not merely an abstract ring isomorphism. For the reverse inclusion the new extension node applies to the actual given closed immersion Z into P, and to f in the restriction kernel J_a. Its F,d,N give G in the exact I_{d+N} used by the item. Neither reducedness nor finite generation is inserted. The other inclusion follows directly from the definition of I_d. I checked these are statements of the cited nodes, not facts borrowed from their unwritten proofs; citations.json copies their statements verbatim.

Step 4 retains the original gluing argument with all of its force. def-weil-affine-spectrum supplies functorial inverse local scheme isomorphisms from the A_a-algebra identifications. def-weil-closed-immersion explicitly gives the homeomorphism onto the image and surjectivity of the structure-sheaf maps; these force both the point maps and stalk maps of the local comparisons on overlaps. Cancelling the surjective quotient maps on stalks proves equality of sheaf maps. lem-weil-pbc-scheme-morphism-gluing states existence and uniqueness for the two compatible families, and uniqueness makes the composites identities. I read these three cited statements. This argument is kept in the item, not hidden in a third new node.

For the new kernel node, the quotient grading is defined by images and K is required to be homogeneous: degreewise representatives really lift, and the directness follows by applying homogeneous-component projections to membership in K. Applying the localization relation to a zero fraction gives f^k s in K, in degree d+k, so s/f^d=(f^k s)/f^{d+k} belongs to the displayed kernel ideal. This additional homogeneous-degree bookkeeping is why the ordinary-localization Mathlib result is not an attachment. For the extension node, each Z_j is affine by the closed-immersion criterion. Old Step 5 uses exactly clause (0) of lem-weil-pbc-affine-ideals-closed-subscheme, the zero criterion of def-weil-ring-localization-away, and the overlap statement of lem-weil-pbc-proj-basic-open-intersection with both degrees one. I read all those statements; the overlap is the principal open of the image of z_a/z_j in the actual quotient ring E_j. The transition h_j=t_j^d f is equality of sections after restriction. No inference from topological vanishing to section vanishing occurs.

I checked the source and every new statement on R=0, Z empty, Z=P, n=0, and a nonreduced closed subscheme cut out by (z_1^2) in P^1. In the kernel lemma I additionally tested K=0, K=S, f=0, a nilpotent f, and a quotient in which bar f is zero. Both localizations may be zero rings; the localization zero criterion still holds and no denominator is cancelled. In the extension lemma n=0 leaves just the one chart, where N=0 works; empty Z gives zero section rings, and the nonreduced example requires the actual square equation rather than its radical. Finiteness of n+1 allows one maximum and never assumes a finite type base ring.

B1--B7: the new nodes are statement-only, introduce all their own data, cite the definitions used, and contain ordinary single TeX escapes in their parsed strings. Their sources give tags and labels, not unstable section numbers. The source-tag collision pairs are discussed above. C1/C4 were checked against the opened statements and the exact quotes. D1/D2 are repaired by the two independent tasks and the retained construction/gluing assembly. E was checked by the hypotheses and degenerate cases just described. No step exceeds 2000 characters. The return's original 4977 characters have not been discarded: every original step is reproduced next, so workers taking the extracted statements retain the full available argument.

## Preservation of all seven returned arguments

- Old Step 1 remains assembly Step 1.
- Old Step 2 remains assembly Step 2, now with the explicit existing chart-map statement cited.
- Old Step 3 is the argument for lem-sfb-homogeneous-quotient-chart-kernel, used in assembly Step 3.
- Old Steps 4, 5 and 6 are the argument for lem-sfb-projective-local-equation-extension, used in assembly Step 3; both inclusions are assembled there.
- Old Step 7 remains assembly Step 4, including forced overlap agreement and uniqueness of the two glued inverses.

### Returned proof, retained verbatim

## Step 1

For every $d$, the set $I_d$ is an $R$-submodule of $B_d$: restriction of $(F+G)/z_i^d$ is the sum of the restrictions and restriction commutes with scalar multiplication. For $F\in I_d$ and $H\in B_e$, the equality $(HF)/z_i^{d+e}=(H/z_i^e)(F/z_i^d)$ shows $HF\in I_{d+e}$. Every polynomial is a finite sum of homogeneous components, so distributing multiplication proves that $I=\bigoplus_d I_d$ is an ideal; its definition as this direct sum proves homogeneity. Give $C=B/I$ the quotient grading $C_d=B_d/I_d$.

Uses: 

## Step 2

Apply the surjective graded-map clause (3) of [prop-nagata-relative-proj-functoriality] in its affine-base case to the graded quotient $B\twoheadrightarrow C$. It gives the canonical closed immersion $Z'=\operatorname{Proj}(C)\hookrightarrow P=\operatorname{Proj}(B)$. By [prop-nagata-proj-standard-open], the opens $U_a=D_+(z_a)$ cover $P$, and $D_+(\bar z_a)$ cover $Z'$, since the variables generate the irrelevant ideals of both graded rings. Put $A_a=B_{(z_a),0}$. The affine characterization in [def-weil-closed-immersion] writes $Z\cap U_a=\operatorname{Spec}(A_a/J_a)$ for the kernel ideal $J_a$ of the restriction map.

Uses: prop-nagata-relative-proj-functoriality, prop-nagata-proj-standard-open, def-weil-closed-immersion

## Step 3

The chart restriction maps in [def-pc-proj] and the fractions in [def-nagata-homogeneous-localization-degree-zero] identify the map over $U_a$ with $q_a:A_a\to C_{(\bar z_a),0}$, $F/z_a^d\mapsto\bar F/\bar z_a^d$. It is onto, since each homogeneous numerator in $C_d$ lifts to $B_d$. Its kernel is the ideal $J'_a$ generated by all $F/z_a^d$ with $F\in I_d$. Indeed these generators map to zero. Conversely, if $q_a(F/z_a^d)=0$, the localization relation [def-weil-ring-localization-away] gives $\bar z_a^k\bar F=0$ for some $k\geq0$. Thus $z_a^kF\in I_{d+k}$, and $F/z_a^d=(z_a^kF)/z_a^{d+k}$ is itself one of the generators. Consequently $C_{(\bar z_a),0}\cong A_a/J'_a$ over $A_a$, with inverse sending the class of $F/z_a^d$ to $\bar F/\bar z_a^d$. No cancellation or nonzero-denominator hypothesis is used.

Uses: def-pc-proj, def-nagata-homogeneous-localization-degree-zero, def-weil-ring-localization-away

## Step 4

If $F\in I_d$, the definition of $I_d$ says precisely that $F/z_a^d$ maps to zero on $Z\cap U_a$, hence belongs to $J_a$. The generators of $J'_a$ therefore belong to $J_a$, and $J'_a\subseteq J_a$. For the reverse inclusion fix $f\in J_a$. Write $f$ as a polynomial in the ratios $z_k/z_a$ ($k\ne a$). Choose $d$ at least every monomial degree and homogenize term by term: replace $c\prod_{k\ne a}(z_k/z_a)^{e_k}$ by $c z_a^{d-\sum e_k}\prod_{k\ne a}z_k^{e_k}$. The resulting $F\in B_d$ satisfies $f=F/z_a^d$. This description of $A_a$ follows directly from the fraction definition: dehomogenization and this homogenization are inverse on degree-zero fractions.

Uses: def-nagata-homogeneous-localization-degree-zero

## Step 5

For each $j\ne a$ put $Z_j=Z\cap U_j$, which is affine by [def-weil-closed-immersion], with section ring $E_j=A_j/J_j$. Let $t_j$ and $h_j$ be the images of $z_a/z_j$ and $F/z_j^d$ in $E_j$. Inside $Z_j$ the overlap with $Z\cap U_a$ is the principal open $D(t_j)$: by [lem-weil-pbc-proj-basic-open-intersection] (with $f=z_j$, $g=z_a$, $d=e=1$) the overlap $U_j\cap U_a$ is the principal open of $z_a/z_j$ in $U_j$, and its inverse image under $Z_j\to U_j=\operatorname{Spec}A_j$ is the principal open of the image $t_j$. On this overlap the transition maps in [def-pc-proj] give $h_j=t_j^d f=0$. Clause (0) of [lem-weil-pbc-affine-ideals-closed-subscheme], applied to the scheme $Z$ and its affine open $Z_j$, identifies the restriction of $E_j$ to $D(t_j)$ with localization at $t_j$. The zero criterion in [def-weil-ring-localization-away] therefore gives $k_j\geq0$ with $t_j^{k_j}h_j=0$ in $E_j$. This uses actual vanishing in the quotient ring, not vanishing just at its points.

Uses: def-weil-closed-immersion, def-pc-proj, lem-weil-pbc-affine-ideals-closed-subscheme, def-weil-ring-localization-away, lem-weil-pbc-proj-basic-open-intersection

## Step 6

Set $k_a=0$ and choose $N=\max_{0\leq j\leq n}k_j$; this finite nonempty index set exists also for $n=0$. Put $G=z_a^N F\in B_{d+N}$. On the $j$ chart with $j\ne a$, its restriction to $Z_j$ is $t_j^Nh_j=t_j^{N-k_j}(t_j^{k_j}h_j)=0$. On the $a$ chart it is $G/z_a^{d+N}=F/z_a^d=f$, which is zero on $Z\cap U_a$ since $f\in J_a$. Thus $G\in I_{d+N}$ by the defining condition on all charts. The equality $f=G/z_a^{d+N}$ then gives $f\in J'_a$. Together with Step 4 this proves $J_a=J'_a$ for every $a$.

Uses: 

## Step 7

Steps 2--6 identify both $Z\cap U_a$ and $Z'\cap U_a$ over $U_a$ with $\operatorname{Spec}(A_a/J_a)$; spectrum functoriality [def-weil-affine-spectrum] gives inverse local isomorphisms over $P$. These isomorphisms agree on overlaps: their point maps are forced by the two closed embeddings into $P$, and their structure-sheaf maps are forced by commuting with the locally surjective maps from $\mathcal O_P$ in [def-weil-closed-immersion]. Equality can be checked on stalks, where surjectivity allows cancellation of those quotient maps. Glue the maps in each direction by [lem-weil-pbc-scheme-morphism-gluing]; the composites are identities by its uniqueness clause. This identifies $Z'$ with $Z$ as a closed subscheme of $P$. The argument used arbitrary quotient rings and finitely many standard charts, so applies to nonreduced and empty $Z$ and to the zero base ring as well.

Uses: def-weil-affine-spectrum, def-weil-closed-immersion, lem-weil-pbc-scheme-morphism-gluing


## Returned landing repair, 2026-10-22

The returned delivery is head afc18272635, identified in coord/returns/Q57.md. Its split, two helper statements, search records, citations and report were retained in this sandbox. The landing return concerns promotion of the side completion to the live queue, not a mathematical rejection. I compared the retained item against the current shared DAG: the only differing item fields are proof, proof_deps and split_report; its statement, stmt_deps, source, blueprint ancestry, creation history, Lean record and historical reviews agree. Both helper IDs are absent from the current shared DAG. The required delivery command fetches the current sheaf-dag tip and overlays only worker-owned fields, so the repaired packet is based on the current DAG rather than the returned base.

I reread every current statement cited by the assembly: prop-nagata-relative-proj-functoriality still supplies the surjective graded-map closed immersion in clause (3); lem-sfb-graded-proj-quotient-twist-comparison supplies exactly its chart preimages and fraction map; prop-nagata-proj-standard-open supplies the standard-open cover; def-weil-closed-immersion supplies the affine quotient and surjective structure-sheaf descriptions; def-weil-affine-spectrum supplies the functorial affine isomorphisms; lem-weil-pbc-scheme-morphism-gluing supplies existence and uniqueness of the glued maps. The statements used by the two helper nodes, def-nagata-homogeneous-localization-degree-zero, def-weil-ring-localization-away and def-pc-proj, retain the fractions, localization equality and standard affine charts required here. The nine assembly citation pairs remain verbatim substrings of those current statements or of the retained new statements. No dependency replacement or altered hypothesis is needed.

The first required dry run completed with a duplicate-check diagnostic for the newly present lem-sfb-projective-field-coordinate-euler-polynomial (Stacks 03GL). I opened its full statement: it gives Euler/Hilbert-polynomial results over a field and existence of a homogeneous presentation, not either helper assertion. I added both explicit comparisons under Not duplicates. This repairs a concrete difference between the returned packet and the current DAG. The helper statements and their recorded search questions have not changed, so I read and reused searches.jsonl instead of rerunning or inventing searches.

For the renewed mathematical review I reread Stacks constructions.tex, lemma-closed-in-projective-space (03GL), and lemma-morphism-proj (01MY), including its chart-fraction formula. Step 1 still proves the ideal property directly. Step 2 applies its cited statements to the degree-one polynomial algebra and its surjective graded quotient. Step 3 applies the kernel statement to the actual homogeneous ideal, and the extension statement to the given closed immersion and its restriction kernel, so it proves both inclusions without a reducedness hypothesis. Step 4's local inverses commute with the embeddings and therefore agree on overlaps, using the surjective structure-sheaf maps; the cited gluing uniqueness proves the two global composites are identities. I checked the helper statements again for zero or nilpotent denominators, zero rings, empty charts, n=0, Z empty, Z=P, and the nonreduced example cut out by z_1^2. The finite chart set ensures a maximum exponent in the extension argument; the kernel argument uses a power annihilator, never cancellation. No statement dispute arises. Each assembly step is below 2000 characters and the assembly remains below the 3000-character repair limit. The earlier argument-preservation section and returned-proof.md are retained.


## Review by Q57: renewed landing repair

I continued the retained afc18272635 repair packet, including both helper statements, the preserved seven-step argument, citations.json and searches.jsonl. The required initial dry run against the latest fetched DAG exited with a new duplicate-check diagnostic: lem-trf-local-proj-isomorphism-compatibility now also cites 01MY. I opened that node in full. Its hypotheses require an isomorphism of graded quasi-coherent algebra sheaves and its conclusions describe local Proj isomorphisms, restriction compatibility and degreewise-unit invariance. None states the kernel of a localization map for an arbitrary homogeneous quotient. The new comparison under Not duplicates is the concrete repair to this returned packet; no argument or recorded search has been discarded. The helper statements and search questions are unchanged, so their logged searches were read and reused as instructed.

I compared the sandbox item field by field with the current shared node. Only proof, proof_deps and split_report differ; the unchanged statement and statement dependencies, source, blueprint field, historical reviews and Lean record are preserved. Neither helper exists in that DAG. The current released stage-1 repair note still explicitly requires at least two statement-only nodes and a short assembly. The delivery script will rebase the packet onto its fetched current DAG; no repository git command was run.

I reread Tag 03GL, constructions.tex lemma-closed-in-projective-space, and Tag 01MY, lemma-morphism-proj, clauses (1)--(2) and its fraction formulas. The former supplies the homogeneous-equations construction and coordinate-power extension argument; the latter supplies the chart-map formula supporting the separate algebraic task. Step 1 directly proves the ideal property by restriction and homogeneous multiplication. Step 2 uses the current surjective-map clause of prop-nagata-relative-proj-functoriality, the explicit chart formula of lem-sfb-graded-proj-quotient-twist-comparison, the cover clause of prop-nagata-proj-standard-open, and the affine quotient criterion of def-weil-closed-immersion. The polynomial grading is generated in degree one and its quotient map is surjective, so these hypotheses hold. Step 3 uses the two helper statements exactly as written: the first computes the chart kernel for K=I, and the second extends an element of J_a to G in the specified homogeneous vanishing ideal. Both inclusions of J_a=J'_a remain explicit. Step 4 uses def-weil-affine-spectrum for inverse affine maps, the locally surjective sheaf maps of def-weil-closed-immersion for their forced overlap equality, and existence and uniqueness in lem-weil-pbc-scheme-morphism-gluing for the global inverse maps. All nine citations.json entries are still verbatim parts of these statements.

I also reread def-pc-proj, def-nagata-homogeneous-localization-degree-zero, def-weil-ring-localization-away, the principal-open localization clause (0) of lem-weil-pbc-affine-ideals-closed-subscheme and lem-weil-pbc-proj-basic-open-intersection, which justify the retained arguments for future helper workers. The kernel argument clears an annihilating power and never cancels a zero divisor. The extension argument takes a maximum over n+1 charts and uses equality of sections on the actual quotient scheme. Thus the zero ring, K=S, f=0 or nilpotent, a quotient with bar f=0, n=0, empty Z, Z=P and the square ideal (z_1^2) in projective one-space remain valid tests. No reduction, Noetherian, finite-presentation or nonempty hypothesis has slipped in. The helpers remain statement-only and neither restates a conclusion clause of the item. Each assembly step is below 2000 characters and their sum remains 2449, below the required 3000. No mathematical statement correction was necessary.


## Review by Q57: current-DAG repair of returned head 9469042e5d3

The current return entry in coord/returns/Q57.md identifies 9469042e5d3 (2026-10-22 16:24 UTC), approved mathematically but refused at landing because the side completion had not been promoted to the live DAG. I continued its retained sandbox files rather than reconstructing or deleting them. Comparison with the current shared item shows differences only in proof, proof_deps and split_report. The statement, statement dependencies, source, blueprint, creation history, accepted tool annotations, reviews and Lean record agree; both helper IDs are still absent from the shared DAG. The released stage-1 repair note still requires two new statement-only tasks and an assembly under 3000 characters. The delivery command fetches the current DAG and builds its own rebased delivery tree.

As required I ran the retained packet's dry run first. It exited with a new 01MY collision, lem-sfb-proper-ample-section-proj-reconstruction. I opened that node's full statement: its proper morphism and relatively ample invertible-module hypotheses lead to reconstruction from the full section algebra and naturality under isomorphisms, not a kernel computation for a homogeneous quotient. I added the explicit pair comparison under Not duplicates. This is the concrete current-DAG adjustment; the helper statements and search questions remain unchanged. I read the retained searches.jsonl and all recorded results, including the ordinary-localization candidate IsLocalization.ker_map and the pointwise vanishing-ideal hits, and reused those searches without recording a new query.

I reread the local Stacks source constructions.tex, Tag 03GL, lemma-closed-in-projective-space, including its polynomial homogenization and maximum coordinate-power argument, and Tag 01MY, lemma-morphism-proj, including the inverse-image and induced fraction-map formulas. Both helper statements match these arguments with their hypotheses explicit. The kernel helper concerns any nonnegative grading, a degree-one element and a homogeneous ideal; it does not require a projective presentation. The extension helper concerns a given closed immersion over any ring and an actual vanishing section on one chart; it does not construct a quotient Proj or assume reducedness. Their arguments remain in the retained seven-step proof and report for the workers who will prove them.

For Step 1 I checked the displayed restriction and multiplication equalities: they prove the homogeneous ideal property directly, with no uncited theorem. For Step 2 I reread every cited current statement. Clause (3) of prop-nagata-relative-proj-functoriality supplies the closed immersion for the surjective graded quotient; lem-sfb-graded-proj-quotient-twist-comparison supplies exactly the chart inverse images and fraction map; prop-nagata-proj-standard-open supplies the covering because the variables generate the irrelevant ideal; def-weil-closed-immersion supplies the affine quotient rings. The source algebra is generated in degree one, as the comparison requires. For Step 3 I checked both helper statements as written: specialize the kernel theorem to S=B, K=I and f=z_a, and apply extension to f in the restriction kernel J_a. Definition of I gives the first ideal inclusion; the stated extension gives a homogeneous numerator in I and the second inclusion. For Step 4 I reread def-weil-affine-spectrum, the sheaf-surjectivity part of def-weil-closed-immersion, and the existence/uniqueness assertion of lem-weil-pbc-scheme-morphism-gluing. The quotient ring identifications give inverse affine maps over P; surjective stalk maps force overlap agreement, and uniqueness of gluing makes the two composites identities. All nine citation entries are verbatim substrings of these current statements and cite exactly what their steps use.

I also reread the current definitions of homogeneous localization, localization away and Proj, the principal-open localization clause (0) of lem-weil-pbc-affine-ideals-closed-subscheme and the degree-one specialization of lem-weil-pbc-proj-basic-open-intersection. They justify the preserved helper arguments with no added Noetherian or finite-presentation hypothesis. I tested zero rings, K=0 and K=S, f=0 and nilpotent f, zero image of f in the quotient, n=0, empty Z, Z=P and the nonreduced square equation (z_1^2) on projective one-space. The annihilating-power criterion works even for zero localizations; the extension uses finitely many charts and section equality rather than pointwise vanishing. No statement correction is needed. Both helpers remain self-contained statement-only nodes, and neither restates a conclusion clause of the item. Every assembly step is below 2000 characters and their total is 2449. The previous proof, citations, search log and reports are retained, and no Lean or repository files were written.
