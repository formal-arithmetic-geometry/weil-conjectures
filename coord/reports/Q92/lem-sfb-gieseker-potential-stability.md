# Q92: lem-sfb-gieseker-potential-stability

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-gieseker-potential-stability.json`: existing statement preserved; 15 proof steps; status split; statement dependencies completed.
- `lem-sfb-bounded-hilbert-weight-polynomials`: statement, unsplit; no Mathlib match. Bounded-weight uniform Hilbert polynomial, half-integral quadratic coefficient and numerical test.
- `lem-sfb-component-projection-weight-bounds`: statement, unsplit; no Mathlib match. Explicit projection-flag coefficient bounds, rather than semistability conclusions.
- `lem-sfb-singular-point-jet-weight-bounds`: statement, unsplit; no Mathlib match. Multiplicity, ramification and tangency jet-weight computations.
- `lem-sfb-subcurve-span-weight-bound`: statement, unsplit; no Mathlib match. Selected-boundary weight computation including rational-normal exceptions and disconnected subcurves.
- `lem-sfb-nodal-special-clifford-subcurve`: statement, unsplit; no Mathlib match. Clifford support subcurve for a special very ample line, without any GIT hypothesis.
- `lem-sfb-gieseker-component-interpolation`: statement, unsplit; no Mathlib match. Component/node interpolation prerequisite, not a conclusion of the item.
- `lem-sfb-coherent-zero-dimensional-support`: statement, unsplit; no Mathlib match. Stacks 0B3J: coherent generation and acyclicity on zero-dimensional support.
- `citations.json`: a verbatim statement quotation for every citation in every item proof step.

The seven new nodes are all in `dag/nodes/sec-six-functors-basics/`. They contain statements only, empty proof/dependency lists and null proof origins. There are zero Mathlib leaves. No Lean or repository file was written, and no compiler/build/git command was run by this worker. Search scripts and their full outputs are preserved in the sandbox.

## Attachments

None. I searched `lean/WeilConjectures/` for the blueprint id, Gieseker, potential stability, Hilbert weights and Hilbert--Mumford. There is no project declaration giving this item or any new numerical claim. Clifford representation-theory declarations are a different theorem.

## Wanted literature

WANTED: `literature/morrison-git-stable-curves-arXiv-0810.2340.pdf`, Sections 2.1 and 3.2--3.3, for the item and its six GIT/curve prerequisites. I read the primary PDF online at https://arxiv.org/pdf/0810.2340 ; I did not download it into the shared repository or sandbox.

WANTED: D. Gieseker, *Lectures on Moduli of Curves*, TIFR 69 (1982), Theorem 0.2.3 and Propositions 1.0.2--1.0.8, printed pp.27--62, for the projection, jet, Clifford and subcurve-flag details. The original text's online transcription was consulted to identify the explicit coefficients and selected-boundary hypothesis. The primary TIFR PDF endpoints did not return a usable PDF. The book's global setup uses the stronger d>=20(g-1); I have not invoked that theorem with the weaker hypothesis of this item. The statements delivered are agent formulations of the individual estimates in Morrison's ten-step route.

The proof is marked `proof_origin.by = agent`: Morrison omits most of the auxiliary estimates, the exact new formulations and the finite-index argument are written here, and the local archival PDFs are missing. The new numerical statements remain unsplit; this delivery does not pretend that their source references are proofs.

## Corrections and source checks

The item's statement is unchanged. I completed its statement dependencies for the Hilbert-polynomial notion, closed embedding, hyperplane twist, normalized degree, cohomology, dimension and completed node model.

Morrison's Theorem 8 describes d>9(g-1) as equivalent to d/N<8/7. With N=d+1-g this arithmetic equivalence is false: the latter is equivalent to d>8(g-1). For example g=2,d=9 satisfies 9/8<8/7 but not d>9. The implication used by the item is valid. Step 1 uses d>9(g-1) to obtain d/r<9/8<8/7, and never uses the false equivalence. This is a source arithmetic typo, not a dispute of the item or a change to the unit route.

I have corrected the following easy-to-miss details in formulating the split: the uniform error must depend on an upper bound on the weights; rescaling a weighted flag precludes an absolute uniform error bound. The quadratic coefficient here is half Morrison's e_F. The tangent-line double-point estimate is 7/2 with total weight at most 3, not the coefficient 4 available when neither branch is a line. One must prove nonspeciality on the reduced curve before killing its finite-length nilradical. The degree from the Hilbert polynomial must be compared to normalized-component degrees even before reducedness is established. The balanced inequality must be proved for disconnected unions, and its upper bound comes from the complement.

## Search and duplicate audit

Before creating nodes I searched the whole DAG by Gieseker, potential stability, Hilbert--Mumford, Hilbert weight, projection weight, Clifford, rational normal, subcurve, finite support, and Stacks 0B3J. I ran blueprint_refs searches for potential stability, projection weight, ramification, Clifford, rational normal, Hilbert and subcurve. The Hilbert hits define Hilbert schemes/polynomials or treat finite point schemes; they do not give the new weight statements. The generic cohomology hits were read to avoid citing etale finite-support acyclicity for Zariski coherent modules. The existing ample-degree proof mentions 0B3J but its statement is only the ample/positive-degree equivalence.

The ancestor command returns None: this item descends through created prerequisites with a null imported ancestor. I retained its null blueprint ancestor and full supplied via chain, added the item to each new node's via chain, and filled each exact estimate's place. No blueprint node matches these statements in another form.

For each new node I ran two LeanFinder phrasings, Loogle, grep through msearch.py, and LeanSearch. All 35 requests succeeded and their complete outputs were read. Their query texts and results are recorded literally in the nodes and searches.jsonl; no unavailable service was called a negative result. The main item also received two new semantic phrasings, Loogle, grep and LeanSearch; I retained all prior item searches.

Weighted-homogeneous polynomials and power-series orders do not compute weights of quotient monomial bases. Elliptic Weierstrass formulas do not supply general curve singularity weight estimates. Clifford algebras and modular cusp forms do not supply the two curve-theoretic claims. Lagrange interpolation is not the node evaluation statement on an embedded reducible curve. The locally Artinian scheme criteria found for finite support lack both coherent generation and higher-cohomology assertions. Hence none is an exact match or a one-line specialization.

## Not duplicates

lem-sfb-coherent-zero-dimensional-support vs lem-trf-proper-integral-curve-ample-degree: the new node gives generation and cohomology vanishing for coherent sheaves with zero-dimensional support on any locally Noetherian scheme; the existing statement gives ampleness iff positive degree for a line on a proper integral curve. Its proof uses 0B3J, but its statement does not expose 0B3J.

lem-sfb-bounded-hilbert-weight-polynomials vs lem-sfb-hilbert-plucker-pgl-linearization: the latter provides the embedding and central descent, not a uniform estimate of minimum monomial-basis weights or the numerical test.

lem-sfb-subcurve-span-weight-bound vs lem-trf-nodal-subcurve-boundary: the existing statement identifies the reduced boundary and its branches; it contains no section filtration or leading weight.

lem-sfb-nodal-special-clifford-subcurve vs lem-sfb-nodal-log-canonical-reconstruction: the existing dualizing-degree/reconstruction statement contains neither Serre--Clifford support extraction nor the h0 bound.

lem-sfb-gieseker-component-interpolation vs lem-sfb-gieseker-potential-stability: interpolation bounds degree by the number of node evaluations on a single normalized component. It does not state nodality, reduction, nonspeciality or the balanced inequality; it is Morrison step (9), an intermediate prerequisite that the proof uses before the actual subcurve-weight computation.

The delivery gate also matches `0810` inside the Morrison arXiv filename as a tag. I opened all eleven flagged existing statements; the following comparisons cover that entire mechanically reported set. The two affine-algebra nodes actually use Stacks 0810, whereas the numerical-curve source contains arXiv:0810.2340.

lem-sfb-bounded-hilbert-weight-polynomials vs lem-sfb-gieseker-potential-stability: the new statement gives uniform bounded-weight minimum monomial-basis estimates and their numerical semistability test; the existing statement gives reducedness, nodality, completeness, nonspeciality and balance for Hilbert-semistable curves; it does not state these intermediate estimates.

lem-sfb-bounded-hilbert-weight-polynomials vs lem-sfb-gieseker-ten-canonical-hilbert-stability: the new statement gives uniform bounded-weight minimum monomial-basis estimates and their numerical semistability test; the existing statement gives stability and closedness of the ten-canonical stable-curve locus, rather than these intermediate estimates.

lem-sfb-bounded-hilbert-weight-polynomials vs lem-sfb-git-orbit-closure-dimension: the new statement gives uniform bounded-weight minimum monomial-basis estimates and their numerical semistability test; the existing statement gives dimensions and unique closed orbits in a semistable orbit closure, without section-filtration estimates.

lem-sfb-bounded-hilbert-weight-polynomials vs lem-sfb-nodal-trait-twister-extremal-degree: the new statement gives uniform bounded-weight minimum monomial-basis estimates and their numerical semistability test; the existing statement gives an extremal degree for a generically trivial line on a nodal DVR family, without Hilbert-weight or Clifford estimates.

lem-sfb-bounded-hilbert-weight-polynomials vs lem-sfb-projective-git-semistable-replacement: the new statement gives uniform bounded-weight minimum monomial-basis estimates and their numerical semistability test; the existing statement gives extension of a semistable generic point after a finite DVR extension and coordinate change, without these estimates.

lem-sfb-bounded-hilbert-weight-polynomials vs lem-sfb-projective-pgl-stable-quotient: the new statement gives uniform bounded-weight minimum monomial-basis estimates and their numerical semistability test; the existing statement gives the projective quotient of a closed stable locus by PGL, without these intermediate estimates.

lem-sfb-bounded-hilbert-weight-polynomials vs lem-sfb-smooth-curve-high-degree-hilbert-stability: the new statement gives uniform bounded-weight minimum monomial-basis estimates and their numerical semistability test; the existing statement gives Hilbert stability of complete high-degree smooth-curve embeddings, without these intermediate estimates for possibly singular schemes.

lem-sfb-bounded-hilbert-weight-polynomials vs lem-sfb-ten-canonical-hilbert-parameter: the new statement gives uniform bounded-weight minimum monomial-basis estimates and their numerical semistability test; the existing statement gives the Hilbert parameter scheme and projective frames of ten-canonical stable curves, without these estimates.

lem-sfb-bounded-hilbert-weight-polynomials vs lem-trf-affine-generic-localization-intersection: the new statement gives uniform bounded-weight minimum monomial-basis estimates and their numerical semistability test; the existing statement gives injectivity of a flat finitely presented algebra into its generic-point localizations, unrelated to these projective curve estimates.

lem-sfb-bounded-hilbert-weight-polynomials vs lem-trf-affine-generic-rank-blowup: the new statement gives uniform bounded-weight minimum monomial-basis estimates and their numerical semistability test; the existing statement gives generic-rank flattening after blowup charts of an affine algebra, unrelated to these projective curve estimates.

lem-sfb-component-projection-weight-bounds vs lem-sfb-gieseker-potential-stability: the new statement gives explicit projection-flag leading coefficients for multiple or low-degree non-rational-normal components; the existing statement gives reducedness, nodality, completeness, nonspeciality and balance for Hilbert-semistable curves; it does not state these intermediate estimates.

lem-sfb-component-projection-weight-bounds vs lem-sfb-gieseker-ten-canonical-hilbert-stability: the new statement gives explicit projection-flag leading coefficients for multiple or low-degree non-rational-normal components; the existing statement gives stability and closedness of the ten-canonical stable-curve locus, rather than these intermediate estimates.

lem-sfb-component-projection-weight-bounds vs lem-sfb-git-orbit-closure-dimension: the new statement gives explicit projection-flag leading coefficients for multiple or low-degree non-rational-normal components; the existing statement gives dimensions and unique closed orbits in a semistable orbit closure, without section-filtration estimates.

lem-sfb-component-projection-weight-bounds vs lem-sfb-hilbert-plucker-pgl-linearization: the new statement gives explicit projection-flag leading coefficients for multiple or low-degree non-rational-normal components; the existing statement gives uniform Hilbert embeddings and descent of the Pluecker linearization to PGL, without these intermediate estimates.

lem-sfb-component-projection-weight-bounds vs lem-sfb-nodal-trait-twister-extremal-degree: the new statement gives explicit projection-flag leading coefficients for multiple or low-degree non-rational-normal components; the existing statement gives an extremal degree for a generically trivial line on a nodal DVR family, without Hilbert-weight or Clifford estimates.

lem-sfb-component-projection-weight-bounds vs lem-sfb-projective-git-semistable-replacement: the new statement gives explicit projection-flag leading coefficients for multiple or low-degree non-rational-normal components; the existing statement gives extension of a semistable generic point after a finite DVR extension and coordinate change, without these estimates.

lem-sfb-component-projection-weight-bounds vs lem-sfb-projective-pgl-stable-quotient: the new statement gives explicit projection-flag leading coefficients for multiple or low-degree non-rational-normal components; the existing statement gives the projective quotient of a closed stable locus by PGL, without these intermediate estimates.

lem-sfb-component-projection-weight-bounds vs lem-sfb-smooth-curve-high-degree-hilbert-stability: the new statement gives explicit projection-flag leading coefficients for multiple or low-degree non-rational-normal components; the existing statement gives Hilbert stability of complete high-degree smooth-curve embeddings, without these intermediate estimates for possibly singular schemes.

lem-sfb-component-projection-weight-bounds vs lem-sfb-ten-canonical-hilbert-parameter: the new statement gives explicit projection-flag leading coefficients for multiple or low-degree non-rational-normal components; the existing statement gives the Hilbert parameter scheme and projective frames of ten-canonical stable curves, without these estimates.

lem-sfb-component-projection-weight-bounds vs lem-trf-affine-generic-localization-intersection: the new statement gives explicit projection-flag leading coefficients for multiple or low-degree non-rational-normal components; the existing statement gives injectivity of a flat finitely presented algebra into its generic-point localizations, unrelated to these projective curve estimates.

lem-sfb-component-projection-weight-bounds vs lem-trf-affine-generic-rank-blowup: the new statement gives explicit projection-flag leading coefficients for multiple or low-degree non-rational-normal components; the existing statement gives generic-rank flattening after blowup charts of an affine algebra, unrelated to these projective curve estimates.

lem-sfb-singular-point-jet-weight-bounds vs lem-sfb-gieseker-potential-stability: the new statement gives explicit jet-flag leading coefficients for triple, ramified and tangent-double points; the existing statement gives reducedness, nodality, completeness, nonspeciality and balance for Hilbert-semistable curves; it does not state these intermediate estimates.

lem-sfb-singular-point-jet-weight-bounds vs lem-sfb-gieseker-ten-canonical-hilbert-stability: the new statement gives explicit jet-flag leading coefficients for triple, ramified and tangent-double points; the existing statement gives stability and closedness of the ten-canonical stable-curve locus, rather than these intermediate estimates.

lem-sfb-singular-point-jet-weight-bounds vs lem-sfb-git-orbit-closure-dimension: the new statement gives explicit jet-flag leading coefficients for triple, ramified and tangent-double points; the existing statement gives dimensions and unique closed orbits in a semistable orbit closure, without section-filtration estimates.

lem-sfb-singular-point-jet-weight-bounds vs lem-sfb-hilbert-plucker-pgl-linearization: the new statement gives explicit jet-flag leading coefficients for triple, ramified and tangent-double points; the existing statement gives uniform Hilbert embeddings and descent of the Pluecker linearization to PGL, without these intermediate estimates.

lem-sfb-singular-point-jet-weight-bounds vs lem-sfb-nodal-trait-twister-extremal-degree: the new statement gives explicit jet-flag leading coefficients for triple, ramified and tangent-double points; the existing statement gives an extremal degree for a generically trivial line on a nodal DVR family, without Hilbert-weight or Clifford estimates.

lem-sfb-singular-point-jet-weight-bounds vs lem-sfb-projective-git-semistable-replacement: the new statement gives explicit jet-flag leading coefficients for triple, ramified and tangent-double points; the existing statement gives extension of a semistable generic point after a finite DVR extension and coordinate change, without these estimates.

lem-sfb-singular-point-jet-weight-bounds vs lem-sfb-projective-pgl-stable-quotient: the new statement gives explicit jet-flag leading coefficients for triple, ramified and tangent-double points; the existing statement gives the projective quotient of a closed stable locus by PGL, without these intermediate estimates.

lem-sfb-singular-point-jet-weight-bounds vs lem-sfb-smooth-curve-high-degree-hilbert-stability: the new statement gives explicit jet-flag leading coefficients for triple, ramified and tangent-double points; the existing statement gives Hilbert stability of complete high-degree smooth-curve embeddings, without these intermediate estimates for possibly singular schemes.

lem-sfb-singular-point-jet-weight-bounds vs lem-sfb-ten-canonical-hilbert-parameter: the new statement gives explicit jet-flag leading coefficients for triple, ramified and tangent-double points; the existing statement gives the Hilbert parameter scheme and projective frames of ten-canonical stable curves, without these estimates.

lem-sfb-singular-point-jet-weight-bounds vs lem-trf-affine-generic-localization-intersection: the new statement gives explicit jet-flag leading coefficients for triple, ramified and tangent-double points; the existing statement gives injectivity of a flat finitely presented algebra into its generic-point localizations, unrelated to these projective curve estimates.

lem-sfb-singular-point-jet-weight-bounds vs lem-trf-affine-generic-rank-blowup: the new statement gives explicit jet-flag leading coefficients for triple, ramified and tangent-double points; the existing statement gives generic-rank flattening after blowup charts of an affine algebra, unrelated to these projective curve estimates.

lem-sfb-subcurve-span-weight-bound vs lem-sfb-gieseker-potential-stability: the new statement gives selected-boundary section-filtration leading weight estimates, permitting disconnected subcurves; the existing statement gives reducedness, nodality, completeness, nonspeciality and balance for Hilbert-semistable curves; it does not state these intermediate estimates.

lem-sfb-subcurve-span-weight-bound vs lem-sfb-gieseker-ten-canonical-hilbert-stability: the new statement gives selected-boundary section-filtration leading weight estimates, permitting disconnected subcurves; the existing statement gives stability and closedness of the ten-canonical stable-curve locus, rather than these intermediate estimates.

lem-sfb-subcurve-span-weight-bound vs lem-sfb-git-orbit-closure-dimension: the new statement gives selected-boundary section-filtration leading weight estimates, permitting disconnected subcurves; the existing statement gives dimensions and unique closed orbits in a semistable orbit closure, without section-filtration estimates.

lem-sfb-subcurve-span-weight-bound vs lem-sfb-hilbert-plucker-pgl-linearization: the new statement gives selected-boundary section-filtration leading weight estimates, permitting disconnected subcurves; the existing statement gives uniform Hilbert embeddings and descent of the Pluecker linearization to PGL, without these intermediate estimates.

lem-sfb-subcurve-span-weight-bound vs lem-sfb-nodal-trait-twister-extremal-degree: the new statement gives selected-boundary section-filtration leading weight estimates, permitting disconnected subcurves; the existing statement gives an extremal degree for a generically trivial line on a nodal DVR family, without Hilbert-weight or Clifford estimates.

lem-sfb-subcurve-span-weight-bound vs lem-sfb-projective-git-semistable-replacement: the new statement gives selected-boundary section-filtration leading weight estimates, permitting disconnected subcurves; the existing statement gives extension of a semistable generic point after a finite DVR extension and coordinate change, without these estimates.

lem-sfb-subcurve-span-weight-bound vs lem-sfb-projective-pgl-stable-quotient: the new statement gives selected-boundary section-filtration leading weight estimates, permitting disconnected subcurves; the existing statement gives the projective quotient of a closed stable locus by PGL, without these intermediate estimates.

lem-sfb-subcurve-span-weight-bound vs lem-sfb-smooth-curve-high-degree-hilbert-stability: the new statement gives selected-boundary section-filtration leading weight estimates, permitting disconnected subcurves; the existing statement gives Hilbert stability of complete high-degree smooth-curve embeddings, without these intermediate estimates for possibly singular schemes.

lem-sfb-subcurve-span-weight-bound vs lem-sfb-ten-canonical-hilbert-parameter: the new statement gives selected-boundary section-filtration leading weight estimates, permitting disconnected subcurves; the existing statement gives the Hilbert parameter scheme and projective frames of ten-canonical stable curves, without these estimates.

lem-sfb-subcurve-span-weight-bound vs lem-trf-affine-generic-localization-intersection: the new statement gives selected-boundary section-filtration leading weight estimates, permitting disconnected subcurves; the existing statement gives injectivity of a flat finitely presented algebra into its generic-point localizations, unrelated to these projective curve estimates.

lem-sfb-subcurve-span-weight-bound vs lem-trf-affine-generic-rank-blowup: the new statement gives selected-boundary section-filtration leading weight estimates, permitting disconnected subcurves; the existing statement gives generic-rank flattening after blowup charts of an affine algebra, unrelated to these projective curve estimates.

lem-sfb-nodal-special-clifford-subcurve vs lem-sfb-gieseker-potential-stability: the new statement gives a connected Clifford support subcurve for a special very ample line, without semistability assumptions; the existing statement gives reducedness, nodality, completeness, nonspeciality and balance for Hilbert-semistable curves; it does not state these intermediate estimates.

lem-sfb-nodal-special-clifford-subcurve vs lem-sfb-gieseker-ten-canonical-hilbert-stability: the new statement gives a connected Clifford support subcurve for a special very ample line, without semistability assumptions; the existing statement gives stability and closedness of the ten-canonical stable-curve locus, rather than these intermediate estimates.

lem-sfb-nodal-special-clifford-subcurve vs lem-sfb-git-orbit-closure-dimension: the new statement gives a connected Clifford support subcurve for a special very ample line, without semistability assumptions; the existing statement gives dimensions and unique closed orbits in a semistable orbit closure, without section-filtration estimates.

lem-sfb-nodal-special-clifford-subcurve vs lem-sfb-hilbert-plucker-pgl-linearization: the new statement gives a connected Clifford support subcurve for a special very ample line, without semistability assumptions; the existing statement gives uniform Hilbert embeddings and descent of the Pluecker linearization to PGL, without these intermediate estimates.

lem-sfb-nodal-special-clifford-subcurve vs lem-sfb-nodal-trait-twister-extremal-degree: the new statement gives a connected Clifford support subcurve for a special very ample line, without semistability assumptions; the existing statement gives an extremal degree for a generically trivial line on a nodal DVR family, without Hilbert-weight or Clifford estimates.

lem-sfb-nodal-special-clifford-subcurve vs lem-sfb-projective-git-semistable-replacement: the new statement gives a connected Clifford support subcurve for a special very ample line, without semistability assumptions; the existing statement gives extension of a semistable generic point after a finite DVR extension and coordinate change, without these estimates.

lem-sfb-nodal-special-clifford-subcurve vs lem-sfb-projective-pgl-stable-quotient: the new statement gives a connected Clifford support subcurve for a special very ample line, without semistability assumptions; the existing statement gives the projective quotient of a closed stable locus by PGL, without these intermediate estimates.

lem-sfb-nodal-special-clifford-subcurve vs lem-sfb-smooth-curve-high-degree-hilbert-stability: the new statement gives a connected Clifford support subcurve for a special very ample line, without semistability assumptions; the existing statement gives Hilbert stability of complete high-degree smooth-curve embeddings, without these intermediate estimates for possibly singular schemes.

lem-sfb-nodal-special-clifford-subcurve vs lem-sfb-ten-canonical-hilbert-parameter: the new statement gives a connected Clifford support subcurve for a special very ample line, without semistability assumptions; the existing statement gives the Hilbert parameter scheme and projective frames of ten-canonical stable curves, without these estimates.

lem-sfb-nodal-special-clifford-subcurve vs lem-trf-affine-generic-localization-intersection: the new statement gives a connected Clifford support subcurve for a special very ample line, without semistability assumptions; the existing statement gives injectivity of a flat finitely presented algebra into its generic-point localizations, unrelated to these projective curve estimates.

lem-sfb-nodal-special-clifford-subcurve vs lem-trf-affine-generic-rank-blowup: the new statement gives a connected Clifford support subcurve for a special very ample line, without semistability assumptions; the existing statement gives generic-rank flattening after blowup charts of an affine algebra, unrelated to these projective curve estimates.

lem-sfb-gieseker-component-interpolation vs lem-sfb-gieseker-ten-canonical-hilbert-stability: the new statement gives degree versus boundary-node interpolation on normalized complementary components under numerical flag inequalities; the existing statement gives stability and closedness of the ten-canonical stable-curve locus, rather than these intermediate estimates.

lem-sfb-gieseker-component-interpolation vs lem-sfb-git-orbit-closure-dimension: the new statement gives degree versus boundary-node interpolation on normalized complementary components under numerical flag inequalities; the existing statement gives dimensions and unique closed orbits in a semistable orbit closure, without section-filtration estimates.

lem-sfb-gieseker-component-interpolation vs lem-sfb-hilbert-plucker-pgl-linearization: the new statement gives degree versus boundary-node interpolation on normalized complementary components under numerical flag inequalities; the existing statement gives uniform Hilbert embeddings and descent of the Pluecker linearization to PGL, without these intermediate estimates.

lem-sfb-gieseker-component-interpolation vs lem-sfb-nodal-trait-twister-extremal-degree: the new statement gives degree versus boundary-node interpolation on normalized complementary components under numerical flag inequalities; the existing statement gives an extremal degree for a generically trivial line on a nodal DVR family, without Hilbert-weight or Clifford estimates.

lem-sfb-gieseker-component-interpolation vs lem-sfb-projective-git-semistable-replacement: the new statement gives degree versus boundary-node interpolation on normalized complementary components under numerical flag inequalities; the existing statement gives extension of a semistable generic point after a finite DVR extension and coordinate change, without these estimates.

lem-sfb-gieseker-component-interpolation vs lem-sfb-projective-pgl-stable-quotient: the new statement gives degree versus boundary-node interpolation on normalized complementary components under numerical flag inequalities; the existing statement gives the projective quotient of a closed stable locus by PGL, without these intermediate estimates.

lem-sfb-gieseker-component-interpolation vs lem-sfb-smooth-curve-high-degree-hilbert-stability: the new statement gives degree versus boundary-node interpolation on normalized complementary components under numerical flag inequalities; the existing statement gives Hilbert stability of complete high-degree smooth-curve embeddings, without these intermediate estimates for possibly singular schemes.

lem-sfb-gieseker-component-interpolation vs lem-sfb-ten-canonical-hilbert-parameter: the new statement gives degree versus boundary-node interpolation on normalized complementary components under numerical flag inequalities; the existing statement gives the Hilbert parameter scheme and projective frames of ten-canonical stable curves, without these estimates.

lem-sfb-gieseker-component-interpolation vs lem-trf-affine-generic-localization-intersection: the new statement gives degree versus boundary-node interpolation on normalized complementary components under numerical flag inequalities; the existing statement gives injectivity of a flat finitely presented algebra into its generic-point localizations, unrelated to these projective curve estimates.

lem-sfb-gieseker-component-interpolation vs lem-trf-affine-generic-rank-blowup: the new statement gives degree versus boundary-node interpolation on normalized complementary components under numerical flag inequalities; the existing statement gives generic-rank flattening after blowup charts of an affine algebra, unrelated to these projective curve estimates.

## Review by Q92

I read the chapter and unit and the item's ancestor chain. This is a node-level prerequisite of the existing Gieseker ten-canonical construction, not the key statement of its constructibility unit; no unit realization fields are changed. The route is Morrison's ten-step potential-stability proof. The scheme/cohomology inputs filed in other units are generic tools and are declared in split_report.tool_uses.

For the item I read Morrison Definition 7, Theorem 8 and its ten proof steps, together with Proposition 1, Lemma 2 and equation (6). For the new bounded-weight node I checked the numerical criterion and the uniform-error statement in Section 2.1 and corrected its dependence on the bound B. For the component node I compared Morrison (2)--(3) with the explicit 2e+1/2 projection coefficient in Gieseker's 1.0.3. For the jet node I read Morrison's cusp calculation and the two tangent cases, and checked the matching 4 and 7/2 coefficients in the original Gieseker calculation. For the span node I checked the selected-boundary hypothesis in Gieseker 1.0.7 and Morrison (9)--(10); I wrote out why the rational-normal exception contributes e>=b/2. For the special-line node I checked the support-of-a-dualizing-section and Clifford argument used in Gieseker 1.0.8 and Morrison (7). For interpolation I checked the exact component/node assertion of Morrison (9), keeping this as an unsplit statement. For the zero-support node I read the local `coherent.tex` statement and proof, label lemma-coherent-support-dimension-0, Tag 0B3J, in full.

I checked each item step against the statements it cites, rather than using a construction hidden in their proofs:

1. Bounded Hilbert weights supplies both the error and the semistability inequality; the PGL-line node supplies the matching linearization and uniform Hilbert index. Half-integrality gives a gap of 1/(2r), and c=1-g is negative, so M>2rA works in every field.
2. The weight node supplies dimension one. The finite-type/Noetherian and finite-components statements give precisely those properties. The flat projective Hilbert-polynomial node over Spec k supplies the Euler polynomial for all twists. I excluded zero-dimensional components by connectedness explicitly.
3. The elementary nilpotent-generator argument gives a fixed exponent for this C, which is enough to take its leading coefficient. It does not claim this exponent is field-uniform. The weight node defines that coefficient and the limits being used.
4. The two projection estimates give the displayed coefficients and sums, not semistability conclusions. I checked the positive gaps at e=1 and at e=3. I added the existing multiplicity-weighted degree formula, normalization theorem and degree-one pullback formula to identify total normalized degree with d. The normalization source is finite birational, so the pullback lemma's degree is one.
5. The jet lemma gives all three exact pairs of coefficient/total-weight bounds. Low-degree and generic reducedness were established first. The weaker tangent-line coefficient still contradicts 3t<7/2. This is the point where cusp and tangency estimates would fail for low-canonical embeddings.
6. The Clifford node supplies an actual connected support subcurve and its h0 bound, not merely a dualizing line. The span node can be used with just ONE selected boundary branch: the ample-degree criterion gives its normalized degree at least one. For Y=D the nondegeneracy dimension bound is used instead, avoiding a nonexistent boundary. The smallest degree e=2 still gives a strict gap.
7. Finite support of the coherent nilradical follows after generic reducedness. The 0B3J node supplies acyclicity and global generation of the actual module N tensor L. The affine-cohomology statement applies to the closed immersion D to C and identifies its cohomology; the dimension-vanishing statement applies to a Noetherian scheme of dimension one, with no smoothness assumption.
8. I used the same exact sequence and the injective restriction to D to get zero sections of N tensor L; 0B3J then forces the sheaf itself to vanish. This is an elementary dimension argument, not a new lemma or a premise hidden in a definition.
9. The nodal-boundary node says the scheme intersection is a reduced finite set and each side has a smooth branch there. Component interpolation supplies exactly the capacity or rational-normal alternative needed by the span node. The rational-normal exception has b>=2 because its degree is positive. The span node explicitly permits disconnected Y.
10. Restriction is a surjection of coherent modules; the kernel has H2=0 by the dimension-vanishing node. The affine-cohomology node again identifies cohomology for the closed immersion. Thus the global nonspeciality really descends to every subcurve.
11. The normalization-quotient node supplies the coherent exact sequence and one fibre per internal node. Locally trivial tensoring identifies its twist and the pushforward of the normalized line. Euler additivity and the affine comparison give the degree/Euler identity; the degree definition is applied only on smooth normalized components. The argument is applied separately on connected components, because the quotient node assumes connectedness.
12. The normalization Euler node and the unmarked dualizing component formula provide the two exact sums used. Internal nodes contribute two branches and boundary nodes one. I verified the dualizing-family hypotheses over the field and counted self-nodes correctly.
13--14. The conversion from the span inequality to the lower bound, and then application to the complement for the upper bound, are written-out arithmetic with positive denominator g-1. Both degree sums are justified earlier. No connectedness of Y or its complement is assumed.
15. The ample-degree node gives positive INTEGRAL hyperplane degrees. The dualizing formula counts ALL branches, including self-nodes. A genus-zero normalized component with at most one branch cannot have a self-node, so the balanced inequality excludes it. In the irreducible case the total Euler formula gives 2g branches. On a smooth rational two-boundary component the dualizing degree is zero, whence positive degree at most one means exactly one.

I tested all new statements on the empty-support case, zero sheaf, rational normal components, an exceptional line with two attachments, a smooth curve (no boundary), a cusp, a tangent-line double point and disconnected subcurves. The projection assumptions exclude the meaningless whole small-degree-component case. Nonreduced structures supported only at points are retained until the cohomological dimension argument eliminates them. In characteristic two the node model and distinct normalized branches are still the stated split model; none of the weight computations divides by the characteristic or uses differentials to conclude that a cusp is a node. I reviewed all step lengths: every step is under 2000 characters, and no lemma is concealed in a long step. No forbidden SGA source occurs.

## Unfinished work

Only the deliberately statement-only prerequisites remain unsplit. They need their own later stage-1 work, as the one-level contract requires. The item proof itself has no omitted implication. This report is the author's self-review, not an independent review.
