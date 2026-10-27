# Q117 stage-1 delivery

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-syntomic-polynomial-fibre-cut.json: the item, now split into seven proof steps; statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-polynomial-zero-section-dimension.json: one statement-only prerequisite, unsplit, no exact Mathlib match. Its result concerns topological dimension at a specified point, not the dimension of a local ring.
- citations.json: full verbatim statement quotations for every cited node in every item step.
- searches.jsonl: actual msearch.py results, retained without alteration.

## Attachments

None. I searched WeilConjectures for the item tag, syntomic, polynomial fibres, syntomic quotients and coordinate cuts. The existing SyntomicPolynomialFibreComparison declaration compares a presented fibre with a quotient and is not this cutting statement. No declaration found gives every clause of the item. No Lean was written or compiled.

## Literature wanted

None. The sources used are present locally.

## Findings and changes

The item had no proof. Stacks smoothing.tex Tag 07M8 (proposition-lift-smooth), proof of (1), says to pass locally to a relative global complete intersection and append the coordinate equations before invoking 00ST. I made the missing dimension comparison explicit. In general the dimensions of different connected pieces need not agree, so I use the pointwise version 00ST(3), not an unjustified globally constant equation count over R/I. The initial statement is faithful and requires no correction.

The newest blueprint was read at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, clause (3). The unit and chapter records and the inherited long auxiliary-source route were read. blueprint_refs.py ancestor prints None for this item, and the new node inherits that computed null ancestor with the item prepended to via. Whole-blueprint searches for syntomic, polynomial, polynomial dimension, dimension polynomial, zero section, dimension at a point, 00OT, 00SY and 00ST found no existing blueprint statement of the new result. Whole-DAG concept/tag searches were also read. No chapter/unit file is changed.

The off-unit citations declared in split_report.tool_uses are generic local commutative algebra and topological tools. In particular 00SY supplies the local presentation, 00ST(3) supplies the localized appended presentation, and 00SO supplies gluing. They implement the given source route rather than replace a unit step.

## Review by Q117

I read smoothing.tex, Tag 07M8, from the construction of D through the final claim and its proof, together with algebra.tex Tags 00SY (lemma-syntomic), 00ST (lemma-localize-relative-complete-intersection), and 00SW (lemma-relative-global-complete-intersection). I checked that 00SY permits an arbitrary base ring and gives an actual finite polynomial quotient chart, and that 00ST(3) uses topological fibre dimension at the specified point. I did not infer flatness of the cut algebra just from flatness of its reduction.

For step 1, the two definition nodes say precisely what a finite polynomial presentation and polynomial ring are. Killing the lifted coordinates appends finitely many equations. The quotient identity A/IA=A0 is evaluation at zero, with an explicit inverse, so it does not require flat reduction.

For step 2, I opened the statements of lem-weil-pbc-flat-local-ring-maps and lem-weil-pbc-syntomic-at-prime-relative-global-complete-intersection. The former supplies exactly local flatness, and the latter requires finite presentation near the point, local flatness, and a principal global-CI neighbourhood of the fibre prime. All three are supplied respectively by syntomicity and by the principal-cover definition in def-weil-pbc-complete-intersection-over-field. The prime in D is the inverse image of the A prime and therefore contains the t_i and I.

For step 3, I read each cited statement: fibre-ring-primes-bijection supplies the actual fibre prime; relative-global-complete-intersection-base-change supplies the specified fibre presentation and its dimension; global-complete-intersection-equidimensional gives dimension at that fibre point. Algebra-localization-away-base-change identifies the localized fibre, and spec-localization-away-basic-open and dimension-at-point-open-subspace permit passage back to the surrounding polynomial fibre. The new zero-section lemma applies to B=A0 tensor kappa(p), a finite type algebra because A0 is finitely presented. I checked that p contains I, so its residue field is an R/I-algebra, and that the polynomial prime is exactly (q_B,x_1,...,x_r). Thus its dimension is the base-point dimension plus r, with no equidimensionality assumption on A0.

For step 4, I read equation-count-localize-relative-global-complete-intersection: its hypothesis is precisely the computed dimension N-(c+r) of the specified presentation at the point, and its conclusion is a relative global CI localization missing that prime. The same localization and open-subspace nodes justify using B localized at u. Nonnegativity of the computed dimension ensures N>=c+r; no natural-number truncated subtraction is used. For step 5, I wrote the fraction v=b/u^e and the two inverse localization maps' unit criterion; this is elementary localization arithmetic, not an uncited descent theorem.

For step 6, spec-zero-loci-disjoint-unit-ideal states exactly that disjoint V(J) and V(IA) give a+i=1 with a in J. This is the reason a is 1 on the reduction, rather than merely a unit there. Membership in J yields a finite expression without any Noetherian or quasi-compactness assumption. For step 7, relative-global-complete-intersection-principal-localization gives the appended inverse-variable presentation after restricting each chart to A_a. Relative-ci-principal-cover-syntomic-gluing states all three syntomic clauses, and its finite unit relation is exactly sum (h_j/a)b_j=1. It explicitly permits the empty cover and zero ring. The proof does not cite a mere definition for these gluing or flatness facts.

For the new node I read algebra.tex Tag 00OT (lemma-dimension-at-a-point-finite-type-over-field) and Tag 00P0 (lemma-dimension-prime-polynomial-ring), including their proofs. The intended later proof uses that the minimal primes of B[x] are pB[x] for minimal p of B. They pass through (q,x) exactly when p is contained in q. Each component has dimension dim(B/p)+r, since its fraction field is Frac(B/p)(x_1,...,x_r); taking the maximum over these components proves the claimed formula. This is a separate non-elementary dimension lemma, not a clause of the syntomic lifting assertion, and is deliberately left statement-only. The existing component formula node alone does not include the polynomial component comparison.

I tested the new statement for r=0 (the identity), B=0 (no prime), a field B (the origin of affine r-space), a nonreduced B such as k[e]/(e^2), and components of different dimensions. The component formula gives the correct maximum through q in every case. For the item, r=0 uses the empty coordinate quotient; A0=0 gives V(IA) empty and a=0, hence the zero localization; I=0 gives the polynomial algebra itself and its coordinate quotient. The argument also permits I=R. No nilpotent-ideal assumption was introduced. Every proof step is below 2000 characters; the only standalone dimension sublemma was extracted. I checked B1--B10, C1--C8, D1--D5 and E1--E7 against the files: no new proof is hidden in a statement, no duplicate or restated item clause is introduced, every non-elementary input is cited, and citations.json quotes the actual cited statements.

Mathlib searches returned global polynomial dimension theorems, smooth/etale presentations, and localization facts. I read Mathlib/RingTheory/KrullDimension/Polynomial.lean, including MvPolynomial.ringKrullDim_of_isNoetherianRing, lines 119--133: it computes global ring dimension and does not state dimension at a chosen zero-section point. It is a candidate ingredient, not a one-line match to the new statement. Two semantic phrasings and the Loogle pattern were checked; no exact result appeared. Searches for the item's syntomic assertion likewise gave only smooth/etale and quotient/localization ingredients.

## Not duplicates
- lem-sfb-polynomial-zero-section-dimension vs lem-sbc-nowhere-dense-closed-fibre-dimension: the existing node concerns strict dimension decrease along a nowhere dense closed fibre, rather than equality of polynomial zero-section and base-point dimensions.
- lem-sfb-polynomial-zero-section-dimension vs lem-trf-field-generators-affine-model: the existing node concerns field generators or residue transcendence degree, not the polynomial zero-section dimension formula.
- lem-sfb-polynomial-zero-section-dimension vs lem-trf-closed-point-affine-dimension-data: the existing node concerns a closed point or an integral affine neighbourhood; q in the new lemma can be any prime and B need not be integral.
- lem-sfb-polynomial-zero-section-dimension vs lem-trf-flat-local-component-dimension-difference: the existing node is a component/transcendence formula for flat local essentially finite type maps; the new statement is a topological dimension formula at zero-section points of polynomial affine space.
- lem-sfb-polynomial-zero-section-dimension vs lem-per-constructible-subset-closure-dimension: the existing node compares a constructible subset with its closure; it has no polynomial dimension comparison.
- lem-sfb-polynomial-zero-section-dimension vs lem-weil-pbc-standard-smooth-over-field-dimension-at-points: the existing node computes dimension for a standard smooth algebra over a field; B in the new lemma can be singular, nonreduced and not equidimensional.
- lem-sfb-polynomial-zero-section-dimension vs lem-weil-pbc-finite-type-domain-dimension-trdeg: the existing node relates global domain dimension to transcendence degree; the new statement concerns local topological dimension for arbitrary finite type B at a specified zero-section point.
- lem-sfb-polynomial-zero-section-dimension vs lem-weil-pbc-global-complete-intersection-equidimensional-lower-bound: the existing node assumes a global complete intersection and controls its dimension; the new lemma assumes only finite type and compares a polynomial zero-section point to the base point.
- lem-sfb-polynomial-zero-section-dimension vs lem-weil-pbc-global-complete-intersection-equidimensional: the existing node assumes a global complete intersection and controls its dimension; the new lemma assumes only finite type and compares a polynomial zero-section point to the base point.
- lem-sfb-polynomial-zero-section-dimension vs lem-weil-pbc-lci-conormal-free-rank-codimension: the existing node computes conormal rank under lci hypotheses; the new node assumes no lci hypothesis and compares topological dimensions of polynomial and base points.
- lem-sfb-polynomial-zero-section-dimension vs lem-weil-pbc-dimension-at-point-components: the existing node compares dimension at a point with component dimensions; it does not identify polynomial components or their dimensions at a zero-section point.
- lem-sfb-polynomial-zero-section-dimension vs lem-weil-pbc-minimal-component-dimension-maximum: the existing node compares dimension at a point with component dimensions; it does not identify polynomial components or their dimensions at a zero-section point.
- lem-sfb-polynomial-zero-section-dimension vs lem-weil-pbc-closed-point-dimension-local-ring: the existing node concerns a closed point or an integral affine neighbourhood; q in the new lemma can be any prime and B need not be integral.
- lem-sfb-polynomial-zero-section-dimension vs lem-kun-finite-type-residue-trdeg: the existing node concerns field generators or residue transcendence degree, not the polynomial zero-section dimension formula.

## Unfinished work

The single new dimension lemma is statement-only as required and joins the stage-1 queue. No unfinished argument remains inside the item beyond its explicit cited prerequisites.
