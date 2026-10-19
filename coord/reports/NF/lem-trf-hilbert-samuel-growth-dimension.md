## Files written

- `dag/nodes/sec-trace-formula/lem-trf-hilbert-samuel-growth-dimension.json`: item, statement unchanged, seven proof steps, status split.
- `dag/nodes/sec-trace-formula/lem-trf-standard-graded-hilbert-function.json`: new statement, unsplit; no exact or one-line Mathlib match. This is the graded-module input of Stacks 00K1, not a local dimension theorem.
- `citations.json`: full verbatim statements for every node used in every item step.
- `searches.jsonl`: actual search-command records, retained with the delivery.

One new node, zero new Mathlib leaves. No Lean, compiler, Lake, or library build was run. No shared repository or launcher file was modified; the required delivery tool alone packages its own commit.

## Attachments

None. Searches of WeilConjectures by item tag, Hilbert--Samuel, Hilbert function/polynomial, hilbertPoly and the graded-algebra source found no declaration stating the item or the new graded-module theorem. The proper-scheme Euler-characteristic theorems in AlgebraicGeometry/Modules/Ample.lean and HilbertPolynomial.lean do not give the homogeneous dimensions of an arbitrary finite graded module without an additional comparison theorem. They are not attachments for these statements.

## Wanted

None. All mathematical sources used are present in `literature/stacks-project/algebra.tex`.

## Findings and corrections

The imported item had no proof. Its statement is correct, including nonzero, the exponent n rather than n+1, and the degree-zero case. There is no STATEMENT-DISPUTED finding and no statement change.

Read Stacks 00K8 (`proposition-hilbert-function-polynomial`) and 00KQ (`proposition-dimension`) in full, the local Hilbert-function definitions immediately before 00K8, 00K1 (`proposition-graded-hilbert-polynomial`) and its preceding finite-generation lemma, 00JZ (`lemma-numerical-polynomial`), Example `example-K0-field`, and 00IN as stated in the existing Artin--Rees node. Rather than create a polynomial-existence node or a degree-equals-dimension node that merely restates a clause, the item constructs the associated graded algebra, sums its polynomial, and proves both degree inequalities. The prime-chain argument uses a direct Artin--Rees estimate instead of introducing the more elaborate 00KC Hilbert exact-sequence theorem. This is the same commutative-algebra route as the cited proof of 00KQ, with that intermediate computation written out.

Read the chapter, unit `sk-i-curve-zero`, and current main-20261015 locality proof. The item's recorded ancestry is historical: the locality proof now follows contracting correspondences rather than the old nearby-duality/alteration branch. Its current ancestor does not explicitly assert this Hilbert--Samuel fact. I retained the existing historical `from.node` and `via`, made this limitation explicit in split_report.blueprint, and did not change the unit, the chapter, or another node. The item remains a legitimate algebra input of its immediate parent `lem-trf-formal-monoid-ring-dimension`.

## Searches and nonduplication

Before creating the node I searched the whole DAG for 00K1, graded-hilbert-polynomial, Hilbert--Samuel, Hilbert function, Hilbert polynomial, graded dimensions and homogeneous-component polynomiality, and searched the whole imported blueprint with `tools/blueprint_refs.py search` for Hilbert, Hilbert function, graded, graded module and 00K1. The ancestor command gives `lem-trf-local-term-locality`. No existing node states 00K1's module theorem. The standard graded algebra definition already exists as `def-pc-standard-graded-algebra` and is reused. The existing Artin--Rees, system-of-parameters and length-additivity nodes are Mathlib leaves, so no duplicate nodes are created for those inputs.

The command log contains two semantic phrasings for the new node, Loogle `"hilbertPoly"`, grep `hilbert|samuel` in RingTheory, and LeanSearch for the Hilbert--Serre theorem. I read the hits. Mathlib/RingTheory/Polynomial/HilbertPoly.lean:18-42 explicitly leaves graded-module Hilbert polynomials as TODO; lines 100-112 define a polynomial from an already supplied rational-series numerator, which does not prove rationality of a graded module's series. The local-ring searches found Krull-dimension inequalities and regular-element quotient dimension formulas, not the item's length-growth theorem. Loogle's length/polynomial hits concern coefficient-list length. The item's previously recorded searches from its creation are retained; fresh searches are appended, not invented.

## Not duplicates

lem-trf-standard-graded-hilbert-function vs lem-sc-hilbert-polynomial: the new node concerns homogeneous components of an arbitrary finite graded module over a field, not Euler characteristics of ample line-bundle powers on a proper scheme. The latter does not state the required module comparison.

lem-trf-standard-graded-hilbert-function vs lem-trf-hilbert-samuel-growth-dimension: the new node has no local ring, maximal-ideal-power quotient, positive-leading-coefficient assertion, or dimension conclusion; it is the independent graded-algebra input. The item supplies the local filtration, the discrete summation, and both dimension inequalities.

## Unfinished work

The new node is deliberately statement-only, with proof and proof_deps empty as required. Its later proof follows 00K1's induction on degree-one generators. No part of the item's proof is left as an uncited standard claim.

## Review by NF

I checked the item against 00K8 and 00KQ with those sources open. The nonzero hypothesis ensures H_R(n) is at least one, which is needed for the nonzero polynomial and positive leading coefficient; neither reducedness, a field of coefficients in R, completeness, nor equicharacteristic is assumed. The polynomial coefficients are rational even in positive residue characteristic. The statement's index is handled directly by summing degrees 0 through n-1, so there is no off-by-one shift to justify at the end.

For the new node I read 00K1, its finite-component lemma, and Example example-K0-field. A standard graded algebra is finitely generated over a field, so this is the field specialization of the source's Noetherian graded theorem. Its module is finite and nonnegatively graded, and its multiplication respects degrees. I explicitly allow P=0: finite-dimensional graded modules, the zero module, and the algebra k itself have eventually zero homogeneous dimension. No leading-degree or dimension conclusion was smuggled into this node. It is a substantive graded-algebra lemma, not elementary, not a clause of the local-ring item, and not already in the DAG, blueprint or Mathlib searches.

Step 1 uses the Noetherian definition precisely to choose finitely many maximal-ideal generators, the length definition to identify the length of a finite-dimensional residue-field vector space by a basis flag, and length additivity to sum the finite filtration. All three cited statements say exactly those things. The monomial spanning argument explicitly supplies finite-dimensionality; no general finite-length criterion is silently invoked.

Step 2 uses the existing standard-graded definition and the new node's eventual dimension polynomial with M=S. The multiplication on the associated graded ring is written down and its representative independence checked. The images of maximal-ideal generators are degree one and span all components multiplicatively; the unit generates S as its own module. Thus all hypotheses of the cited graded theorem are supplied.

Step 3 uses only the established filtration identity and the displayed binomial telescoping formula. The rational binomial basis has distinct degrees with nonzero leading terms. Positivity of eventual values excludes the zero polynomial and a negative leading coefficient, including constant polynomials. This is elementary polynomial arithmetic and does not need a separate node.

Step 4 reads the actual system-of-parameters statement: it supplies a finite d, exactly d generators, and a maximal-ideal power contained in J. Those clauses, and not merely its title, give finite length of R/J from step 1. The cited length-additivity statement supplies the quotient inequality and the filtration bound. Degree-i monomials give the displayed finite surjection. I checked both directions of ideal containment: J^n is contained in m^n, hence the length of R/m^n is bounded above by that of R/J^n. The d=0 case is separate, avoiding a binomial expression with denominator d-1. This tool is a Mathlib leaf, not an off-route unproved statement.

Step 5 reads the Artin--Rees statement, in particular its intersection containment and permission to enlarge the constant. It is applied only with a Noetherian ring A, finite module A, submodule xA, and ideal a. The domain and x nonzero hypotheses are exactly what make multiplication by x injective and identify xA with A. I checked the containment gives a surjection from xA/(xA intersect a^n) onto xA/a^(n-c)xA, so its length is at least H_A(n-c), yielding the stated upper bound on H_B. The exact-sequence calculation uses the full length-additivity statement. All its lengths are finite, as subquotients of A/a^n or by step 1. Quotient-ring versus original-ring lengths agree because the submodule sets agree. Choosing c at least one is essential for the finite difference to have positive leading coefficient; e_A=0 would force a nonzero quotient to have length at most zero and is explicitly excluded.

Step 6 uses length additivity for the quotient inequality e_A<=e_R and the Krull-dimension definition for the supremum over prime chains. The remaining argument is an explicit strong induction, not an appeal to the desired dimension theorem. Quotients by ideals inside the maximal ideal remain nonzero and local, and their ideals are lifted finitely generated ideals, so they remain Noetherian. Prime p_0 makes A a domain. The chosen nonzero x lies in p_1/p_0 and thus in the maximal ideal. All later primes contain x, so their images in B remain distinct by inverse image. The induction decreases polynomial degree strictly, handles degree zero directly, and counts l-1 inclusions in B, giving l<=e_R. Step 7 simply combines these results and takes a threshold at least one.

I checked small cases: a field gives H(n)=1 and degree zero; k[epsilon]/(epsilon^r) has H(n)=min(n,r), eventually constant r; a DVR gives H(n)=n and the nonzero quotient by a uniformizer is constant; the zero ring is excluded as required. For the graded node, S=k, M=0, shifted finite-dimensional modules, and S=k[T] give respectively eventually zero or constant homogeneous polynomials. No perfectness or residue-characteristic restriction was used. All proof steps are below 2000 characters. I rechecked delivery-errors B--E: new node has a self-contained statement only, exact sources and logged searches; every citation is a statement quote in citations.json; no cycles or relabelled clauses are intended; no SGA source is used.
