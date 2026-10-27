# Stage-1 report: lem-trf-differential-operator-localization

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-differential-operator-localization.json`: item, statement unchanged, split into eight steps following Stacks 0G36, including the omitted uniqueness argument.
- `dag/nodes/sec-trace-formula/lem-trf-differential-operator-composition-order.json`: one new statement-only node, unsplit, Stacks 09CJ. No Mathlib match: neither the returned derivation-composition lemmas nor the special polynomial Hasse-derivative formula gives the general recursive order bound for arbitrary modules.
- `citations.json`: one verbatim statement excerpt for every node in each step's `uses`.
- `searches.jsonl`: unmodified results recorded by the prescribed search command. The extra generator-criterion searches record a possible node that was deliberately not created.

## Attachments

None. Searched the project library `lean/WeilConjectures/` for the item tag and differential-operator names/concepts: no declarations found. Also checked `lean/Sheaf/`: its commutator occurrences concern Tate residues or categorical derivation transformations, not finite-order operators. No compiler or Lean writer was used.

## Literature

Read `literature/stacks-project/algebra.tex`, Definition 09CI (`definition-differential-operators`), Lemma 09CJ (`lemma-composition-differential-operators`), Lemma 0G35 (`lemma-check-differential-operators`), and Lemma 0G36 (`lemma-invert-system-differential-operators`), including their proofs. Tag-to-label assignments were checked in `literature/stacks-project/tags/tags`. These are the source for the item and the single new node. WANTED: none.

Read the unit and chapter records and the current files under `literature/blueprint/latest/blueprint/sec-trace-formula/`, especially `sk-i-curve-zero/lem-trf-local-term-locality.md` and its proof. The current blueprint uses contracting correspondences, whereas this assigned descendant records the earlier nearby-duality/resolution branch in `blueprint.from`. I preserve that historical provenance and split only the assigned supporting algebra claim; no chapter or unit route is changed or re-realized. No SGA source is used.

## Corrections and unfinished work

The item statement is correct and unchanged. The original empty proof is replaced. The Stacks proof omits uniqueness; Step 8 supplies it using the simultaneous induction hypothesis, rather than assuming localization is injective or citing an unnamed uniqueness fact. The common-refinement argument for equality of fractions is expanded to account for zero divisors. The source's algebra-generator test is expanded inline; it does not merit another node once the general composition theorem is cited. There is no statement dispute.

The single supporting composition theorem remains unsplit, as required for a new node. There is no other unfinished portion of this one-level split. In particular, no localization theorem restating all or a clause of the item was created.

## Searches and small cases

Searched the whole DAG for `0G35`, `09CJ`, `09CI`, the Stacks labels, differential-operator and composition concepts, and searched the whole imported blueprint using `tools/blueprint_refs.py search` for differential operators, commutators, algebra generators, composition differential, and 0G35. No node states the new composition theorem. The ancestor command confirms `lem-trf-local-term-locality`; the new node's `via` begins with the item followed by its previous `via`. `same_as` is empty after those searches.

For the new node, the command ran LeanFinder twice with different phrasings naming its own id, Loogle, LeanSearch, and a whole-Mathlib grep. All services answered; all recorded results are the command's actual log entries. Read the candidate types returned. `LinearMap.compDer` and `Derivation.llcomp` compose a derivation with an algebra-linear map; `Polynomial.hasseDeriv_comp` is a special polynomial calculation, not a general finite-order theorem. None is an exact or one-line generalization. For the item a new LeanFinder search confirmed the inherited searches' distinction: localization of Kaehler differentials concerns first-order derivations, not arbitrary orders. Read the potentially useful generator-search candidates at `Mathlib/Algebra/MvPolynomial/Derivation.lean:88` (`MvPolynomial.leibniz_iff_X`) and `Mathlib/RingTheory/Derivation/Basic.lean:164` (`Derivation.ext_of_adjoin_eq_top`); their polynomial/derivation hypotheses do not match the higher-order assertion.

Tested composition with either order zero, with both zero, with zero modules/maps, and with multiplication maps: the bound is exactly the expected one. For the item, order zero gives multiplication by D(1); the identity localization changes nothing; noninjective examples such as B=Z/6 at (2), and the zero operator, are covered by common refinement rather than cancellation in B. In positive characteristic the argument never divides by factorials or integers. The zero ring has no prime, so the item's prime hypotheses have no zero-ring counterexample; the composition theorem still applies to zero modules over the zero ring.

## Not duplicates

lem-trf-differential-operator-composition-order vs lem-trf-differential-operator-localization: both mention Definition 09CI, but the new node bounds the composition of two operators between arbitrary modules; the item extends one operator on a ring to its prime localization.

lem-trf-differential-operator-composition-order vs lem-trf-projective-order-algebra-additive-generators: the latter uses 09CI in its Hasse-derivative discussion and asserts generation of homogeneous maximal-order forms by additive polynomials. It does not state a composition bound for differential operators on arbitrary modules. It is an ancestor of the item, not an input to this proof.

## Review by NV

I read the item against Stacks 0G36, specialized with M=N=B and S=B minus p. Its hypotheses are precisely a commutative ring map, a prime and an R-linear operator of finite nonnegative bound; no characteristic, finite-generation, noetherianity, domain or injectivity hypothesis is used. I read the new statement against 09CJ, including its arbitrary module inputs and the k+l bound; its recursive definition is given inline. The algebra notion cites `def-weil-pbc-algebra-hom-quotient`, whose opening sentence defines an R-algebra exactly as a commutative ring with a structure map from R. I opened that statement and checked it; its ideal and quotient clauses are not used.

Step 1 cites `def-weil-pbc-localization-at-prime`. I opened its statement: it gives exactly fractions, their equality criterion and the map b to b/1. Its local-ring, residue-field and fibre clauses are not used. The bound-zero proof is the explicit identity D(b)=bD(1).

Step 2 cites the new composition statement, whose k+l conclusion gives the unchanged bound when either map is multiplication and hence order zero. Closure under sums, differences and zero is proved by the displayed recursive induction, not taken from an uncited statement. Step 3 cites that same composition conclusion to make both sides legitimate lower-order operators before applying the induction hypothesis. The induction is on the original localization assertion for all operators on the fixed B, and includes uniqueness. Thus it applies to L_bc, to the common restriction of the two double commutators, and to zero; it is not circular. The double-commutator identity follows by expanding D(bcx)-bD(cx)-cD(bx)+bcD(x).

Step 4 cites the actual fraction-equality sentence of the localization definition. I recomputed E_ts(z) using E_t(mu_s z)+mu_t E_s(z), with mu_s z=j(b), and verified cancellation of the two L_t(b) terms. For equality of arbitrary representatives, the explicit multipliers ut and us make the numerators equal in B itself. This covers torsion and is the correction that prevents an illicit injectivity argument. Step 5 uses only that constructed formula and R-linearity; common denominator st makes the additivity check legitimate.

Step 6 cites the composition conclusion for the inverse-multiplier expression. I checked the signs: [E,s^{-1}]=-mu_(s^{-1}) E_s mu_(s^{-1}). In the first calculation, [E_s,b]=[E_b,s], so the L_b(c) terms cancel and leave s E_b(c/s), as required. Cancellation is only by a unit in the localized ring. Step 7 cites the same composition theorem for product closure of H. All other facts in this step are explicit sum and product commutator identities or the expression of a fraction as j(b)j(s)^{-1}; this is the elementary subalgebra argument of 0G35, not a hidden lemma or an unproved appeal to generators. Its use of tag 0G35 names the argument actually written out. Step 8 applies lower-order uniqueness to [F,j(s)] and solves the resulting equation by the unit j(s). It uses no external lemma and supplies the uniqueness omitted by 0G36.

I checked every citation against its statement and created the verbatim excerpts in citations.json. The new node is statement-only, self-contained and not a clause of the item; tags, provenance, search records and the lack of a Mathlib match were checked. All proof steps are below 2000 characters. The long inherited blueprint provenance is history, not a long proof step. No maintainer fields, existing dependency nodes, unit records, Lean source, repository files or launcher files were changed. These checks address B (form and searches), C (actual statement citations and absence of cycles), D (a real induction and construction rather than relabelling), and E (hypotheses, representatives, signs and zero-divisor edge cases).

## Dry-run repair

The first dry run required a node citation in the new statement. I added the existing definition `def-weil-pbc-algebra-hom-quotient` for precisely its opening R-algebra clause, with matching `stmt_deps`; this changes no mathematical hypothesis. The only warning is the expanded 0G35 argument in elementary Step 7, which uses the cited composition statement and the displayed identities rather than assuming an additional theorem. No generator-criterion node is needed.
