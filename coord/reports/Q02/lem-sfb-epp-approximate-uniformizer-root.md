# Worker report: lem-sfb-epp-approximate-uniformizer-root

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-epp-approximate-uniformizer-root.json`: statement, split using existing nodes; Mathlib searches found no match.
- `citations.json`: verbatim statement quotes for every step/node citation.
- `report.md`: this review. No new nodes; zero Mathlib leaves created.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag, approximate uniformizer roots, Eisenstein, and separable uniformizers. Existing uniformizer-root declarations concern exact roots, whose characteristic-p extensions are inseparable; they do not state this item. Nothing was compiled or written to Lean.

## WANTED

None. All sources used are present in `literature/stacks-project/`.

## Corrections and blueprint

The imported statement contained doubled TeX backslashes in its string. Reduced those to single TeX backslashes; the mathematical statement and all its hypotheses and clauses are retained. Equality of residue fields is understood through the canonical residue isomorphism, explicitly computed in step 5. No statement dispute was found.

Read the chapter/unit records, the three levels in SETUP.md, and latest blueprint `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md` (latest snapshot main-20261024). This Epp lemma is a historical auxiliary below the imported direct-image route; the current blueprint does not state it. Preserved the existing historical provenance and via chain; `blueprint_refs.py ancestor` returns None. Whole-blueprint searches for Eisenstein, 09EW, approximate uniformizer root and uniformizer were read; none states this general prime-power approximation. The existing degree-p approximation node is only a special case and cannot supply degree p^r; it is not used to relabel the item. The stronger generic existing Eisenstein quotient node is reused rather than recreated.

## Unfinished work

None in this one-level split. Existing unsplit dependencies retain their own work. No new statement-only nodes are needed.

## Not duplicates

No new nodes. Reused lem-sfb-eisenstein-quotient-dvr for Tag 09ER; lem-sfb-epp-separable-uniformizer-approximation (Tag 09EW) only asserts q=p, whereas this item handles all p^r and retains both explicit approximation identities.

## Review by Q02

I read Tag 09EW (more-algebra.tex, lemma-make-degree-q-extension), including its substitution y=pi z, and Tag 09ER's last Eisenstein quotient sentence. I also read the actual statements of every cited node and the relevant source inputs: algebra.tex Tag 00PD (DVR characterization), Tag 00IC (valuation rings normal), Tag 00MA (finite-module completion by base change), and fields.tex Tag 09H9 (separably generated extension), as well as the cited definitions of integral closure, separability, field extension and completeness. The proof expands the short source argument; it does not take extra conclusions from its cited nodes' proofs.

Step 1 uses exactly the DVR and maximal-ideal conclusion of lem-sfb-eisenstein-quotient-dvr, with all Eisenstein coefficients checked for the explicit polynomial. The constant term is -pi, never pi squared; q>=2 prevents collision of the leading and linear terms. The monic quotient node supplies the entire basis, rank and faithful inclusion, not an unproved normalization assertion.

Step 2 uses that same monic basis after inverting nonzero base elements. Localization of a domain remains a domain by the explicit fractions description; multiplication by a nonzero element is injective and hence surjective on this q-dimensional space. This is elementary finite-dimensional linear algebra, and proves that the localized quotient is a field rather than assuming an irreducibility result. Every fraction of C exists in it, and it lies in Frac(C), identifying the fraction field and its degree. Minimality of f follows from the independence of the displayed basis, so there is no hidden Eisenstein-irreducibility citation.

Step 3 uses the separable-polynomial definition through the displayed Bezout identity and the minimal-polynomial definition of separable algebraic element. The cited simple-extension theorem really says the whole generated extension is separable, which a polynomial definition alone would not imply. The derivative is the nonzero constant -pi^N because char(E)=p and p divides q. No perfection of the residue field is needed.

Step 4 uses the integral-closure definition, including its subring clause, to include R[t] without appealing to finite-implies-integral. The DVR definition explicitly records the valuation-ring characterization, so lem-weil-pbc-valuation-ring-normal applies to C with its already identified fraction field. The same monic equation then places any R-integral element in C. This proves the required integral closure, rather than merely constructing some DVR extension.

Step 5 uses the local-ring and uniformizer clauses of the DVR definition. The factor u is 1 modulo (t), hence a unit. The explicit ideals and quotient presentation prove both ramification and canonical residue identification. There is no residue-field assumption hidden in this calculation.

Step 6 uses the finite-module completeness node with base R, ideal (pi), and module C. R is Noetherian because every ideal is principal, and C is finite free by step 1. The source Tag 00MA supports exactly this complete Noetherian specialization. Completeness for (pi)C is converted to completeness for (t) by an explicit inverse-limit reindexing, not by an unproved change-of-topology claim. The hypotheses required by the cited node are all present. Normality and finite-module completeness are declared as generic off-unit tool uses in split_report.

Step 7 is just the source's polynomial equation and multiplication by u to the negative h power. Its elements b=pi^(q-1)t and b'=u^(-h)b are visibly in C. Thus the same t supplies both formulas, with the correct signs and exponents.

I checked B1-B10: no new nodes, no hollow data, complete source tags, actual logged Mathlib searches and exact statements. I checked C1-C8: every non-elementary input is a cited existing statement with its verbatim quote in citations.json; dependency traversals from all five theorem tools do not reach this item; generic off-unit tools are declared. I checked D1-D5: the proof constructs the extension and computes its properties, rather than moving the item or one of its clauses into a new node. I checked E1-E7 on q=2, h=2, arbitrary imperfect residue fields, and r>1: the derivative remains nonzero, the polynomial is Eisenstein, u is a unit, and the hq exponent follows from pi=t^q/u. The excluded q=1 case is not used. No step exceeds 2000 characters or hides a separate comparison lemma. Existing searches and new actual search results were retained without fabricating a query. The only source-level change is TeX escaping; no weakened statement or SGA source is used.
