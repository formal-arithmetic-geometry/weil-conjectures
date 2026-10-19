# N7: lem-trf-cm-ring-universally-catenary

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-cm-ring-universally-catenary.json`: statement; split into six steps, statement unchanged; not a Mathlib leaf.
- `dag/nodes/sec-trace-formula/lem-trf-polynomial-algebra-cm.json`: new statement-only unsplit node, Stacks 00ND; no Mathlib match.
- `citations.json`: verbatim statements for every node cited in every item step.
- `searches.jsonl`: actual msearch.py results; the node JSON records those exact tool/query strings and results. Sandbox script `write_split.py` assembles the JSON only.

## Attachments

None. I searched the project source under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, the blueprint tag, catenarity, Cohen–Macaulayness and the polynomial Cohen–Macaulay concept. No declaration states the item or the new node. The upstream master checkout is not used as evidence of finished proofs.

## WANTED

None. All mathematical sources needed here are present in `literature/stacks-project/algebra.tex`, and tag-label correspondences were checked in `literature/stacks-project/tags/tags`.

## Issues found and corrected

The item was statement-only, with no proof or Lean audit attachment, and the sandbox contained only dispatcher brief markers. I retained its statement, previous search records, source, created fields, unit and blueprint ancestry. No statement dispute arose. Its source mentions the polynomial and chain facts but had not named the corresponding dependencies. I reused the existing 00N9 maximal-chain node and 00E3/00E5 prime-correspondence leaves. Only the missing 00ND polynomial Cohen–Macaulay assertion becomes a new node. The more general full-support module assertion of 00NM is not needed or introduced.

I expanded two reductions that 00NM leaves implicit: finite local dimension supplies existence and bounds for prime chains; a finite-type algebra is a polynomial quotient whose entire prime interval is identified with the interval above its kernel. This does not assume a uniform finite dimension for R or its polynomial algebra. I checked the quotient lemma's tag in tags/tags and corrected the draft source reference from 00NJ to the actual 00NK before delivery. The canonical source tag for the quotient prime correspondence is 00E5.

The blueprint ancestry is the inherited arithmetic-model universal-catenarity input below the regular-ring node, not a replacement for the unit's contracting-correspondence route. I read the current main-20261015 local-term proof and unit sk-i-curve-zero. The generic 00N9 use is declared in split_report.tool_uses; the other off-unit results are Mathlib leaves or definitions. No chapter or unit file is changed. No SGA source is used.

## Unfinished work

The new 00ND node is intentionally unsplit: its future worker must split the preservation of Cohen–Macaulayness by adjoining variables. It is a genuine input different from catenarity, not a clause of the item moved into a new name. No work required for this one-level split remains after the delivery checks pass.

## Not duplicates

Whole-DAG searches for 00ND, 0AAI, lemma-CM-polynomial-algebra, polynomial/Cohen–Macaulay combinations and the proposed id found no existing node stating this theorem. Whole-blueprint searches for Cohen, catenary, 00ND, polynomial Cohen, and polynomial found no same-statement node; the broad polynomial hits concern unrelated definitions or field/coefficient assertions. The project-source concept search found no declaration to attach. There are no existing nodes with the new node's source tags 00ND or 0AAI.

lem-trf-polynomial-algebra-cm vs lem-weil-pbc-polynomial-ring-field-regular-ring: the latter has a field base and gives regularity; the new statement permits any Noetherian Cohen–Macaulay base and only asserts local depth equals dimension.

lem-trf-polynomial-algebra-cm vs lem-weil-pbc-cm-local-maximal-chain-length: the latter controls chains in one already Cohen–Macaulay local ring; it does not show that polynomial extensions are Cohen–Macaulay.

lem-trf-polynomial-algebra-cm vs lem-pur-cohen-macaulay-field-extension: the latter concerns base change of finite-type schemes over a field along a field extension; the new node concerns polynomial extension of an arbitrary Noetherian base ring, with no field hypothesis.

## Review by N7

I read Stacks algebra.tex 00NM (lemma-CM-ring-catenary), including its two applications of 00N9, its first reduction to polynomial rings and the separate module generalization. For the sole new node I read 00ND (lemma-CM-polynomial-algebra), its definition of a CM ring immediately above, and its cited module theorem 0AAI (lemma-maximal-CM-polynomial-algebra). The new statement expands “Cohen–Macaulay” at both source and target into depth equals Krull dimension at every prime, and restricts “polynomial algebra” to finitely many variables, exactly what 00NM needs. It contains no hidden proof or unintroduced objects, and each of its notions has a statement dependency.

For Step 1, I checked that the new polynomial node really states both Noetherianity of P and Cohen–Macaulayness of every prime localization, under exactly the item's hypotheses. For Step 2, I opened the localization definition (it includes locality and its maximal ideal), the Noetherian definition, the Noetherian-local finite-dimension leaf, and the primes-of-localization leaf. The local Noetherian argument is written from contraction and fractions: multiplying by a denominator shows an ideal is generated by its contracted ideal. Hence the finite-dimension lemma applies to the actual rings being used. The prime correspondence has inverse extension and preserves inclusions in both directions, so it bounds chains of P below q without assuming global finite dimension.

For Step 3, the same finite bound gives a largest available prefix length because the set of lengths is a nonempty finite set of natural numbers. Inserting a prime would contradict maximal length. The localization correspondence's statement gives all primes below p, so this prefix really becomes a maximal chain in P_p. This is an elementary finite-chain argument, not an uncited existence theorem.

For Step 4, I opened lem-weil-pbc-cm-local-maximal-chain-length in full. Its hypotheses are Noetherian local, finite dimension d, depth at least d, and a chain with minimal first prime, maximal last prime and saturated successive pairs. Step 2 supplies the first two, Step 1 supplies depth equality (and therefore the required inequality), and Step 3 plus the given saturated chain supply the last condition. The concatenation has length m+t, so the two direct applications yield m=d_p and m+t=d_q. I checked p=q: t=0 and both local dimensions agree. There is no use of the stronger CM module generalization, localization preservation of CM, or a dimension-formula theorem hidden here.

For Step 5, I opened the finite-type definition and the quotient-spectrum leaf. The definition gives the surjective polynomial presentation. The leaf gives the exact prime bijection and its inverse; inclusion preservation follows directly from inverse image and image. Every intermediate prime contains the lower endpoint and hence the kernel, so the entire interval is present, including every potential inserted prime. This elementary argument proves the quotient's catenarity from Step 4 and does not require a separate new quotient-catenarity node. For Step 6, I opened def-exc-excellent-ring and checked its universal-catenarity clause contains both the finite bound and equality of saturated chain lengths. Step 5 proves precisely that clause for arbitrary finite-type A; no condition on excellence, G-rings or J-2 is asserted or used.

I tested the item and new node on the zero ring (no prime localizations or chains), n=0 (the polynomial assertion is the given hypothesis), fields, an Artinian CM ring with nilpotents such as k[epsilon]/(epsilon^2), and a DVR. No argument assumes reducedness, a domain, or finite global dimension. All step texts are below 2000 characters (the longest is under 1200); none hides a standard comparison or a new substantive sublemma. I checked B1–B10, C1–C8, D1–D5 and E1–E7 against these files and sources: one genuine new input, no duplicate or relabelled clause, explicit applications with the right hypotheses, verbatim citations, correct tag labels and actual logged Mathlib searches. The semantic hits concern Noetherianity, polynomial dimension and presentations; none provides the depth assertion or universal catenarity. Loogle and full-source grep found no such predicate/theorem. The report records my own check, not an independent second review.
