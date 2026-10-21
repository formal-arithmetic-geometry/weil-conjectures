# Stage-1 delivery: lem-sfb-prime-to-ell-linear-image-finite

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-prime-to-ell-linear-image-finite.json: item, split into five proof steps; no statement change.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-matrix-group-coprime-power.json: new statement, Mathlib leaf. Nat.Coprime.pow_left_bijective, Mathlib/GroupTheory/OrderOfElement.lean:1245-1247, directly specialized to the finite subgroup G.
- citations.json: verbatim statements for every step citation.
- searches.jsonl: genuine msearch.py query records; all new recorded searches were run and their hits read.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and prime-to-ell/profinite linear-image notions, and inspected the plausible representation-theory/real-sheaf hits. No complete project declaration states this item. The existing stable-lattice result supplies only an ingredient and is reused as a DAG theorem, not claimed as an attachment.

## WANTED

None. The lattice input is already a node and its source is present. The additional argument is explicitly marked agent-written, rather than attributed to an absent reference.

## Corrections and scope

The statement is correct, including the zero-dimensional case, and is unchanged. The inherited Mathlib-search verdicts referred to an unrelated condensed-module assertion; corrected those verdicts to discuss this actual statement, preserving their queries/results. New searches used two semantic phrasings for the item and the finite matrix power lemma. Semantic results for the item concern finite quotients, local fields and arithmetic subgroups, not this theorem. The new leaf is a bijection of sets: despite misleading semantic service descriptions, the power map need not be a group homomorphism. Read the actual declaration to establish exactly this distinction.

Read the chapter record, the unit record sk-thm-sf-ctf-stability, and the current main-20261015 unit statement and direct-images proof. This is a group-theoretic tool below paragraph (3), the open-direct-image route through tame-boundary Kummer descent; no unit route changes. The supplied item has a broken created.item ancestry (lem-sfb-admissible-direct-image has no created record), and blueprint_refs.py ancestor prints None. Kept the inherited null ancestor, with the exact paragraph in from.place and split_report.blueprint, and used that same computed ancestor for the leaf. No maintainer metadata or unit record was edited.

Generic off-unit tools are declared in split_report.tool_uses: lem-pod-profinite-stable-lattice supplies the compact-group lattice and its topology; lem-weil-valued-dvr-finite-quotients supplies finite coefficient rings. Their statements were opened and read. These are coefficient/representation tools, not replacements of the unit's geometry.

## Not duplicates

No new Stacks-tagged node was created. Whole-DAG searches for coprime powers, power-map bijectivity and the exact Mathlib declaration found no existing statement of the new leaf. The occurrence of pow_left_bijective in lem-exc-tame-ell-coordinate is a search result, not that node's statement. Blueprint searches for coprime cardinality, coprime power, power map, matrix group, finite image and congruence did not find a duplicate. Existing stable-lattice and coefficient-ring nodes were reused. The new leaf says nothing about profinite groups, continuity, local fields or finite monodromy, so it is not a restatement or clause of the item.

## Review by Q02

I read Stanford Weil II seminar L19.pdf, Proposition 1.1.9 on printed p. 3 (also examined pp. 2-3). Its second bullet proves the stable-lattice input and its third bullet discusses finite reductions. The prime-to-ell corollary is not a theorem in these notes; the congruence argument here is explicitly agent-written. For the new leaf I read the pinned Mathlib source at lines 1210-1247, including powCoprime and Nat.Coprime.pow_left_bijective. The latter has only the group and coprimality hypotheses and states precisely bijectivity of the power map. I also read the statement of def-weil-matrix, which defines its matrix notion; matrix multiplication, inverse, coprimality and finite group order are spelled out in the new statement. This new node has no proof or proof dependencies.

Step 1 uses the full statement of lem-pod-profinite-stable-lattice: H is compact because it is profinite, M is finite-dimensional with the stated norm topology, and joint continuity is exactly the assumed action continuity. Its conclusion gives a free full lattice, equality under every group element, adic/subspace topology agreement and the restricted continuous action. This justifies the integral action and its inverse in a lattice basis. I separated the rank-zero case before the basis argument: its image has order one.

Step 2 uses that lattice statement for evaluation continuity and the coefficient datum for O_E, pi and A_n. I added the actual theorem lem-weil-valued-dvr-finite-quotients for finiteness rather than leaving the argument solely on the definition. Its hypotheses match: a nonarchimedean absolute value, its valuation DVR, finite residue field and a uniformizer generating the maximal ideal are explicitly supplied by the coefficient datum. Open cosets modulo pi^n Lambda are the definition of the adic topology. Finitely many basis evaluations give continuous maps into the finite discrete matrix groups; their images Q_n are themselves continuous finite quotient groups of H. This uses the hypothesis on H itself, without silently assuming it for arbitrary subgroups.

Step 3 uses only the extending absolute value and maximal-ideal description in def-weil-l-adic-coefficient-extension. It explicitly shows ell belongs to pi O and proves the first-order matrix congruence by multiplication induction. The cross term has order 2n >= n+1 for n>=1; no unramifiedness, oddness or convergence of a matrix logarithm is assumed. This is a short elementary calculation, so no separate congruence-group node is introduced.

Step 4 uses the exact conclusion of the new Mathlib leaf on Q_(n+1). Its order is coprime to ell by Step 2; the matrix calculation shows the ell-th power of the selected element is the identity. Injectivity of that power map then gives the identity itself. Both the induction base and the reverse kernel inclusion are written, so the statement K_1=K_n is proved for every n, not asserted by a pro-ell slogan. The leaf is a generic group-theoretic input strictly smaller than the item.

Step 5 uses the coefficient datum's norm and uniformizer. An entry in pi^n O has norm at most |pi|^n, which tends to zero since 0<|pi|<1; hence the intersection is zero. Fullness of the lattice then detects the identity on M. I wrote the actual correspondence of the image with Q_1 and checked its well-definedness and injectivity by the equality of kernels; its surjectivity follows from the definition of Q_1. Thus finiteness and the prime-to-ell order assertion both follow, not just finiteness.

Against delivery-errors B-E: the new statement introduces every object and has a real exact Mathlib match with verified file/line; its searches are logged, and blueprint/DAG/source duplicate searches were performed. Every cited node statement was opened, and citations.json copies it verbatim. The only new node is the finite-matrix power tool, not a clause of the item. All remaining steps are explicit few-line calculations from cited statements; no hidden topological or pro-ell structure theorem is used. No step exceeds 2000 characters. Checked M=0, trivial H, trivial representation, ell=2, ramified E and n=1. For the new leaf, checked r=0 (trivial group), n=0 (coprimality forces |G|=1) and n=1; all agree with Mathlib. No statement dispute or source error was found.

## Unfinished work

None in the split. This delivery contains no Lean changes and runs no compiler or build.
