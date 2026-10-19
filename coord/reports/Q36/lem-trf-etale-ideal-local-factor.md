# Report: lem-trf-etale-ideal-local-factor

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-etale-ideal-local-factor.json`: unchanged statement, five proof steps, blueprint metadata and split report; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-etale-fitting-trick.json`: one new statement-only unsplit node, the finite-free specialization of Stacks 0812; no Mathlib match.
- `citations.json`: a verbatim statement quote for each node cited by each proof step.

## Attachments

None. I searched `WeilConjectures/` in the read-only slopmaster2 source by the item id, Stacks label, and etale/ideal/Fitting terminology. No project declaration states either the item or the new auxiliary lemma. The upstream master checkout is not treated as evidence of a closed proof.

## Literature wanted

None. The sources used are present in `literature/stacks-project/`.

## Corrections and unfinished work

The imported item had no proof, and its statement agrees with Stacks 0813. No statement or hypothesis was changed. Stacks' proof has the index slip `h_{r+1}` after defining `h_1,...,h_n`; the split consistently writes the enlarged ideal as `(c_1,...,c_r,a_C^m)` and does not reproduce that slip. The nonzerodivisor hypothesis is retained even though the written argument does not need it. The new auxiliary lemma remains unsplit, as this delivery splits the item by one level only.

I repaired a missing chapter/unit on the new node caught by the server DAG check. The first search-log check failed because I had invoked the search command with the auxiliary id as its delivery-item argument; those results were real searches, but belonged to a different log. I then ran the searches under the required parent item id and replaced the new node's search records with exact entries from this sandbox's `searches.jsonl`. The different phrasings and actual hits have been read; none provides this factorization. Existing searches imported on the item were retained, and my item searches were appended.

## Review by Q36

I read Stacks `flat.tex` 0813 (`lemma-push-ideal`, lines 8875–8901) for the item and 0812 (`lemma-trick-fitting-ideal`, lines 8848–8873) for the new node, including their complete proofs. The new statement specializes 0812 from finite locally free constant rank to finite free, which is exactly what the monic quotient in 0813 supplies. It neither assumes the boundary element nor states the item's local existence or support condition. Its Fitting ideal means exactly the kernel-minor ideal defined by the existing 07Z8/07ZA node. I read that node's statement before using it. I checked the tags in `stacks-project/tags/tags`, and read the relevant standard-etale convention 00UB/00UE and radical criterion 00E0 in `algebra.tex`.

Step 1 cites `lem-weil-pbc-zero-locus-eq-iff-radical-eq` for its explicit intersection-of-primes formula, not merely its equality-of-zero-loci clause. The inclusion `V(J) ⊂ V(aB)` says that each prime in the intersection contains `a_B`, so the same statement's definition of the radical supplies an exponent m≥1. Doing this before localization avoids an unstated compatibility claim about zero loci after localization.

For Step 2 I read the complete statements of `lem-weil-pbc-etale-locally-standard`, `lem-weil-pbc-principal-localization-open-immersion`, `lem-weil-pbc-etale-composition-cancellation`, and `lem-weil-pbc-monic-quotient-free`. The first supplies g outside the chosen prime and the monic standard-etale presentation over the unchanged base A. The second and third say that Spec(B_g) is etale over A. The last gives exactly the finite free basis of C required by 0812; it is valid over an arbitrary commutative base, without Noetherian or domain assumptions. The displayed maps identifying the standard-etale presentation with C_h are inverse by the relation Yh=1, so no additional comparison theorem is being hidden.

Step 3 uses only the fraction description in `def-weil-ring-localization-away`, whose statement I opened. If a localized generator is c_i/h^{e_i}, multiplication by the unit h^{e_i} replaces it by c_i without changing the generated ideal. The power adjoined is already in the localized centre by Step 1. This proves the equality K C_h=theta(J B_g) and the annihilation of C/K explicitly; it is marked elementary. No finite-generation descent assertion is used.

Step 4 applies the new node to the specific generating surjection A^d≅C→C/K. I checked all its hypotheses in the earlier steps: finite freeness from the monic-quotient node, etaleness after localization from the open-immersion/composition nodes, and finite generation of K from its listed generators. The source 0812 gives both finite generation assertions as well as the factorization; pulling the auxiliary generators back along the algebra isomorphism gives the required J' in B_g.

Step 5 cites `lem-trf-fitting-ideal-independence-base-change` for its actual kernel-row definition, and `def-weil-pbc-matrix-determinant` for the Leibniz formula. I read both statements. Each row a^m e_i is in the kernel because a_C^m annihilates C/K, and the determinant is the product of diagonal entries. This is a two-line calculation from the cited definitions and is marked elementary. For d=0 the kernel-minor convention gives I=A and an empty zero locus; for d>0 the positive exponent md allows the prime-ideal implication. This step proves the support condition rather than moving that clause into the new node.

I tested the item on B=A (one can take I=J, g=1, J'=A), B=A_a (the localized centre is the unit ideal, so I=A works), B=0 (there is no prime q), and J=B. For J=0, the regular-element hypothesis and V(0)⊂V(aB) force the nonzero-chart case to be empty; no illicit injection of A into B is used. I tested the auxiliary statement on C=A, h=1 (I=K and L=A), C=A×A (I=K_1K_2, with the two complementary factors on the two components), K=0 (I=0 in positive rank), K=C (I=A, L=C_h), h=0 (zero localization), and rank zero. In positive rank, the ordinary product formula is consistent with the source's decomposition by the etale diagonal; no Noetherian or flatness-of-quotient assumption has been introduced.

Against delivery-errors B–E, the new node is self-contained, defines its notation through explicit definition citations, has no proof or proof dependencies, and records only searches actually run. I searched the whole DAG by tags and concepts, the whole blueprint using `blueprint_refs.py search` (including Fitting, 0813 and lemma-trick-fitting-ideal), and the project source. The blueprint has no separate statement of the new factorization. I read each statement flagged by the same-tag check; the comparisons are below. All cited statements say what the steps take from them, and all remaining non-elementary facts are cited. No step exceeds 2000 characters. No SGA source, source download, Lean edit, compiler, Lake, or local preflight was used. The inherited chapter/unit and full ancestor chain are preserved; this is the existing general algebra ingredient below the flattening-descent branch, with no change to the unit's contracting-correspondence route. The item is not the unit's key node, so its realized fields are untouched.

## Not duplicates

lem-trf-etale-fitting-trick vs lem-sc-etale-coproduct-etale: the existing lemma asserts etaleness of a coproduct of etale morphisms; the new lemma factors a specified zeroth Fitting ideal after an etale localization.

lem-trf-etale-fitting-trick vs lem-weil-pbc-affine-chart-directed-ring-model: the existing statement models affine charts in a directed limit of schemes; it contains no Fitting-ideal or ideal-product assertion.

lem-trf-etale-fitting-trick vs lem-weil-pbc-descend-etale: the existing statement descends etaleness to a finite stage in an inverse system; the new statement concerns ideals in one fixed finite free algebra.

lem-trf-etale-fitting-trick vs lem-weil-pbc-etale-algebra-finite-presentation-localization: the existing statement gives finite algebra presentation and persistence of etaleness under localization; it does not give a Fitting ideal factorization or finite generation of the factor.

lem-trf-etale-fitting-trick vs lem-weil-pbc-etale-algebra-flat: flatness of an etale algebra does not assert divisibility of a zeroth Fitting ideal by an arbitrary localized ideal.

lem-trf-etale-fitting-trick vs lem-weil-pbc-etale-local-on-source: locality of etaleness on an open cover contains no ideal-product statement.

lem-trf-etale-fitting-trick vs lem-weil-pbc-etale-near-prime-naive-cotangent-vanishing: the existing node finds an etale neighborhood from cotangent vanishing, whereas the new node assumes an etale localization and proves a Fitting ideal factorization there.

lem-trf-etale-fitting-trick vs lem-weil-pbc-etale-over-normal-ring-normal: preservation of normality is about local rings; the new lemma assumes neither normality nor reducedness and concerns Fitting ideals.

lem-trf-etale-fitting-trick vs lem-weil-pbc-etale-ring-map-conormal-criterion: the existing node characterizes etaleness by a conormal differential map, not by a factorization for arbitrary K⊂C.

lem-trf-etale-fitting-trick vs lem-weil-pbc-etale-ring-map-iff-etale-affine: the existing node equates the ring and scheme etale conventions; it says nothing about the Fitting ideal of C/K.

lem-trf-etale-fitting-trick vs def-trf-first-fitting-singular-subscheme: that definition constructs a first-Fitting closed subscheme from relative differentials; the new statement is a zeroth-Fitting algebraic factorization for arbitrary quotients C/K.

lem-trf-etale-fitting-trick vs def-trf-fitting-ideal-sheaf: that definition constructs Fitting ideal sheaves from affine presentation ideals; it does not prove the new ideal-product equality.
