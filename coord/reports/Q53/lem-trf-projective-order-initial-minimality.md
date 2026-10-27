# Stage-1 delivery: lem-trf-projective-order-initial-minimality

## Files written

- dag/nodes/sec-trace-formula/lem-trf-projective-order-initial-minimality.json: item, statement; complete six-step split, unchanged statement, not a Mathlib match.
- citations.json: one verbatim dependency-statement excerpt for each of the 14 step/node citation pairs.
- report.md: this report. searches.jsonl is the unedited search-command log.

## New nodes

None. The proof uses two existing Mathlib leaves, for faithfully flat coefficient extension and contraction of ideals. It needs no extra assertion about Hironaka's order algebra, additive generators, Cohen coefficient fields, completion, or smooth purity. The coefficient calculation at a rational origin is written out in the item's steps rather than made into an elementary new node.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, Hironaka, projective order, and initial-form minimality. No declaration states this item; sorry declarations would not count. Read the existing polynomial and associated-graded definitions and the statements of both algebra leaves used below.

## WANTED

WANTED: Hironaka, Certain numerical characters of singularities, J. Math. Kyoto Univ. 10-1 (1970), pp.151–187, archival copy, especially Lemma 15 pp.170–171, for lem-trf-projective-order-initial-minimality. I read those pages through https://scispace.com/pdf/certain-numerical-characters-of-singularities-18d51ii5bz.pdf. The inherited source.document points to ILO, which supplies the historical resolution motivation, not the proof of this algebraic lemma. I did not download or write literature files. proof_origin.by is agent because the argument adapts the source's enlargement argument at the residue-field diagonal point.

## Findings and corrections

The item is true as stated, including arbitrary prime ideals and inseparable residue fields. No hypothesis or conclusion was changed. The existing proof was empty. Hironaka's proof enlarges the coefficient field and chooses linear coordinates. I instead use K = L/N, translate t_i to a_i + Z_i, and work at the rational origin of K[Z]. This avoids any assertion that the map on tangent graded rings from L is injective; in inseparable examples it is not. Only its multiplicativity and its values on our particular initial forms are needed. All grade comparisons, denominators, and maps are explicit in steps 1–6.

The chapter and unit records were read, and remain unchanged: this is an algebra tool below the historical alteration branch of the current blueprint ancestor lem-trf-local-term-locality proof (1)–(2), via the existing permissible-standard-basis chain. The current literature/blueprint/latest ancestor statement and proof were read, with snapshot main-20261024, ef6f9619fdbffa59e88528fb56483d76c70258c8. It now routes the local-term theorem directly through Varshavsky; this delivery does not alter that ancestor or revive its historical route. The inherited from.place already specifies the historical branch. Whole-blueprint searches for “projective order”, “graded polynomial”, and “initial form” found no equivalent blueprint node. No new duplicate or clause-node was introduced.

The fresh msearch.py runs cover LeanFinder, LeanSearch, Loogle and grep, with a second concept phrasing. They returned homogeneous-ideal and projective-spectrum facts, ordinary span-power descriptions, homogeneity under coefficient maps, height bounds and power-series orders. These do not state the local initial-form/minimal-generator assertion or specialize to it in one line. One Loogle query used the unknown short identifier IsHomogeneous; its invalid-query result is recorded explicitly, and the successful retry uses MvPolynomial.IsHomogeneous and MvPolynomial.map. The earlier searches of the inherited item are retained unchanged. No unavailable service is represented as a successful no-match.

## Not duplicates

No new nodes, so there are no new/existing node pairs to distinguish. The existing projective-order-homogeneous-approximation node is a different approximation assertion and is not used: citing it could needlessly risk a dependency cycle.

## Review by Q53

I checked the item against Hironaka Lemma 15, printed pp.170–171, and read the relevant chart/order conventions on pp.168–169. The source's SB condition means a minimal homogeneous generating family sorted by degree, exactly as in the item. In the replacement proof, the field extension is allowed to be transcendental or inseparable: K is the actual residue field of the original local ring, and no algebraic-closure or separability property is invoked. I also read Stacks algebra.tex at the labels lemma-ff (00HP), lemma-flat-base-change (00HI), and lemma-faithfully-flat-universally-injective (05CK), checking the statements behind the reused leaves.

Step 1 uses def-weil-pbc-localization-at-prime for K = L/N and fraction denominators, and def-weil-pbc-mv-polynomial-ring for substitution. I checked that s outside p has nonzero residue s(a), so its substituted polynomial is a unit in the origin localization. For a numerator in p its constant coefficient vanishes. This proves the ideal-power inclusions needed later, with no missing closed-point hypothesis.

Step 2 uses the polynomial definition for the explicit tensor/coefficient isomorphism. The statement of lem-weil-pbc-field-extension-base-change-faithfully-flat applies to D = B and K/k; lem-weil-pbc-faithfully-flat-ideal-contraction says precisely that the extended ideal contracts to the original ideal and that the map is injective. Applying it to each ideal generated by the other forms proves preservation of minimality, rather than merely preservation of their nonzero images. Both are existing Mathlib leaves, not new nodes or a changed unit route.

Step 3 uses the localization fraction definition, the finite monomial definition, and the associated-graded representative multiplication from their three definition nodes. The elementary calculation is included: multiply all the finitely many denominator polynomials, compare the least homogeneous term with its product by the nonzero constant of that denominator, and reduce f/s modulo the next power by its degree-n numerator and constant denominator. This proves injectivity, surjectivity and multiplicativity of the particular beta map. It does not cite the associated-graded definition as if that definition itself asserted the isomorphism. The domain assertion used to pass from a localized equality to a polynomial equality is justified by the leading term of a product over the field K. This calculation is a few lines of finite coefficient algebra, so I did not create a new node for it.

Step 4 cites the polynomial and standard-grading definitions: the invertible linear substitution and its explicit inverse preserve total degree. The unique expression sum c_alpha X0^(e-|alpha|) Z^alpha shows that specialization X0 = 1 is injective on a fixed homogeneous degree, which is essential here. Step 1 and the U hypothesis give membership in M^e, and step 3 then removes every smaller-degree term. The resulting q_i is nonzero homogeneous of degree e, not a polynomial with merely an upper degree bound.

Step 5 cites the associated-graded definition for the displayed formulas on classes and products. The contradiction with M^(e+1) gives exact order, without needing separation of the entire adic filtration. The map gamma is constructed degree by degree and is well defined by the inclusions already proved. Its residue-field map is the identity K to K, and its values on eta_i are beta(q_i). I checked that no injectivity assumption about gamma is smuggled in.

Step 6 cites the polynomial, standard-grading and associated-graded definitions. An invertible substitution preserves the minimality obtained in step 2. A relation in K[Z] would also be one in K[X0,Z], so minimality holds in the smaller ring. A hypothetical original graded-ring relation maps under gamma and beta inverse to exactly such a forbidden relation. The ideal is homogeneous by componentwise decomposition of each finite coefficient. I corrected the wording “polynomial multiples” here to “graded-ring multiples”: no polynomial presentation of the original graded ring was proved or required.

I tested b = 0, r = 0, p = (0), rational primes p = (t_i-a_i), and an inseparable prime p = (t^p-u) over k = F_p(u). For the generic prime N = 0 there are no nonzero positive-degree U forms. For r = 0 the same observation forces the empty family. At a rational prime the proof is ordinary translation of homogeneous forms; e.g. the linear form X1-aX0 has exact order one. In the inseparable one-variable example, (t^p-u) has local order one although its degree is p, so it is not in U_p; its tangent image can vanish after the residue-field translation, which confirms why gamma must not be assumed injective. None of these tests requires adding a hypothesis.

Against delivery-errors B–E: all nodes used already exist and their statements were opened; each non-elementary invocation in step 2 is precisely a cited statement with its hypotheses checked; the other steps give the finite coefficient arguments rather than invoke unnamed facts. No new nodes, circular dependencies, clause relabelling, tag-only citations, source change, hollow definitions or new Lean occur. The longest step is below 2000 characters; no long-step extraction is needed. Every citation excerpt was tested verbatim against its actual node statement, and proof_deps equals the union of uses. The original statement, source, created record, blueprint.is/from/via and any imported metadata are retained. No repository, launcher, Lean or compiler writes were performed.

## Unfinished work

No mathematical work remains for this stage-1 item. Acceptance still requires the server dry run and direct delivery; their outcomes will be recorded below.
