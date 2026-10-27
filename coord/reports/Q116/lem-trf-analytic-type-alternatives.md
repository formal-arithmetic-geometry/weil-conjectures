# Q116 — lem-trf-analytic-type-alternatives

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-analytic-type-alternatives.json`: item, statement; ten explicit proof steps, status split. All mathematical hypotheses and conclusions retained. Literal doubled TeX escapes in its statement were normalized to single TeX commands.
- `dag/nodes/sec-trace-formula/lem-trf-valued-extension-degree-bound.json`: new statement-only prerequisite, unsplit; no Mathlib match. It asserts the fundamental inequality for arbitrary real-valued valuations, without completeness, discreteness, separability or finiteness of the integer ring over the base integer ring.
- `citations.json`: the exact statement quoted for each citation in steps 7, 8 and 9.
- `searches.jsonl`: searches logged by the required msearch command. The item's previous searches are retained; all additional recorded searches were actually run. Searches about Gauss norms were exploratory and led to no node.

One new node; zero Mathlib leaves. No Lean was written, no compiler or Lake tool was run, and no repository or launcher file was changed.

## Attachments

None. Searches in the live read-only `lean/WeilConjectures/` for the item id, analytic fields, residue transcendence and value transcendence found no declaration stating the item. The commutative algebra hits concern scheme/local-ring dimension and do not state this analytic classification. The new degree bound also has no matching project declaration.

## Wanted literature

WANTED: Michael Temkin, Stable Modification of Relative Curves, arXiv:0707.3953v3, local archival copy `literature/temkin-stable-modification-arXiv-0707.3953v3.pdf`; Section 2.1 printed pp. 7–8 for lem-trf-valued-extension-degree-bound, Section 6.2 printed pp. 41–42 and the beginning of the proof of Theorem 6.3.1 printed p. 49 for lem-trf-analytic-type-alternatives. The primary PDF at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf was read online. The named local PDF does not exist in this read clone. No document was downloaded or written to the repository.

I read the source's definition of analytic fields, its finite-extension fundamental inequality, the opening classification in Section 6.2, Remark 6.2.2, and the coordinate choice at the beginning of the proof of Theorem 6.3.1. The source's general classification uses the invariance of rational rank and residue transcendence degree under finite extensions and completion. Here the explicit rational-field computation additionally proves the finite-generation and cyclicity clauses needed by this item. The supplementary details are marked agent-written. I also read Stacks algebra.tex Tag 030Z (lemma-perfect), Tag 030O's separability convention, and the statement of the existing algebraically closed separating-basis node.

## Corrections and route

There is no mathematical statement dispute. The inherited statement was mathematically correct, but its TeX commands were literally doubled, contrary to B4; these are normalized. The imported source's local path is unavailable, so the proof is marked agent-written and the archival copy is requested above. The chapter and unit are unchanged; this item is not their statement node and does not change their realization records. The latest blueprint, commit ef6f9619fdbffa59e88528fb56483d76c70258c8, and the existing ancestor lem-trf-local-term-locality were read. The historical semistable-modification/analytic-uniformization route remains the same. No SGA source was used.

The field-theory separating-basis theorem is a declared off-unit generic tool in split_report.tool_uses; it supplies no geometric route change. The finite-extension bound is not the stability/defectlessness theorem: the inequality is sufficient, and equality is deliberately not assumed. The item does not cite its parent analytic-uniformization node or the sibling stability node, so there is no circular use of uniformization.

## Not duplicates

lem-trf-valued-extension-degree-bound vs lem-trf-almost-finite-residue-field-degree: that node assumes a Noetherian base domain and an integral subring of a finite extension and concludes only residue-degree finiteness; our integer rings need not be Noetherian, and our node also bounds value-group index and the product ef.

lem-trf-valued-extension-degree-bound vs lem-trf-analytic-etale-residue-degree: that node is the etaleness criterion involving separable residue degree and equality with the field degree; our node is the unconditional ef inequality and assumes neither etaleness nor separability.

lem-trf-valued-extension-degree-bound vs lem-trf-analytic-type23-stability: stability assumes a one-dimensional analytic extension over an algebraically closed base of type 2 or 3, and asserts equality for its finite extensions; our lemma applies to arbitrary real-valued valued fields and asserts only the fundamental inequality. Stability would be both stronger than needed and inappropriate for the immediate case.

lem-trf-valued-extension-degree-bound vs lem-sbc-dvr-galois-normalization-ramification-dvd: that node assumes DVRs and a finite Galois normalization and gives divisibility; our valuation can be nondiscrete and the extension inseparable or defective.

lem-trf-valued-extension-degree-bound vs lem-trf-valued-decompletion-etale: that node concerns completion and etaleness and does not bound the value-group index or the residue-degree/index product.

No new Stacks-tagged node was created; consequently there are no additional same-Stacks-tag pairs. Whole-DAG statement/title/source searches and blueprint_refs searches for fundamental inequality, valuation, value group, residue degree, Gauss and separating basis found no duplicate of the new node. The existing separating-basis theorem is reused. The rational-valuation-linear-residue node constructs an affine coordinate under residual transcendence, rather than proving the finite-extension bound. Gauss-norm and Tate-algebra nodes do not supply this bound either.

## Mathlib search assessment

For the new node I ran leanfinder with the finite-extension ef inequality, Loogle `Valuation, Module.finrank`, a full Mathlib grep for fundamental inequality and ramification/inertia products, LeanSearch with the same mathematical question, a second leanfinder phrasing about residue lifts and distinct value cosets, and a targeted valuation grep for residue/linear-independence/value-group-index combinations. All services returned results. I read the candidates' types and the relevant source contexts in NumberTheory/RamificationInertia/Basic.lean: the inertia-degree bounds and ef identities assume Dedekind domains and finite integer-ring modules; these do not specialize to the nondiscrete rings here. Valuation.pow_coeff_zero_ne_zero_of_unit is a minimal-polynomial nonvanishing assertion, not the fundamental inequality. The other linear-independence hits concern root systems and profinite products. Hence no exact or one-line Mathlib specialization was found.

For the item, both prior searches and the newly logged complete-extension/classification and Berkovich-type phrasings yielded local fields, function fields, completions, and unrelated analytic declarations, with no classification of these general extensions. Gauss-norm searches found Polynomial.gaussNorm and its multiplicativity theorem, but neither is used as a hidden external fact in the final proof: polynomial norms in the two attained-distance cases are established directly by reduction or unique largest terms. No node or Mathlib leaf was created for these elementary computations.

## Review by Q116

I checked B–E against the actual files, not only the imported dependency lists. I read the primary Temkin PDF at each of the places above, and opened the full statements of every cited node. The new node introduces F, H, both absolute values, valuation rings, maximal ideals, residue fields, value groups, coset index and vector-space degree; it has no proof sketch in its statement, proof, or proof_deps. Its prospective proof is the familiar residue-lift/value-coset linear-independence argument: choose representatives x_i with distinct value cosets and units y_j with residue classes independent over the base residue field. For each nonzero coefficient row, divide by a coefficient of maximal norm to show that its y_j sum has that maximal norm; multiplication by x_i makes the nonzero row sums have different values, so they cannot cancel. Any finite grid is independent, hence its size is at most [H:F]. This bounds both numbers of independent choices and then their product. This is a genuine supporting valuation theorem, not a clause of the analytic classification or an elementary duplicate.

Step 1 uses only polynomial root existence from the assumed algebraic closedness and the stated norm axioms. The lifted polynomial is monic; that hypothesis is exactly what forces a root to be integral. Root extraction proves divisibility for every positive integer, including the residue characteristic. No separability or Hensel assertion is smuggled in.

Step 2 uses E != k, k algebraically closed and E finite over the closure of k(y), so y cannot lie in k or be algebraic over it. The dense-field computation explicitly chooses a relative as well as absolute error bound; it proves equality of value groups and surjectivity on residues without claiming that completion preserves arbitrary algebraic degrees.

Steps 3–4 treat an attained distance r in Gamma_k. The chosen b is nonzero, and t has norm one. A hypothetical algebraic residue would be a ground-field residue because step 1 proves the latter field algebraically closed, and lifting it would contradict minimality. Dividing by maximal coefficients then proves the polynomial norm and the rational residue-field identification directly, including residue-zero elements.

Step 5 treats an attained distance outside Gamma_k. I verified that divisibility in the positive real numbers excludes every nonzero integral power of r from Gamma_k; this is necessary to exclude equal monomial norms and to force equal exponents in a rational function of norm one. The displayed largest-term calculation proves both the residue equality and the cyclic group formula.

Step 6 treats a distance with no minimum. For each particular rational function only finitely many roots and poles occur. Failure of a minimum supplies a closer a than all of them, so f(a) is defined and nonzero. I wrote the factor comparison explicitly, including negative powers, rather than assuming an unjustified global closest-point theorem. This proves immediacy without assuming spherical completeness.

Step 7 cites the new degree bound, whose statement explicitly gives both finite indices for every finite valued extension, with no discrete or separability hypotheses. It applies to E/L with the inherited real absolute value and the given finite dimension. Divisibility plus uniqueness of positive roots kills finite extensions of Gamma_k. Algebraic closedness kills finite residue extensions of the ground residue field, but does not kill finite extensions of its rational function field; the latter remain finitely generated of transcendence degree one, as required.

Step 8 cites exactly the same statement for E/L in the value-transcendental branch. I checked that a finite-index supergroup of Gamma_k r^Z need not be generated by r itself. The proof therefore constructs a new generator s using N=e! and the least positive element of an explicit subgroup of Z. Euclidean division proves cyclicity, and positive-root uniqueness proves s is outside Gamma_k. It does not incorrectly infer that an arbitrary rational-rank-one group is cyclic.

Step 9 cites lem-weil-pbc-algclosed-fg-field-separating-basis. Its statement gives an algebraically independent separating transcendence basis under exactly the algebraic-closedness and finite-generation assumptions already proved. The trdeg-one hypothesis forces a singleton, and the explicit finite monomial spanning argument upgrades algebraicity to finiteness. The Stacks perfect-field source and separability convention were read. Step 10 uses only the distinct residue degrees and the strict value-group distinction to prove exclusivity.

I tested the new bound on H=F (e=f=n=1), trivially valued finite field extensions (e=1, f=n), an inseparable finite extension, and a defective immediate finite extension (e=f=1 <= n). The inequality remains correct in each case. For the item I tested the unit-radius Gauss rational completion (type 2), an irrational-radius completion (type 3), and a nonattained-distance immediate extension (type 4, when such an extension exists). Finite covers may enlarge the value generator by a root; step 8 allows this. E=k is correctly excluded, and a spherically complete ground field simply has no nonattained-distance branch. No false claim about the existence of every type for every base is made.

All non-elementary steps are shorter than 2000 characters and cite the precise statements used. The longer-looking rational computations are broken at their logical boundaries, not hidden under “standard”, “transport” or a document citation. citations.json quotes the full verbatim statements used in steps 7–9. All proof_deps equal the union of the uses lists. New-node searches were logged before writing the node; new nodes were written before the item.

## Unfinished work

None at stage 1. The new supporting valuation statement remains unsplit as required for a one-level split. The missing archival PDF is requested above and is not misrepresented as a local source read.
