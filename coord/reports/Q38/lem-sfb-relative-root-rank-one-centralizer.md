# Stage-1 delivery: lem-sfb-relative-root-rank-one-centralizer

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-relative-root-rank-one-centralizer.json`: existing statement, now split into seven steps. Statement and statement dependencies retained exactly. Mathlib verdict: no matching relative group-scheme theorem.
- `citations.json`: fifteen verbatim statement quotations, one for every step/node pair.
- `report.md`: this report. No new nodes or Mathlib leaves.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint id, relative-root and rank-one-centralizer terms, and group-scheme centralizers. The matrix-centralizer equations and field-valued constructions in `AlgebraicGeometry/GroupScheme/GeneralLinear/ClosedSubgroup/LieSubalgebra.lean` do not supply a smooth relative reductive centralizer with arbitrary-base-change and root-line clauses. No project declaration states the item exactly.

## Wanted literature

WANTED: Brian Conrad, *Reductive group schemes*, author PDF https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, locally as `literature/conrad-reductive-group-schemes.pdf`; Lemma 4.1.3 and its proof, printed pp.108-109, with p.107 and Lemma 2.2.4 pp.64-66. I read these places online. The local PDF is absent. The proof is marked agent-written: it follows the published argument but supplies the affine local-basis, weight-support and successive-base-change calculations. No SGA source was used. Conrad's attribution to another source is not used as a proof input.

## Problems found and corrections

No statement dispute. No hypotheses, conclusion or definition were changed. The existing item had no proof. The tempting shortcut through `lem-sfb-relative-tangent-weight-base-change` is invalid for this item because that node assumes a nonzero Noetherian base, whereas the item permits any ring. Instead the proof uses the arbitrary-base theorem `lem-sfb-relative-torus-centralizer-normalizer`. I initially considered treating the tangent module as globally finite projective; the final proof applies the weight theorem on affine opens where the tangent bundle is actually free, and glues its uniquely defined projections. This avoids importing an uncited locally-free/projective equivalence.

An equality of fibre dimensions alone does not identify submodules over a nonreduced ring. Step 4 uses finite-free neighbourhoods to prove vanishing, and step 5 inverts the determinant of the actual tangent inclusion. Thus the proof never claims that a matrix whose reduction vanishes must vanish.

The nearest-blueprint-ancestor command prints `None` for this inherited long provenance chain. The item's existing `blueprint.from.node = null` and complete `via` list are retained. The latest unit `_section.md` and direct-images proof were read at `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`; this remains the existing relative-root structural prerequisite on that route. Whole-blueprint searches for `centralizer` (three matches) and `root` (69 matches) give no matching imported relative statement. The existing arbitrary-base centralizer and weight nodes and the field rank-one node supply every structural input; creating clause nodes would duplicate them.

## Mathlib search evidence

All fresh searches were run through the prescribed `msearch.py Q38 lem-sfb-relative-root-rank-one-centralizer` command and read; their exact queries/results are copied from `searches.jsonl` into the item. The inherited four searches remain unchanged. Fresh Loogle `"centralizer", "Scheme"` and grep `centralizer|Centralizer|reductive` in `AlgebraicGeometry` yielded no hits. LeanSearch returned root-datum definitions, abstract reduced root-pairing criteria, and the Killing-form Lie-algebra root-system instance. Two LeanFinder phrasings returned Cartan, coroot and Geck-construction declarations, including `LieAlgebra.rootSpace_zero_eq` and `LieAlgebra.IsKilling.sl2SubmoduleOfRoot_eq_sup`. I read the candidate source at `Mathlib/Algebra/Lie/Weights/Cartan.lean:257`, `Killing.lean:698` and `RootSystem.lean:387`: these use Lie-algebra weights/Cartan or characteristic-zero Killing hypotheses and give no relative algebraic-group construction. They cannot be one-line specializations to the item in arbitrary characteristic. No service failure is recorded as absence.

## Not duplicates

No new nodes. Reused `lem-sfb-relative-torus-centralizer-normalizer`, `lem-sfb-relative-torus-bundle-weights`, `lem-sfb-reductive-rank-one-reflections`, and `lem-weil-pbc-finite-projective-prime-local-free`. The field rank-one theorem is not an attachment of this arbitrary-ring theorem. The relative centralizer theorem does not itself give reductivity or the two-root description, and the weight theorem does not identify which weights occur; the item's argument combines their statements.

## Review by Q38

I read Conrad's Lemma 4.1.3 and proof (printed pp.108-109), the preceding weight-bundle discussion (p.107), and the centralizer/tangent theorem Lemma 2.2.4 (pp.64-66) online. I read Milne's Propositions 21.1-21.2 and Theorem 21.11(a)-(b), printed pp.424-425 and 428-429, in the local PDF. These are exactly the field structure inputs: maximal torus, full torus characters rather than their differentials, one-dimensional root spaces and no rationally proportional roots beyond the opposite pair. I read Stacks `algebra.tex`, label `lemma-finite-projective`, tag 00NX (tag-table entry checked), including finite-projective local freeness. There are no new-node sources to audit.

For step 1 I opened the entire statements of the relative centralizer and bundle-weight nodes. Applying the centralizer theorem to the trivial torus is allowed by its explicit rank-zero clause, so its statement supplies the tangent bundle and arbitrary base change for G itself. Weight decomposition is applied only after restricting to an affine free neighbourhood, satisfying the weight theorem's finite-projective hypothesis. Unique Laurent coefficients glue; a finite affine subcover controls the global finite support. The first-order multiplication formula verifies that the module used is the item's module, rather than an unspecified tangent convention.

For step 2 I checked the full universal centralizer functor in the cited node, not just its closedness clause. The integral Euclidean-coordinate calculation shows that the specified primitive-root kernel really is a split closed torus, including when the root itself is divisible by a residue characteristic. The theorem's hypotheses are satisfied by the given smooth affine finitely presented G, with no Noetherian assumption. It gives the requested H and the inclusion of its Lie algebra as invariant vectors.

For step 3 I reread the field rank-one node's full statement. It explicitly gives the zero-weight space, the reduced proportional-root property, dimensions of root spaces, and reductivity of the root-kernel centralizer. At each geometric point the item's rank-one hypothesis and the weight-base-change comparison make alpha a nonzero root, so every hypothesis is satisfied. The general relative centralizer comparison identifies this field centralizer with the actual geometric fibre of H. T is contained in H because T is commutative; its geometric maximality is inherited from G. Thus the two nodes say every fact taken from them; no proof-only construction is used.

For step 4 I checked that the local-freeness node holds over any commutative ring and that the weight node supplies projectivity on the chosen free neighbourhoods. Free ranks are detected after extending a residue field to its algebraic closure. Vanishing is justified on those neighbourhoods and then by the explicit annihilator/localization argument, so nilpotents and nonflat base changes do not introduce an unproved step. The same argument gives a locally free opposite line, without choosing its global basis.

For step 5 the relative node supplies the actual tangent map and its fibre comparison, the field node supplies the zero-weight identification, and the two module nodes supply local bases. The determinant becomes a unit near each prime. Its adjugate supplies the inverse there, proving equality of the actual submodules rather than abstract equal ranks. This is a few-line matrix argument, so it is kept as a step, not a new lemma.

For step 6 I checked that the weight node explicitly states the restriction-invariants formula for a subgroup L with free quotient; step 2 verifies precisely that hypothesis. It yields the displayed Lie decomposition after the vanishings and zero-weight identification proved in steps 4-5. Centrality follows by reversing the same commutation equality in the defining functor, on every test extension. This is elementary functor manipulation, not a hidden reductivity theorem.

For step 7 the two relative nodes explicitly state arbitrary-base-change comparisons for the centralizer, tangent inclusion, weight and invariant summands. The proof identifies the successive centralizer maps on all test points and the successive tangent maps by the formula b' tensor (b tensor D) maps to the coefficient b'h(b)D(c). Restricting to weight summands gives all the promised compatibilities, including nonflat extensions. All seven steps are shorter than 2000 characters, and I checked that none conceals another standalone structural lemma.

Small cases checked: r=1 makes the kernel torus trivial and H=G; SL2 over characteristic 2 has root alpha=2 times a primitive character, so the torus kernel is trivial while ker(alpha) may be nonreduced, and the proof correctly uses the primitive kernel and full characters. For G a torus there is no nonzero root over a nonempty base, so the hypotheses cannot occur. For GL2 over dual numbers the determinant and split coefficient projections remain valid. A nontrivial invertible root module (Conrad's GL(A direct-sum J) example) is preserved because every basis choice is local. Disconnected bases are allowed; the rank-one alpha hypothesis is used on every component. Over A=0 the geometric assertions are vacuous and all modules vanish. For r=0 no nonzero alpha exists. No new false or redundant node was introduced.

## Unfinished work

None in this one-level stage-1 split. Existing dependencies remain independently owned and are reused by statement only. No Lean file was written and no compiler, Lake or build command was run. Required server dry run and direct delivery follow this review.
