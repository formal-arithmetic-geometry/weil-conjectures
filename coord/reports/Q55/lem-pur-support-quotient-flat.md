1. Files written

- `dag/nodes/sec-smooth-purity/lem-pur-support-quotient-flat.json` — statement node, split into four proof steps; no new nodes and therefore no Mathlib leaves.
- `citations.json` — verbatim statement quotations for every node used by every step.

2. Attachments

None.

3. WANTED

None. The split uses the existing DAG statements and the blueprint source paragraph.

4. What was wrong in the imported material

The imported statement quantified over an arbitrary closed immersion but gave no quasi-compactness hypothesis on the complementary pro-etale open. The existing pro-etale open-closed exactness lemma and the existing open-closed flatness lemma both explicitly require that open to be quasi-compact. I corrected the statement by adding this hypothesis and added `def-weil-finite-type-morphism` to `stmt_deps`; the correction is recorded in `split_report.statement_change`. The blueprint support-quotient paragraph is otherwise realized directly. No new lemma node was needed: the cokernel identification, flatness/K-flatness, stalk calculation, and comparison all use existing DAG statements.

5. What I could not finish

Nothing.

## Review by Q55

I read the item source paragraph in `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/lem-pur-kunneth-supported.proof.md`, the item’s imported dependency list, and the statements of every cited node. Step 1 uses the etale open-closed short exact sequence and the pro-etale ringed open-closed sequence; those statements supply the two exact sequences and the latter explicitly supplies the quasi-compact-open hypothesis now present in the item. The constant-sheaf and extension-by-zero definitions identify their first terms with the maps in the two cokernels. Step 2 uses the open-closed flatness criterion’s explicit conclusion that `i_*M` is flat when `M` is flat, with the rank-one constant sheaf on `C`, and the bounded-above-flat K-flat criterion for the degree-zero complex; I checked the flatness and K-flat definitions cited there. Step 3 uses finiteness of a closed immersion, the finite-morphism geometric-stalk product formula, the constant-sheaf geometric-stalk isomorphism, and the lower-star stalk identification; their statements give exactly the fibre and stalk calculations used, including the empty fibre off `C` and the singleton fibre on `C`, while Step 1 tracks the quotient generator to `1`. Step 4 uses the free-Yoneda universal generator statement, the comparison morphism definition, and exactness of `nu_T^*`; these statements justify that the two extension-by-zero maps and their generators correspond, so exactness identifies their cokernels and quotient maps. I checked every `uses` entry against its node statement and wrote the corresponding verbatim quotes in `citations.json`. I also ran the required LeanFinder, Loogle, grep, and LeanSearch searches for the item; they returned only generic Mathlib declarations and are recorded in `mathlib_searches`.
